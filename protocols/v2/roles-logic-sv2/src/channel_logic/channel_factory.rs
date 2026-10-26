//! # Channel Factory
//!
//! This module contains logic for creating and managing channels.

use super::extended_to_standard_job;
use crate::{
    common_properties::StandardChannel,
    job_creator::{self, JobsCreators},
    parsers::Mining,
    utils::{GroupId, Id, Mutex},
    Error,
};

use mining_sv2::{
    ExtendedExtranonce, NewExtendedMiningJob, NewMiningJob, OpenExtendedMiningChannelSuccess,
    OpenMiningChannelError, OpenStandardMiningChannelSuccess, SetCustomMiningJob,
    SetCustomMiningJobError, SetCustomMiningJobSuccess, SetExtranoncePrefix, SetNewPrevHash,
    SubmitSharesError, SubmitSharesExtended, SubmitSharesStandard, Target,
};

use hex::DisplayHex;
use nohash_hasher::BuildNoHashHasher;
use std::{
    collections::{HashMap, HashSet},
    convert::TryInto,
    sync::Arc,
};
use template_distribution_sv2::{NewTemplate, SetNewPrevHash as SetNewPrevHashFromTp};

use tracing::{debug, error, info, trace, warn};

use stratum_common::bitcoin::{
    block::{Header, Version},
    consensus::{deserialize_partial, serialize},
    hash_types,
    hashes::sha256d::Hash,
    Amount, CompactTarget, ScriptBuf, TxOut,
};
use stratum_common::secp256k1::rand::{rngs::OsRng, RngCore};

/// Stable output for one pool extended channel. The zero-valued OP_RETURN pushes `CHSEQ`
/// followed by a fixed 16-byte random factory prefix and an 8-byte big-endian channel counter.
/// The counter starts at 1; the prefix is shared by all channels for the factory's lifetime.
/// This tagged format is reserved for the factory; other outputs are preserved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChannelCoinbaseOutput([u8; 24]);

impl ChannelCoinbaseOutput {
    /// Returns this channel marker as a zero-valued coinbase output.
    pub fn tx_out(self) -> TxOut {
        let mut payload = [0; 29];
        payload[..5].copy_from_slice(b"CHSEQ");
        payload[5..].copy_from_slice(&self.0);
        TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::new_op_return(payload),
        }
    }

    /// Conservative extra coinbase weight: the output plus two bytes for CompactSize output
    /// count growth. Larger count boundaries cannot fit in an SV2 coinbase suffix.
    pub fn additional_coinbase_weight() -> usize {
        (serialize(&Self([0; 24]).tx_out()).len() + 2) * 4
    }

    /// Materializes a pool-created job, including shared jobs returned by extended fanout.
    /// Call before adding local outputs and registering the per-job output.
    /// Repeated application replaces an existing CHSEQ output in place and removes duplicates.
    /// Other outputs, the input sequence, extranonce split, witness and locktime remain intact.
    pub fn apply(self, job: &mut NewExtendedMiningJob<'static>) -> Result<(), Error> {
        let suffix = job.coinbase_tx_suffix.as_ref();
        // Pool-created suffixes begin with the input sequence, then the output vector.
        let encoded_outputs = suffix.get(4..).ok_or(Error::InvalidCoinbase)?;
        let (mut outputs, consumed): (Vec<TxOut>, usize) =
            deserialize_partial(encoded_outputs).map_err(|_| Error::InvalidCoinbase)?;
        let mut has_channel_output = false;
        outputs.retain_mut(|output| {
            if output.value == Amount::ZERO
                && output.script_pubkey.len() == 31
                && output
                    .script_pubkey
                    .as_bytes()
                    .starts_with(b"\x6a\x1dCHSEQ")
            {
                if has_channel_output {
                    false
                } else {
                    *output = self.tx_out();
                    has_channel_output = true;
                    true
                }
            } else {
                true
            }
        });
        if !has_channel_output {
            outputs.push(self.tx_out());
        }
        let new_suffix = [
            &suffix[..4],
            serialize(&outputs).as_slice(),
            &encoded_outputs[consumed..],
        ]
        .concat();
        job.coinbase_tx_suffix = new_suffix.try_into()?;
        Ok(())
    }
}

/// A stripped type of `SetCustomMiningJob` without the (`channel_id, `request_id` and `token`)
/// fields
#[derive(Debug)]
pub struct PartialSetCustomMiningJob {
    pub version: u32,
    pub prev_hash: binary_sv2::U256<'static>,
    pub min_ntime: u32,
    pub nbits: u32,
    pub coinbase_tx_version: u32,
    pub coinbase_prefix: binary_sv2::B0255<'static>,
    pub coinbase_tx_input_n_sequence: u32,
    pub coinbase_tx_value_remaining: u64,
    pub coinbase_tx_outputs: binary_sv2::B064K<'static>,
    pub coinbase_tx_locktime: u32,
    pub merkle_path: binary_sv2::Seq0255<'static, binary_sv2::U256<'static>>,
    pub extranonce_size: u16,
    pub future_job: bool,
}

/// Represents the action that needs to be done when a new share is received.
#[derive(Debug, Clone)]
pub enum OnNewShare {
    /// Used when the received is malformed, is for an inexistent channel or do not meet downstream
    /// target.
    SendErrorDownstream(SubmitSharesError<'static>),
    /// Used when an extended channel in a proxy receive a share, and the share meet upstream
    /// target, in this case a new share must be sent upstream. Also an optional template id is
    /// returned, when a job declarator want to send a valid share upstream could use the
    /// template for get the up job id.
    SendSubmitShareUpstream((Share, Option<u64>)),
    /// Used when a group channel in a proxy receive a share that is not malformed and is for a
    /// valid channel in that case we relay the same exact share upstream with a new request id.
    RelaySubmitShareUpstream,
    /// Indicate that the share meet bitcoin target, when there is an upstream the we should send
    /// the share upstream, whenever possible we should also notify the TP about it.
    /// When a pool negotiate a job with downstream we do not have the template_id so we set it to
    /// None
    /// (share, template id, coinbase,complete extranonce)
    ShareMeetBitcoinTarget((Share, Option<u64>, Vec<u8>, Vec<u8>)),
    /// Indicate that the share meet downstream target, in the case we could send a success
    /// response downstream.
    ShareMeetDownstreamTarget,
}

impl OnNewShare {
    /// Converts standard share into extended share
    pub fn into_extended(&mut self, extranonce: Vec<u8>, up_id: u32) {
        match self {
            OnNewShare::SendErrorDownstream(_) => (),
            OnNewShare::SendSubmitShareUpstream((share, template_id)) => match share {
                Share::Extended(_) => (),
                Share::Standard((share, _)) => {
                    let share = SubmitSharesExtended {
                        channel_id: up_id,
                        sequence_number: share.sequence_number,
                        job_id: share.job_id,
                        nonce: share.nonce,
                        ntime: share.ntime,
                        version: share.version,
                        extranonce: extranonce.try_into().unwrap(),
                    };
                    *self = Self::SendSubmitShareUpstream((Share::Extended(share), *template_id));
                }
            },
            OnNewShare::RelaySubmitShareUpstream => (),
            OnNewShare::ShareMeetBitcoinTarget((share, t_id, coinbase, ext)) => match share {
                Share::Extended(_) => (),
                Share::Standard((share, _)) => {
                    let share = SubmitSharesExtended {
                        channel_id: up_id,
                        sequence_number: share.sequence_number,
                        job_id: share.job_id,
                        nonce: share.nonce,
                        ntime: share.ntime,
                        version: share.version,
                        extranonce: extranonce.try_into().unwrap(),
                    };
                    *self = Self::ShareMeetBitcoinTarget((
                        Share::Extended(share),
                        *t_id,
                        coinbase.clone(),
                        ext.to_vec(),
                    ));
                }
            },
            OnNewShare::ShareMeetDownstreamTarget => todo!(),
        }
    }
}

/// A share can be either extended or standard
#[derive(Clone, Debug)]
pub enum Share {
    Extended(SubmitSharesExtended<'static>),
    // share, group id
    Standard((SubmitSharesStandard, u32)),
}

/// Helper type used before a `SetNewPrevHash` has a channel_id
#[derive(Clone, Debug)]
pub struct StagedPhash {
    job_id: u32,
    prev_hash: binary_sv2::U256<'static>,
    min_ntime: u32,
    nbits: u32,
}

impl StagedPhash {
    /// Converts a Staged PrevHash into a SetNewPrevHash message
    pub fn into_set_p_hash(
        &self,
        channel_id: u32,
        new_job_id: Option<u32>,
    ) -> SetNewPrevHash<'static> {
        SetNewPrevHash {
            channel_id,
            job_id: new_job_id.unwrap_or(self.job_id),
            prev_hash: self.prev_hash.clone(),
            min_ntime: self.min_ntime,
            nbits: self.nbits,
        }
    }
}

impl Share {
    /// Get share sequence number
    pub fn get_sequence_number(&self) -> u32 {
        match self {
            Share::Extended(s) => s.sequence_number,
            Share::Standard(s) => s.0.sequence_number,
        }
    }

    /// Get share channel id
    pub fn get_channel_id(&self) -> u32 {
        match self {
            Share::Extended(s) => s.channel_id,
            Share::Standard(s) => s.0.channel_id,
        }
    }

    /// Get share timestamp
    pub fn get_n_time(&self) -> u32 {
        match self {
            Share::Extended(s) => s.ntime,
            Share::Standard(s) => s.0.ntime,
        }
    }

    /// Get share nonce
    pub fn get_nonce(&self) -> u32 {
        match self {
            Share::Extended(s) => s.nonce,
            Share::Standard(s) => s.0.nonce,
        }
    }

    /// Get share job id
    pub fn get_job_id(&self) -> u32 {
        match self {
            Share::Extended(s) => s.job_id,
            Share::Standard(s) => s.0.job_id,
        }
    }

    /// Get share version
    pub fn get_version(&self) -> u32 {
        match self {
            Share::Extended(s) => s.version,
            Share::Standard(s) => s.0.version,
        }
    }
}

#[derive(Debug)]
/// Basic logic shared between all the channel factories
struct ChannelFactory {
    ids: Arc<Mutex<GroupId>>,
    standard_channels_for_non_hom_downstreams:
        HashMap<u64, StandardChannel, BuildNoHashHasher<u64>>,
    standard_channels_for_hom_downstreams: HashMap<u32, StandardChannel, BuildNoHashHasher<u32>>,
    extended_channels:
        HashMap<u32, OpenExtendedMiningChannelSuccess<'static>, BuildNoHashHasher<u32>>,
    extranonces: ExtendedExtranonce,
    share_per_min: f32,
    // (NewExtendedMiningJob,group ids that already received the future job)
    future_jobs: Vec<(NewExtendedMiningJob<'static>, Vec<u32>)>,
    // (SetNewPrevHash,group ids that already received the set prev_hash)
    last_prev_hash: Option<(StagedPhash, Vec<u32>)>,
    last_prev_hash_: Option<hash_types::BlockHash>,
    // (NewExtendedMiningJob,group ids that already received the job)
    last_valid_jobs: [Option<(NewExtendedMiningJob<'static>, Vec<u32>)>; 3],
    // Index of the last valid job for channel_id ++ job_id
    id_to_job: HashMap<u32, u8, BuildNoHashHasher<u64>>,
    extended_job_coinbase_outputs: HashMap<(u32, u32), TxOut>,
    // Used to understand which is the last added element in last_valid_jobs
    added_elements: usize,
    kind: ExtendedChannelKind,
    job_ids: Id,
    // Channel IDs map to their group; reserved group IDs map to themselves.
    // All extended and header-only channels use the shared, reserved group 0
    // for reasons that are currently unknown. Closing it would affect channels
    // from multiple downstream connections.
    channel_to_group_id: HashMap<u32, u32, BuildNoHashHasher<u32>>,
    future_templates: HashMap<u32, NewTemplate<'static>, BuildNoHashHasher<u32>>,
}

impl ChannelFactory {
    fn close_channel(&mut self, channel_id: u32) {
        // Group IDs mark reservations rather than individual mining channels.
        if self.channel_to_group_id.get(&channel_id) == Some(&channel_id) {
            return;
        }
        self.standard_channels_for_hom_downstreams
            .remove(&channel_id);
        self.extended_channels.remove(&channel_id);
        self.extended_job_coinbase_outputs
            .retain(|(variant_channel_id, _), _| *variant_channel_id != channel_id);
        if let Some(group_id) = self.channel_to_group_id.remove(&channel_id) {
            self.standard_channels_for_non_hom_downstreams
                .remove(&GroupId::into_complete_id(group_id, channel_id));
            if group_id != 0
                && !self
                    .standard_channels_for_non_hom_downstreams
                    .values()
                    .any(|channel| channel.group_id == group_id)
            {
                self.remove_group(group_id);
            }
        }
    }

    fn remove_group(&mut self, group_id: u32) {
        self.channel_to_group_id.remove(&group_id);
        for (_, sent_groups) in &mut self.future_jobs {
            sent_groups.retain(|id| *id != group_id);
        }
        for (_, sent_groups) in self.last_valid_jobs.iter_mut().flatten() {
            sent_groups.retain(|id| *id != group_id);
        }
        if let Some((_, sent_groups)) = &mut self.last_prev_hash {
            sent_groups.retain(|id| *id != group_id);
        }
    }
}

impl ChannelFactory {
    fn add_valid_job(&mut self, job: NewExtendedMiningJob<'static>, group_ids: Vec<u32>) {
        match self.last_valid_jobs {
            [None, None, None] => {
                self.id_to_job.insert(job.job_id, 0);
                self.last_valid_jobs[0] = Some((job, group_ids));
                self.added_elements = 1;
            }
            [Some(_), None, None] => {
                self.id_to_job.insert(job.job_id, 1);
                self.last_valid_jobs[1] = Some((job, group_ids));
                self.added_elements = 2;
            }
            [Some(_), Some(_), None] => {
                self.id_to_job.insert(job.job_id, 2);
                self.last_valid_jobs[2] = Some((job, group_ids));
                self.added_elements = 3;
            }
            [Some(_), Some(_), Some(_)] => {
                let to_remove = self.added_elements % 3;
                let evicted_job_id = self.last_valid_jobs[to_remove].as_ref().unwrap().0.job_id;
                self.extended_job_coinbase_outputs
                    .retain(|(_, job_id), _| *job_id != evicted_job_id);
                self.id_to_job.retain(|_, v| *v != to_remove as u8);
                self.id_to_job.insert(job.job_id, to_remove as u8);
                self.last_valid_jobs[to_remove] = Some((job, group_ids));
                self.added_elements += 1;
            }
            _ => panic!("Internal error: invalid last_valid_jobs state"),
        }
    }
    fn get_valid_job(&self, job_id: u32) -> Option<&(NewExtendedMiningJob<'static>, Vec<u32>)> {
        let index = self.id_to_job.get(&job_id)?;
        self.last_valid_jobs[*index as usize].as_ref()
    }
    fn get_last_valid_job(&self) -> Option<&(NewExtendedMiningJob<'static>, Vec<u32>)> {
        let index = self.get_last_valid_job_index()?;
        self.last_valid_jobs[index as usize].as_ref()
    }
    fn get_mut_last_valid_job(&mut self) -> Option<&mut (NewExtendedMiningJob<'static>, Vec<u32>)> {
        let index = self.get_last_valid_job_index()?;
        self.last_valid_jobs[index as usize].as_mut()
    }
    fn get_last_valid_job_index(&self) -> Option<u8> {
        match self.last_valid_jobs {
            [None, None, None] => None,
            [Some(_), None, None] => Some(0),
            [Some(_), Some(_), None] => Some(1),
            [Some(_), Some(_), Some(_)] => Some(2),
            _ => panic!("Internal error: invalid last_valid_jobs state"),
        }
    }
    fn clear_valid_jobs(&mut self) {
        self.last_valid_jobs = [None, None, None];
        self.id_to_job.clear();
        self.added_elements = 0;
    }
}

impl ChannelFactory {
    pub fn add_standard_channel(
        &mut self,
        request_id: u32,
        downstream_hash_rate: f32,
        is_header_only: bool,
        id: u32,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<Vec<Mining>, Error> {
        match is_header_only {
            true => self.new_standard_channel_for_hom_downstream(
                request_id,
                downstream_hash_rate,
                id,
                additional_coinbase_script_data,
            ),
            false => self.new_standard_channel_for_non_hom_downstream(
                request_id,
                downstream_hash_rate,
                id,
                additional_coinbase_script_data,
            ),
        }
    }

    /// Called when a `OpenExtendedMiningChannel` message is received.
    /// Here we save the downstream's target (based on hashrate) and the
    /// channel's extranonce details before returning the relevant SV2 mining messages
    /// to be sent downstream. For the mining messages, we will first return an
    /// `OpenExtendedMiningChannelSuccess` if the channel is successfully opened. Then we add
    /// the `NewExtendedMiningJob` and `SetNewPrevHash` messages if the relevant data is
    /// available. If the channel opening fails, we return `OpenExtendedMiningChannelError`.
    pub fn new_extended_channel(
        &mut self,
        request_id: u32,
        hash_rate: f32,
        min_extranonce_size: u16,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<(Vec<Mining<'static>>, Option<u32>), Error> {
        let extended_channels_group = 0;
        let max_extranonce_size = self.extranonces.get_range2_len() as u16;
        if min_extranonce_size <= max_extranonce_size {
            // SECURITY is very unlikely to finish the ids btw this unwrap could be used by an
            // attacker that want to disrupt the service maybe we should have a method
            // to reuse ids that are no longer connected?
            let channel_id = self
                .ids
                .safe_lock(|ids| ids.new_channel_id(extended_channels_group))
                .unwrap();
            self.channel_to_group_id.insert(channel_id, 0);
            let target = match crate::utils::hash_rate_to_target(
                hash_rate.into(),
                self.share_per_min.into(),
            ) {
                Ok(target) => target,
                Err(e) => {
                    error!(
                        "Impossible to get target: {:?}. Request id: {:?}",
                        e, request_id
                    );
                    return Err(e);
                }
            };
            let (extranonce, extranonce_with_stripped_data) = loop {
                let extranonce = self
                    .extranonces
                    .next_extended(max_extranonce_size as usize)
                    .ok_or(Error::ExtranonceSpaceEnded)?;
                let extranonce_with_stripped_data = extranonce
                    .into_prefix(self.extranonces.get_prefix_len(), &[])
                    .unwrap();
                if !self.has_extended_channel_extranonce_prefix(
                    extranonce_with_stripped_data.inner_as_ref(),
                ) {
                    break (extranonce, extranonce_with_stripped_data);
                }
            };
            let success_with_stirpped_extranonce_add_data = OpenExtendedMiningChannelSuccess {
                request_id,
                channel_id,
                target: target.clone(),
                extranonce_size: max_extranonce_size,
                extranonce_prefix: extranonce_with_stripped_data,
            };
            self.extended_channels
                .insert(channel_id, success_with_stirpped_extranonce_add_data);
            let extranonce_prefix = extranonce
                .into_prefix(
                    self.extranonces.get_prefix_len(),
                    additional_coinbase_script_data.unwrap_or(&[]),
                )
                .unwrap();
            let success = OpenExtendedMiningChannelSuccess {
                request_id,
                channel_id,
                target,
                extranonce_size: max_extranonce_size,
                extranonce_prefix,
            };
            let mut result = vec![Mining::OpenExtendedMiningChannelSuccess(success)];
            self.prepare_extended_jobs_and_p_hash(&mut result, channel_id);
            Ok((result, Some(channel_id)))
        } else {
            Ok((
                vec![Mining::OpenMiningChannelError(
                    OpenMiningChannelError::unsupported_extranonce_size(request_id),
                )],
                None,
            ))
        }
    }

    fn has_extended_channel_extranonce_prefix(&self, extranonce_prefix: &[u8]) -> bool {
        self.extended_channels
            .values()
            .any(|channel| channel.extranonce_prefix.inner_as_ref() == extranonce_prefix)
    }

    fn prepare_extended_jobs_and_p_hash(&self, result: &mut Vec<Mining<'static>>, channel_id: u32) {
        if let Some((job, _)) = &self.get_last_valid_job() {
            let mut job = job.clone();
            job.channel_id = channel_id;
            job.set_future();
            let j_id = job.job_id;
            result.push(Mining::NewExtendedMiningJob(job));
            if let Some((new_prev_hash, _)) = &self.last_prev_hash {
                let mut new_prev_hash = new_prev_hash.into_set_p_hash(channel_id, None);
                new_prev_hash.job_id = j_id;
                result.push(Mining::SetNewPrevHash(new_prev_hash.clone()))
            };
        } else if let Some((new_prev_hash, _)) = &self.last_prev_hash {
            let new_prev_hash = new_prev_hash.into_set_p_hash(channel_id, None);
            result.push(Mining::SetNewPrevHash(new_prev_hash.clone()))
        };
        for (job, _) in &self.future_jobs {
            let mut job = job.clone();
            job.channel_id = channel_id;
            result.push(Mining::NewExtendedMiningJob(job))
        }
    }

    /// Called when we want to replicate a channel already opened by another actor.
    /// It is used only in the jd client from the template provider module to mock a pool.
    /// Anything else should open channel with the new_extended_channel function
    pub fn replicate_upstream_extended_channel_only_jd(
        &mut self,
        target: binary_sv2::U256<'static>,
        extranonce: mining_sv2::Extranonce,
        channel_id: u32,
        extranonce_size: u16,
    ) -> Option<()> {
        self.replicate_extended_channel(target, extranonce, channel_id, extranonce_size);
        Some(())
    }

    fn replicate_extended_channel(
        &mut self,
        target: binary_sv2::U256<'static>,
        extranonce: mining_sv2::Extranonce,
        channel_id: u32,
        extranonce_size: u16,
    ) {
        self.channel_to_group_id.insert(channel_id, 0);
        let extranonce_prefix = extranonce.into();
        let success = OpenExtendedMiningChannelSuccess {
            request_id: 0,
            channel_id,
            target,
            extranonce_size,
            extranonce_prefix,
        };
        self.extended_channels.insert(channel_id, success);
    }

    /// Called when an `OpenStandardChannel` message is received for a header only mining channel.
    /// Here we save the downstream's target (based on hashrate) and and the
    /// channel's extranonce details before returning the relevant SV2 mining messages
    /// to be sent downstream.
    fn new_standard_channel_for_hom_downstream(
        &mut self,
        request_id: u32,
        downstream_hash_rate: f32,
        id: u32,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<Vec<Mining>, Error> {
        let hom_group_id = 0;
        let mut result = vec![];
        let channel_id = id;
        let target = match crate::utils::hash_rate_to_target(
            downstream_hash_rate.into(),
            self.share_per_min.into(),
        ) {
            Ok(target) => target,
            Err(e) => {
                error!(
                    "Impossible to get target: {:?}. Request id: {:?}",
                    e, request_id
                );
                return Err(e);
            }
        };
        let extranonce = self
            .extranonces
            .next_standard()
            .ok_or(Error::ExtranonceSpaceEnded)?;
        let standard_channel = StandardChannel {
            channel_id,
            group_id: hom_group_id,
            target: target.clone().into(),
            extranonce: extranonce.clone(),
        };
        self.standard_channels_for_hom_downstreams
            .insert(channel_id, standard_channel);

        let extranonce: Vec<u8> = match additional_coinbase_script_data {
            Some(data) => {
                let mut data = data.to_vec();
                data.extend_from_slice(extranonce.as_ref());
                data
            }
            None => extranonce.into(),
        };

        // First message to be sent is OpenStandardMiningChannelSuccess
        result.push(Mining::OpenStandardMiningChannelSuccess(
            OpenStandardMiningChannelSuccess {
                request_id: request_id.into(),
                channel_id,
                target,
                extranonce_prefix: extranonce.try_into().expect("Internal error: On initialization we make sure that extranonce + coinbase script additional data are not > then 32 bytes"),
                group_channel_id: hom_group_id,
            },
        ));
        self.prepare_standard_jobs_and_p_hash(
            &mut result,
            channel_id,
            additional_coinbase_script_data,
        )?;
        self.channel_to_group_id.insert(channel_id, hom_group_id);
        Ok(result)
    }

    /// This function is called when downstream have a group channel
    /// should not all standard channel's be non HOM??
    fn new_standard_channel_for_non_hom_downstream(
        &mut self,
        request_id: u32,
        downstream_hash_rate: f32,
        group_id: u32,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<Vec<Mining>, Error> {
        let mut result = vec![];
        let channel_id = self
            .ids
            .safe_lock(|ids| ids.new_channel_id(group_id))
            .unwrap();
        let complete_id = GroupId::into_complete_id(group_id, channel_id);
        let target = match crate::utils::hash_rate_to_target(
            downstream_hash_rate.into(),
            self.share_per_min.into(),
        ) {
            Ok(target_) => target_,
            Err(e) => {
                info!(
                    "Impossible to get target: {:?}. Request id: {:?}",
                    e, request_id
                );
                return Err(e);
            }
        };
        let extranonce = self
            .extranonces
            .next_standard()
            .ok_or(Error::ExtranonceSpaceEnded)?;
        let standard_channel = StandardChannel {
            channel_id,
            group_id,
            target: target.clone().into(),
            extranonce: extranonce.clone(),
        };
        self.standard_channels_for_non_hom_downstreams
            .insert(complete_id, standard_channel);

        let extranonce: Vec<u8> = match additional_coinbase_script_data {
            Some(data) => {
                let mut data = data.to_vec();
                data.extend_from_slice(extranonce.as_ref());
                data
            }
            None => extranonce.into(),
        };
        // First message to be sent is OpenStandardMiningChannelSuccess
        result.push(Mining::OpenStandardMiningChannelSuccess(
            OpenStandardMiningChannelSuccess {
                request_id: request_id.into(),
                channel_id,
                target,
                extranonce_prefix: extranonce.try_into().expect(""),
                group_channel_id: group_id,
            },
        ));
        self.prepare_jobs_and_p_hash(&mut result, complete_id);
        // A caller may supply a group ID without using PoolChannelFactory::new_group_id().
        // Reserve it as a key: restore collision checks inspect keys, so channel_id ->
        // group_id alone would allow an extended channel to reuse the group ID and
        // collide with grouped-standard jobs during fanout.
        self.channel_to_group_id.insert(group_id, group_id);
        self.channel_to_group_id.insert(channel_id, group_id);
        Ok(result)
    }

    // When a hom downstream opens a channel, we use this function to prepare all the standard jobs
    // (future and not) that we need to be sent downstream
    fn prepare_standard_jobs_and_p_hash(
        &mut self,
        result: &mut Vec<Mining>,
        channel_id: u32,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<(), Error> {
        // Safe cause the function is private and we always add the channel before calling this
        // funtion
        let standard_channel = self
            .standard_channels_for_hom_downstreams
            .get(&channel_id)
            .unwrap();
        // OPTIMIZATION this could be memoized somewhere cause is very likely that we will receive a
        // lot od OpenStandardMiningChannel requests consecutively
        let job_id = self.job_ids.next();
        let future_jobs: Option<Vec<NewMiningJob<'static>>> = self
            .future_jobs
            .iter()
            .map(|j| {
                extended_to_standard_job(
                    &j.0,
                    standard_channel.extranonce.as_ref(),
                    standard_channel.channel_id,
                    Some(job_id),
                    additional_coinbase_script_data,
                )
            })
            .collect();

        let id = self.job_ids.next();
        // OPTIMIZATION the extranonce is cloned so many time but maybe is avoidable?
        let last_valid_job = match self.get_last_valid_job() {
            Some((j, _)) => Some(
                extended_to_standard_job(
                    j,
                    standard_channel.extranonce.as_ref(),
                    standard_channel.channel_id,
                    Some(id),
                    additional_coinbase_script_data,
                )
                .ok_or(Error::ImpossibleToCalculateMerkleRoot)?,
            ),
            None => None,
        };

        // This is the same thing of just check if there is a prev hash add it to result. If there
        // is last_job add it to result and add each future job to result.
        // But using the pattern match is more clear how each option is handled
        match (
            &self.last_prev_hash,
            last_valid_job,
            self.future_jobs.is_empty(),
        ) {
            // If we do not have anything just do nothing
            (None, None, true) => Ok(()),
            // If we have only future jobs we need to send them all after the
            // SetupConnectionSuccess message
            (None, None, false) => {
                // Safe unwrap cause we check that self.future_jobs is not empty
                let mut future_jobs = future_jobs.unwrap();
                while let Some(job) = future_jobs.pop() {
                    result.push(Mining::NewMiningJob(job));
                }
                Ok(())
            }
            // If we have just a prev hash we need to send it after the SetupConnectionSuccess
            // message
            (Some((prev_h, _)), None, true) => {
                let prev_h = prev_h.into_set_p_hash(channel_id, None);
                result.push(Mining::SetNewPrevHash(prev_h.clone()));
                Ok(())
            }
            // If we have a prev hash and a last valid job we need to send new mining job before the
            // prev hash
            (Some((prev_h, _)), Some(mut job), true) => {
                let prev_h = prev_h.into_set_p_hash(channel_id, Some(job.job_id));

                // set future_job to true
                job.set_future();

                result.push(Mining::NewMiningJob(job));
                result.push(Mining::SetNewPrevHash(prev_h.clone()));
                Ok(())
            }
            // If we have everything we need, send the future jobs and the the prev hash
            (Some((prev_h, _)), Some(mut job), false) => {
                let prev_h = prev_h.into_set_p_hash(channel_id, Some(job.job_id));

                job.set_future();

                result.push(Mining::NewMiningJob(job));
                result.push(Mining::SetNewPrevHash(prev_h.clone()));

                // Safe unwrap cause we check that self.future_jobs is not empty
                let mut future_jobs = future_jobs.unwrap();

                while let Some(job) = future_jobs.pop() {
                    result.push(Mining::NewMiningJob(job));
                }
                Ok(())
            }
            // This can not happen because we can not have a valid job without a prev hash
            (None, Some(_), true) => unreachable!(),
            // This can not happen because we can not have a valid job without a prev hash
            (None, Some(_), false) => unreachable!(),
            // This can not happen because as soon as a prev hash is received we flush the future
            // jobs
            (Some(_), None, false) => unreachable!(),
        }
    }

    // When a new non HOM downstream opens a channel, we use this function to prepare all the
    // extended jobs (future and non) and the prev hash that we need to send downstream
    fn prepare_jobs_and_p_hash(&mut self, result: &mut Vec<Mining>, complete_id: u64) {
        // If group is 0 it means that we are preparing jobs and p hash for a non HOM downstream
        // that want to open a new extended channel in that case we want to use the channel id
        // TODO verify that this is true also for the case where the channel factory is in a proxy
        // and not in a pool.
        let group_id = match GroupId::into_group_id(complete_id) {
            0 => GroupId::into_channel_id(complete_id),
            a => a,
        };
        // This is the same thing of just check if there is a prev hash add it to result if there
        // is last_job add it to result and add each future job to result.
        // But using the pattern match is more clear how each option is handled
        let last_prev_hash = self.last_prev_hash.clone();
        let is_empty = self.future_jobs.is_empty();
        match (last_prev_hash, self.get_mut_last_valid_job(), is_empty) {
            // If we do not have anything just do nothing
            (None, None, true) => (),
            // If we have only future jobs we need to send them all after the
            // SetupConnectionSuccess message
            (None, None, false) => {
                for (job, group_id_job_sent) in &mut self.future_jobs {
                    if !group_id_job_sent.contains(&group_id) {
                        let mut job = job.clone();
                        job.channel_id = group_id;
                        group_id_job_sent.push(group_id);
                        result.push(Mining::NewExtendedMiningJob(job));
                    }
                }
            }
            // If we have just a prev hash we need to send it after the SetupConnectionSuccess
            // message
            (Some((prev_h, mut group_id_p_hash_sent)), None, true) => {
                if !group_id_p_hash_sent.contains(&group_id) {
                    let prev_h = prev_h.into_set_p_hash(group_id, None);
                    group_id_p_hash_sent.push(group_id);
                    result.push(Mining::SetNewPrevHash(prev_h.clone()));
                }
                self.last_prev_hash = Some((prev_h, group_id_p_hash_sent));
            }
            // If we have a prev hash and a last valid job we need to send before the prev hash and
            // the the valid job
            (Some((prev_h, mut group_id_p_hash_sent)), Some((job, group_id_job_sent)), true) => {
                if !group_id_p_hash_sent.contains(&group_id) {
                    let prev_h = prev_h.into_set_p_hash(group_id, Some(job.job_id));
                    group_id_p_hash_sent.push(group_id);
                    result.push(Mining::SetNewPrevHash(prev_h));
                }
                if !group_id_job_sent.contains(&group_id) {
                    let mut job = job.clone();
                    job.channel_id = group_id;
                    group_id_job_sent.push(group_id);
                    result.push(Mining::NewExtendedMiningJob(job));
                }
                self.last_prev_hash = Some((prev_h, group_id_p_hash_sent));
            }
            // If we have everything we need, send before the prev hash and then all the jobs
            (Some((prev_h, mut group_id_p_hash_sent)), Some((job, group_id_job_sent)), false) => {
                if !group_id_p_hash_sent.contains(&group_id) {
                    let prev_h = prev_h.into_set_p_hash(group_id, Some(job.job_id));
                    group_id_p_hash_sent.push(group_id);
                    result.push(Mining::SetNewPrevHash(prev_h));
                }

                if !group_id_job_sent.contains(&group_id) {
                    let mut job = job.clone();
                    job.channel_id = group_id;
                    group_id_job_sent.push(group_id);
                    result.push(Mining::NewExtendedMiningJob(job));
                }

                for (job, group_id_future_j_sent) in &mut self.future_jobs {
                    if !group_id_future_j_sent.contains(&group_id) {
                        let mut job = job.clone();
                        job.channel_id = group_id;
                        group_id_future_j_sent.push(group_id);
                        result.push(Mining::NewExtendedMiningJob(job));
                    }
                }
                self.last_prev_hash = Some((prev_h, group_id_p_hash_sent));
            }
            // This can not happen because we can not have a valid job without a prev hash
            (None, Some(_), true) => unreachable!(),
            // This can not happen because we can not have a valid job without a prev hash
            (None, Some(_), false) => unreachable!(),
            // This can not happen because as soon as a prev hash is received we flush the future
            // jobs
            (Some(_), None, false) => unreachable!(),
        }
    }

    /// Called when a new prev hash is received. If the respective job is available in the future
    /// job queue, we move the future job into the valid job slot and store the prev hash as the
    /// current prev hash to be referenced.
    fn on_new_prev_hash(&mut self, m: StagedPhash) -> Result<(), Error> {
        self.clear_valid_jobs();
        while let Some(mut job) = self.future_jobs.pop() {
            if job.0.job_id == m.job_id {
                let now = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs() as u32;
                job.0.set_no_future(now);
                self.add_valid_job(job.0, job.1);
                break;
            }
        }
        self.future_jobs = vec![];
        let id_to_job = &self.id_to_job;
        self.extended_job_coinbase_outputs
            .retain(|(_, job_id), _| id_to_job.contains_key(job_id));
        self.last_prev_hash_ = Some(crate::utils::u256_to_block_hash(m.prev_hash.clone()));
        let mut ids = vec![];
        for complete_id in self.standard_channels_for_non_hom_downstreams.keys() {
            let group_id = GroupId::into_group_id(*complete_id);
            if !ids.contains(&group_id) {
                ids.push(group_id)
            }
        }
        self.last_prev_hash = Some((m, ids));
        Ok(())
    }

    /// Called when a `NewExtendedMiningJob` arrives. If the job is future, we add it to the future
    /// queue. If the job is not future, we pair it with a the most recent prev hash
    fn on_new_extended_mining_job(
        &mut self,
        m: NewExtendedMiningJob<'static>,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<HashMap<u32, Mining<'static>, BuildNoHashHasher<u32>>, Error> {
        match (m.is_future(), &self.last_prev_hash) {
            (true, _) => {
                let mut result = HashMap::with_hasher(BuildNoHashHasher::default());
                self.prepare_jobs_for_downstream_on_new_extended(
                    &mut result,
                    &m,
                    additional_coinbase_script_data,
                )?;
                let mut ids = vec![];
                for complete_id in self.standard_channels_for_non_hom_downstreams.keys() {
                    let group_id = GroupId::into_group_id(*complete_id);
                    if !ids.contains(&group_id) {
                        ids.push(group_id)
                    }
                }
                self.future_jobs.push((m, ids));
                Ok(result)
            }
            (false, Some(_)) => {
                let mut result = HashMap::with_hasher(BuildNoHashHasher::default());
                self.prepare_jobs_for_downstream_on_new_extended(
                    &mut result,
                    &m,
                    additional_coinbase_script_data,
                )?;
                // If job is not future it must always be paired with the last received prev hash
                let mut ids = vec![];
                for complete_id in self.standard_channels_for_non_hom_downstreams.keys() {
                    let group_id = GroupId::into_group_id(*complete_id);
                    if !ids.contains(&group_id) {
                        ids.push(group_id)
                    }
                }
                self.add_valid_job(m, ids);
                if let Some((_p_hash, _)) = &self.last_prev_hash {
                    Ok(result)
                } else {
                    Err(Error::JobIsNotFutureButPrevHashNotPresent)
                }
            }
            // This should not happen when a non future job is received we always need to have a
            // prev hash
            (false, None) => Err(Error::JobIsNotFutureButPrevHashNotPresent),
        }
    }

    // When a new extended job is received we use this function to prepare the jobs to be sent
    // downstream (standard for hom and this job for non hom)
    fn prepare_jobs_for_downstream_on_new_extended(
        &mut self,
        result: &mut HashMap<u32, Mining, BuildNoHashHasher<u32>>,
        m: &NewExtendedMiningJob<'static>,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<(), Error> {
        self.prepare_standard_jobs_for_downstream_on_new_extended(
            result,
            m,
            additional_coinbase_script_data,
        )?;
        self.prepare_extended_jobs_for_downstream_on_new_extended(result, m);
        Ok(())
    }

    fn prepare_standard_jobs_for_downstream_on_new_extended(
        &mut self,
        result: &mut HashMap<u32, Mining, BuildNoHashHasher<u32>>,
        m: &NewExtendedMiningJob<'static>,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<(), Error> {
        for (id, channel) in &self.standard_channels_for_hom_downstreams {
            let job_id = self.job_ids.next();
            let mut standard_job = extended_to_standard_job(
                m,
                channel.extranonce.as_ref(),
                *id,
                Some(job_id),
                // We dont' care about what we have in the additional data since downstream do not
                // have to handle extranonces in that case, whatever is ok.
                additional_coinbase_script_data,
            )
            .unwrap();
            standard_job.channel_id = *id;
            let standard_job = Mining::NewMiningJob(standard_job);
            result.insert(*id, standard_job);
        }
        for id in self.standard_channels_for_non_hom_downstreams.keys() {
            let group_id = GroupId::into_group_id(*id);
            let mut extended = m.clone();
            extended.channel_id = group_id;
            let extended_job = Mining::NewExtendedMiningJob(extended);
            result.insert(group_id, extended_job);
        }
        Ok(())
    }

    fn prepare_extended_jobs_for_downstream_on_new_extended(
        &self,
        result: &mut HashMap<u32, Mining, BuildNoHashHasher<u32>>,
        m: &NewExtendedMiningJob<'static>,
    ) {
        for id in self.extended_channels.keys() {
            let mut extended = m.clone();
            extended.channel_id = *id;
            let extended_job = Mining::NewExtendedMiningJob(extended);
            result.insert(*id, extended_job);
        }
    }

    // If there is job creator, bitcoin_target is retrieved from there. If not, it is set to 0.
    // If there is a job creator we pass the correct template id. If not, we pass `None`
    // allow comparison chain because clippy wants to make job management assertion into a match
    // clause
    #[allow(clippy::comparison_chain)]
    #[allow(clippy::too_many_arguments)]
    fn check_target<TxHash: std::convert::AsRef<[u8]>>(
        &mut self,
        mut m: Share,
        bitcoin_target: Target,
        template_id: Option<u64>,
        up_id: u32,
        merkle_path: Vec<TxHash>,
        coinbase_tx_prefix: &[u8],
        coinbase_tx_suffix: &[u8],
        prev_blockhash: hash_types::BlockHash,
        bits: u32,
        additional_coinbase_script_data: Option<&[u8]>,
    ) -> Result<OnNewShare, Error> {
        debug!("Checking target for share {:?}", m);
        let upstream_target = match &self.kind {
            ExtendedChannelKind::Pool => Target::new(0, 0),
            ExtendedChannelKind::Proxy {
                upstream_target, ..
            }
            | ExtendedChannelKind::ProxyJd {
                upstream_target, ..
            } => upstream_target.clone(),
        };

        let (downstream_target, extranonce) = self.get_channel_specific_mining_info(&m)?;
        let extranonce_1_len = self.extranonces.get_range0_len();
        let extranonce_2 = extranonce[extranonce_1_len..].to_vec();
        match &mut m {
            Share::Extended(extended_share) => {
                extended_share.extranonce = extranonce_2.try_into()?;
            }
            Share::Standard(_) => (),
        };
        trace!(
            "On checking target coinbase prefix is: {:?}",
            coinbase_tx_prefix.to_hex_string(hex::Case::Lower)
        );
        trace!(
            "On checking target coinbase suffix is: {:?}",
            coinbase_tx_suffix.to_hex_string(hex::Case::Lower)
        );
        // Safe unwrap a sha256 can always be converted into [u8;32]
        let merkle_root: [u8; 32] = crate::utils::merkle_root_from_path(
            coinbase_tx_prefix,
            coinbase_tx_suffix,
            &extranonce[..],
            &merkle_path[..],
            additional_coinbase_script_data.unwrap_or(&[]),
        )
        .ok_or(Error::InvalidCoinbase)?
        .try_into()
        .unwrap();
        let version = match &m {
            Share::Extended(share) => share.version as i32,
            Share::Standard(share) => share.0.version as i32,
        };

        let header = Header {
            version: Version::from_consensus(version),
            prev_blockhash,
            merkle_root: (*Hash::from_bytes_ref(&merkle_root)).into(),
            time: m.get_n_time(),
            bits: CompactTarget::from_consensus(bits),
            nonce: m.get_nonce(),
        };

        trace!("On checking target header is: {:?}", header);
        let hash_ = header.block_hash();
        let hash: [u8; 32] = *hash_.to_raw_hash().as_ref();

        if tracing::level_enabled!(tracing::Level::DEBUG)
            || tracing::level_enabled!(tracing::Level::TRACE)
        {
            let bitcoin_target_log: binary_sv2::U256 = bitcoin_target.clone().into();
            let mut bitcoin_target_log = bitcoin_target_log.to_vec();
            bitcoin_target_log.reverse();
            debug!("Bitcoin target : {:?}", bitcoin_target_log.as_hex());
            let upstream_target: binary_sv2::U256 = upstream_target.clone().into();
            let mut upstream_target = upstream_target.to_vec();
            upstream_target.reverse();
            debug!("Upstream target: {:?}", upstream_target.to_vec().as_hex());
            let mut hash = hash;
            hash.reverse();
            debug!("Hash           : {:?}", hash.to_vec().as_hex());
        }
        let hash: Target = hash.into();

        if hash <= bitcoin_target {
            let mut print_hash: [u8; 32] = *hash_.to_raw_hash().as_ref();
            print_hash.reverse();

            info!(
                "Share hash meet bitcoin target: {:?}",
                print_hash.to_vec().as_hex()
            );

            let coinbase = [
                coinbase_tx_prefix,
                additional_coinbase_script_data.unwrap_or(&[]),
                &extranonce[..],
                coinbase_tx_suffix,
            ]
            .concat()
            .to_vec();
            match self.kind {
                ExtendedChannelKind::Proxy { .. } | ExtendedChannelKind::ProxyJd { .. } => {
                    let upstream_extranonce_space = self.extranonces.get_range0_len();
                    let extranonce_ = extranonce[upstream_extranonce_space..].to_vec();
                    let mut res = OnNewShare::ShareMeetBitcoinTarget((
                        m,
                        template_id,
                        coinbase,
                        extranonce.to_vec(),
                    ));
                    res.into_extended(extranonce_, up_id);
                    Ok(res)
                }
                ExtendedChannelKind::Pool => Ok(OnNewShare::ShareMeetBitcoinTarget((
                    m,
                    template_id,
                    coinbase,
                    extranonce.to_vec(),
                ))),
            }
        } else if hash <= upstream_target {
            match self.kind {
                ExtendedChannelKind::Proxy { .. } | ExtendedChannelKind::ProxyJd { .. } => {
                    let upstream_extranonce_space = self.extranonces.get_range0_len();
                    let extranonce = extranonce[upstream_extranonce_space..].to_vec();
                    let mut res = OnNewShare::SendSubmitShareUpstream((m, template_id));
                    res.into_extended(extranonce, up_id);
                    Ok(res)
                }
                ExtendedChannelKind::Pool => {
                    Ok(OnNewShare::SendSubmitShareUpstream((m, template_id)))
                }
            }
        } else if hash <= downstream_target {
            Ok(OnNewShare::ShareMeetDownstreamTarget)
        } else {
            error!("Share does not meet any target: {:?}", m);
            let error = SubmitSharesError {
                channel_id: m.get_channel_id(),
                sequence_number: m.get_sequence_number(),
                // Infallible unwrap we already know the len of the error code (is a
                // static string)
                error_code: SubmitSharesError::difficulty_too_low_error_code()
                    .to_string()
                    .try_into()
                    .unwrap(),
            };
            Ok(OnNewShare::SendErrorDownstream(error))
        }
    }

    /// Returns the downstream target and extranonce for the channel
    fn get_channel_specific_mining_info(
        &self,
        m: &Share,
    ) -> Result<(mining_sv2::Target, Vec<u8>), Error> {
        match m {
            Share::Extended(share) => {
                let channel = self
                    .extended_channels
                    .get(&m.get_channel_id())
                    .ok_or(Error::ShareDoNotMatchAnyChannel)?;
                let extranonce_prefix = channel.extranonce_prefix.to_vec();
                let dowstream_target = channel.target.clone().into();
                let extranonce = [&extranonce_prefix[..], &share.extranonce.to_vec()[..]]
                    .concat()
                    .to_vec();
                if extranonce.len() != self.extranonces.get_len() {
                    error!(
                        "Extranonce is not of the right len expected {} actual {}",
                        self.extranonces.get_len(),
                        extranonce.len()
                    );
                    return Err(Error::InvalidCoinbase);
                }
                Ok((dowstream_target, extranonce))
            }
            Share::Standard((share, group_id)) => match &self.kind {
                ExtendedChannelKind::Pool => {
                    let complete_id = GroupId::into_complete_id(*group_id, share.channel_id);
                    let mut channel = self
                        .standard_channels_for_non_hom_downstreams
                        .get(&complete_id);
                    if channel.is_none() {
                        channel = self
                            .standard_channels_for_hom_downstreams
                            .get(&share.channel_id);
                    };
                    Ok((
                        channel
                            .ok_or(Error::ShareDoNotMatchAnyChannel)?
                            .target
                            .clone(),
                        channel
                            .ok_or(Error::ShareDoNotMatchAnyChannel)?
                            .extranonce
                            .clone()
                            .to_vec(),
                    ))
                }
                ExtendedChannelKind::Proxy { .. } | ExtendedChannelKind::ProxyJd { .. } => {
                    let complete_id = GroupId::into_complete_id(*group_id, share.channel_id);
                    let mut channel = self
                        .standard_channels_for_non_hom_downstreams
                        .get(&complete_id);
                    if channel.is_none() {
                        channel = self
                            .standard_channels_for_hom_downstreams
                            .get(&share.channel_id);
                    };
                    Ok((
                        channel
                            .ok_or(Error::ShareDoNotMatchAnyChannel)?
                            .target
                            .clone(),
                        channel
                            .ok_or(Error::ShareDoNotMatchAnyChannel)?
                            .extranonce
                            .clone()
                            .to_vec(),
                    ))
                }
            },
        }
    }
    /// Updates the downstream target for the given channel_id
    fn update_target_for_channel(&mut self, channel_id: u32, new_target: Target) -> Option<bool> {
        let channel = self.extended_channels.get_mut(&channel_id)?;
        channel.target = new_target.into();
        Some(true)
    }
}

/// Used by a pool to in order to manage all downstream channel. It adds job creation capabilities
/// to ChannelFactory.
#[derive(Debug)]
pub struct PoolChannelFactory {
    inner: ChannelFactory,
    job_creator: JobsCreators,
    pool_coinbase_outputs: Vec<TxOut>,
    last_channel_coinbase_sequence: Option<[u8; 24]>,
    channel_coinbase_outputs: HashMap<u32, ChannelCoinbaseOutput, BuildNoHashHasher<u32>>,
    user_identifier_to_channel: HashMap<Vec<u8>, u32>,
    // Per channel additional data that the pool may want to include in the coinbase input script
    // as first part of the extranonce. This can be used to put things like the pool signature
    // or commitments. It is per channel since the pool may want to include different
    // commitment data based on downstream hash rate.
    // channel_if -> (additional_coinbase_script_data, old_additional_coinbase_script_data)
    #[allow(clippy::type_complexity)]
    channel_to_additional_coinbase_script_data:
        HashMap<u32, (Vec<u8>, Option<Vec<u8>>), BuildNoHashHasher<u32>>,
    // Additional data that the pool may want to include in the coinbase input script as first part
    // of the extranonce. This can be used to put things like the pool signature.
    additional_coinbase_script_data: Vec<u8>,
    // channel_id ++ job_id
    job_ids_using_old_add_data: HashSet<u32, BuildNoHashHasher<u32>>,
    // Extended channel_id -> latest SetCustomMiningJob
    negotiated_jobs: HashMap<u32, SetCustomMiningJob<'static>, BuildNoHashHasher<u32>>,
}

impl PoolChannelFactory {
    /// constructor
    pub fn new(
        ids: Arc<Mutex<GroupId>>,
        extranonces: ExtendedExtranonce,
        job_creator: JobsCreators,
        share_per_min: f32,
        kind: ExtendedChannelKind,
        pool_coinbase_outputs: Vec<TxOut>,
        additional_coinbase_script_data: Vec<u8>,
    ) -> Result<Self, Error> {
        if additional_coinbase_script_data.len() + extranonces.get_len() > 32 {
            error!("Additional coinbase script data is too big");
            return Err(Error::AdditionalCoinbaseScriptDataTooBig);
        }
        let inner = ChannelFactory {
            ids,
            standard_channels_for_non_hom_downstreams: HashMap::with_hasher(
                BuildNoHashHasher::default(),
            ),
            standard_channels_for_hom_downstreams: HashMap::with_hasher(
                BuildNoHashHasher::default(),
            ),
            extended_channels: HashMap::with_hasher(BuildNoHashHasher::default()),
            extranonces,
            share_per_min,
            future_jobs: Vec::new(),
            last_prev_hash: None,
            last_prev_hash_: None,
            last_valid_jobs: [None, None, None],
            id_to_job: HashMap::with_hasher(BuildNoHashHasher::default()),
            extended_job_coinbase_outputs: HashMap::new(),
            added_elements: 0,
            kind,
            job_ids: Id::new(),
            channel_to_group_id: HashMap::with_hasher(BuildNoHashHasher::default()),
            future_templates: HashMap::with_hasher(BuildNoHashHasher::default()),
        };

        Ok(Self {
            inner,
            job_creator,
            pool_coinbase_outputs,
            last_channel_coinbase_sequence: None,
            channel_coinbase_outputs: HashMap::with_hasher(BuildNoHashHasher::default()),
            user_identifier_to_channel: HashMap::new(),
            channel_to_additional_coinbase_script_data: HashMap::with_hasher(
                BuildNoHashHasher::default(),
            ),
            additional_coinbase_script_data,
            job_ids_using_old_add_data: HashSet::with_hasher(BuildNoHashHasher::default()),
            negotiated_jobs: HashMap::with_hasher(BuildNoHashHasher::default()),
        })
    }

    /// Enables stable channel outputs before opening any extended channels. Disabled by default.
    /// Each successful pool extended open (including restored prefixes) receives the next
    /// 8-byte counter, starting at 1; closing a channel never rewinds it. The 16-byte random
    /// prefix is initialized once and shared for the factory's lifetime. Standard jobs are
    /// unaffected; custom jobs must carry their channel's output.
    pub fn with_channel_coinbase_outputs(mut self) -> Self {
        assert!(self.inner.extended_channels.is_empty());
        self.last_channel_coinbase_sequence.get_or_insert_with(|| {
            let mut sequence = [0; 24];
            OsRng.fill_bytes(&mut sequence[..16]);
            sequence
        });
        self
    }

    /// Copies a channel's stable output so callers can materialize jobs outside the factory lock.
    pub fn channel_coinbase_output(&self, channel_id: u32) -> Option<ChannelCoinbaseOutput> {
        self.channel_coinbase_outputs.get(&channel_id).copied()
    }

    /// Registers a user identifier for an open extended channel. Repeating the same pair is allowed.
    /// NOTE: Requires `user_identifier` to be unique across channels; two different channels
    /// must not use the same user identifier.
    /// Returns `ChannelIdAlreadyInUse(existing_id)` if the identifier names another channel.
    pub fn register_channel_user(
        &mut self,
        channel_id: u32,
        user_identifier: &[u8],
    ) -> Result<(), Error> {
        if !self.inner.extended_channels.contains_key(&channel_id) {
            return Err(Error::NotFoundChannelId);
        }
        if let Some(existing_id) = self.user_identifier_to_channel.get(user_identifier) {
            if *existing_id != channel_id {
                return Err(Error::ChannelIdAlreadyInUse(*existing_id));
            }
        }
        self.user_identifier_to_channel
            .insert(user_identifier.to_vec(), channel_id);
        Ok(())
    }

    /// Looks up an explicitly registered user identifier, returning `None` after its channel closes.
    pub fn channel_id_for_user(&self, user_identifier: &[u8]) -> Option<u32> {
        self.user_identifier_to_channel
            .get(user_identifier)
            .copied()
    }

    fn next_channel_coinbase_output(&self) -> Result<Option<ChannelCoinbaseOutput>, Error> {
        self.last_channel_coinbase_sequence
            .map(|mut sequence| {
                for byte in sequence[16..].iter_mut().rev() {
                    let (next, carry) = byte.overflowing_add(1);
                    *byte = next;
                    if !carry {
                        return Ok(ChannelCoinbaseOutput(sequence));
                    }
                }
                Err(Error::ChannelCoinbaseSequenceExhausted)
            })
            .transpose()
    }

    fn finish_extended_channel_open(
        &mut self,
        channel_id: u32,
        output: Option<ChannelCoinbaseOutput>,
        mut messages: Vec<Mining<'static>>,
    ) -> Result<Vec<Mining<'static>>, Error> {
        if let Some(output) = output {
            for message in &mut messages {
                if let Mining::NewExtendedMiningJob(job) = message {
                    if let Err(error) = output.apply(job) {
                        self.close_channel(channel_id);
                        return Err(error);
                    }
                }
            }
            self.last_channel_coinbase_sequence = Some(output.0);
            self.channel_coinbase_outputs.insert(channel_id, output);
        }
        Ok(messages)
    }

    /// Calls [`ChannelFactory::add_standard_channel`]
    pub fn add_standard_channel(
        &mut self,
        request_id: u32,
        downstream_hash_rate: f32,
        is_header_only: bool,
        id: u32,
    ) -> Result<Vec<Mining>, Error> {
        let messages = self.inner.add_standard_channel(
            request_id,
            downstream_hash_rate,
            is_header_only,
            id,
            Some(&self.additional_coinbase_script_data),
        )?;
        if let Some(Mining::OpenStandardMiningChannelSuccess(success)) = messages.first() {
            self.channel_to_additional_coinbase_script_data.insert(
                success.channel_id,
                (self.additional_coinbase_script_data.clone(), None),
            );
        }
        Ok(messages)
    }

    /// Calls [`ChannelFactory::new_extended_channel`]
    pub fn new_extended_channel(
        &mut self,
        request_id: u32,
        hash_rate: f32,
        min_extranonce_size: u16,
    ) -> Result<Vec<Mining<'static>>, Error> {
        let output = self.next_channel_coinbase_output()?;
        match self.inner.new_extended_channel(
            request_id,
            hash_rate,
            min_extranonce_size,
            Some(&self.additional_coinbase_script_data),
        ) {
            // Channel is opened
            Ok((res, Some(channel_id))) => {
                self.channel_to_additional_coinbase_script_data.insert(
                    channel_id,
                    (self.additional_coinbase_script_data.clone(), None),
                );
                self.finish_extended_channel_open(channel_id, output, res)
            }
            // Channel is not opened and we can return an error downtream
            Ok((res, None)) => Ok(res),
            // Channel is not opened and we can not return an error downtream
            Err(e) => Err(e),
        }
    }

    /// Called when we want to replicate a channel already opened by another actor.
    /// is used only in the jd client from the template provider module to mock a pool.
    /// Anything else should open channel with the new_extended_channel function
    ///
    /// This does not register the replicated channel's extranonce in the `ExtendedExtranonce`
    /// allocator, so the factory can still allocate overlapping extranonce space later.
    /// SAFETY It is safe only when all of the following are true:
    /// - the factory is used only as a JD mock pool for share validation;
    /// - no standard or extended channels are opened from this factory after replication;
    /// - the channel id and extranonce come from a channel already opened by the trusted upstream;
    /// - no pool additional coinbase script data is configured.
    pub fn replicate_upstream_extended_channel_only_jd(
        &mut self,
        target: binary_sv2::U256<'static>,
        extranonce: mining_sv2::Extranonce,
        channel_id: u32,
        extranonce_size: u16,
    ) -> Option<()> {
        // This initialise a PoolChannelFactory for a JDC that can not have
        // additional_coinbase_script_data as it is set only by the pool.
        assert!(self.additional_coinbase_script_data.is_empty());
        self.channel_to_additional_coinbase_script_data.insert(
            channel_id,
            (self.additional_coinbase_script_data.clone(), None),
        );
        self.inner.replicate_upstream_extended_channel_only_jd(
            target,
            extranonce,
            channel_id,
            extranonce_size,
        )
    }

    /// Called when a pool wants to restore an already-known extended channel prefix.
    ///
    /// The provided `extranonce_prefix` must not include the pool's additional coinbase script
    /// data. That data is stored separately and prepended only when constructing the coinbase.
    /// this function can be used also from downstream, but the additional_coinbase_script_data
    /// should be empty (that field non empty only if the pool has to restore a channel, with a
    /// pool signature already assigned in a previous session)
    /// With channel coinbase outputs enabled, successful restorations receive a fresh marker.
    /// An occupied prefix is allowed only when every colliding channel has a distinct marker.
    pub fn replicate_pool_extended_channel(
        &mut self,
        request_id: u32,
        target: binary_sv2::U256<'static>,
        extranonce_prefix: mining_sv2::Extranonce,
        channel_id: u32,
        extranonce_size: u16,
        additional_coinbase_script_data: Vec<u8>,
    ) -> Result<Vec<Mining<'static>>, Error> {
        let output = self.next_channel_coinbase_output()?;
        if self.additional_coinbase_script_data.len() != additional_coinbase_script_data.len() {
            return Err(Error::NewAdditionalCoinbaseDataLenDoNotMatch);
        }

        let expected_prefix_len = self.inner.extranonces.get_prefix_len();
        let actual_prefix_len = extranonce_prefix.as_ref().len();
        if actual_prefix_len != expected_prefix_len {
            return Err(Error::InvalidExtranonceSize(
                expected_prefix_len as u16,
                actual_prefix_len.try_into().unwrap_or(u16::MAX),
            ));
        }

        let expected_extranonce_size = self.inner.extranonces.get_range2_len();
        if extranonce_size as usize != expected_extranonce_size {
            return Err(Error::InvalidExtranonceSize(
                expected_extranonce_size as u16,
                extranonce_size,
            ));
        }

        if self.inner.channel_to_group_id.contains_key(&channel_id) {
            return Err(Error::ChannelIdAlreadyInUse(channel_id));
        }
        for channel in self.inner.extended_channels.values().filter(|channel| {
            channel.extranonce_prefix.inner_as_ref() == extranonce_prefix.as_ref()
        }) {
            match (output, self.channel_coinbase_output(channel.channel_id)) {
                (Some(restored), Some(existing)) if restored != existing => warn!(
                    channel_id,
                    existing_channel_id = channel.channel_id,
                    "Restoring an occupied extranonce prefix with a distinct CHSEQ output"
                ),
                _ => return Err(Error::ExtranoncePrefixAlreadyInUse),
            }
        }
        self.inner
            .ids
            .safe_lock(|ids| ids.reserve_channel_id(channel_id))
            .unwrap()?;

        let downstream_extranonce_prefix = extranonce_prefix
            .into_prefix(expected_prefix_len, &additional_coinbase_script_data)
            .unwrap();
        self.channel_to_additional_coinbase_script_data
            .insert(channel_id, (additional_coinbase_script_data, None));
        self.inner.replicate_extended_channel(
            target.clone(),
            extranonce_prefix,
            channel_id,
            extranonce_size,
        );
        let success = OpenExtendedMiningChannelSuccess {
            request_id,
            channel_id,
            target,
            extranonce_size,
            extranonce_prefix: downstream_extranonce_prefix,
        };
        let mut result = vec![Mining::OpenExtendedMiningChannelSuccess(success)];
        self.inner
            .prepare_extended_jobs_and_p_hash(&mut result, channel_id);
        self.finish_extended_channel_open(channel_id, output, result)
    }

    /// Called only when a new prev hash is received by a Template Provider. It matches the
    /// message with a `job_id` and calls [`ChannelFactory::on_new_prev_hash`]
    /// it return the job_id
    pub fn on_new_prev_hash_from_tp(
        &mut self,
        m: &SetNewPrevHashFromTp<'static>,
    ) -> Result<u32, Error> {
        let job_id = self.job_creator.on_new_prev_hash(m).unwrap_or(0);
        let new_prev_hash = StagedPhash {
            job_id,
            prev_hash: m.prev_hash.clone(),
            min_ntime: m.header_timestamp,
            nbits: m.n_bits,
        };
        self.inner.on_new_prev_hash(new_prev_hash)?;
        Ok(job_id)
    }

    /// Called only when a new template is received by a Template Provider
    pub fn on_new_template(
        &mut self,
        m: &mut NewTemplate<'static>,
    ) -> Result<HashMap<u32, Mining<'static>, BuildNoHashHasher<u32>>, Error> {
        let new_job = self.job_creator.on_new_template(
            m,
            true,
            self.pool_coinbase_outputs.clone(),
            self.additional_coinbase_script_data.len() as u8,
        )?;
        let mut messages = self.inner.on_new_extended_mining_job(
            new_job,
            // Here we can use the data that we used to initialize this channel factory. Since this
            // value it will be used only to create standard jobs for HOM downstreams.
            Some(&self.additional_coinbase_script_data),
        )?;
        // Keep sent jobs consistent with share validation by applying the same channel marker.
        // This only takes effect after opting in with `with_channel_coinbase_outputs()`;
        // otherwise `channel_coinbase_output()` returns `None` and jobs remain unchanged.
        // Markers distinguish the pool's immediate downstreams, regardless of how they
        // redistribute work.
        for message in messages.values_mut() {
            if let Mining::NewExtendedMiningJob(job) = message {
                if let Some(output) = self.channel_coinbase_output(job.channel_id) {
                    output.apply(job)?;
                }
            }
        }
        Ok(messages)
    }

    /// Registers a template and returns the data needed to fan out extended jobs outside the
    /// caller's channel-factory lock. Apply [`Self::channel_coinbase_output`] to each cloned
    /// extended job before adding local outputs and registering its per-job output.
    #[allow(clippy::type_complexity)]
    pub fn on_new_template_for_extended_fanout(
        &mut self,
        m: &mut NewTemplate<'static>,
    ) -> Result<
        (
            NewExtendedMiningJob<'static>,
            Vec<u32>,
            HashMap<u32, Mining<'static>, BuildNoHashHasher<u32>>,
        ),
        Error,
    > {
        if !m.future_template && self.inner.last_prev_hash.is_none() {
            return Err(Error::JobIsNotFutureButPrevHashNotPresent);
        }

        let new_job = self.job_creator.on_new_template(
            m,
            true,
            self.pool_coinbase_outputs.clone(),
            self.additional_coinbase_script_data.len() as u8,
        )?;
        let extended_channel_ids = self.inner.extended_channels.keys().copied().collect();
        let mut standard_messages = HashMap::with_hasher(BuildNoHashHasher::default());
        self.inner
            .prepare_standard_jobs_for_downstream_on_new_extended(
                &mut standard_messages,
                &new_job,
                Some(&self.additional_coinbase_script_data),
            )?;

        let mut ids = vec![];
        for complete_id in self.inner.standard_channels_for_non_hom_downstreams.keys() {
            let group_id = GroupId::into_group_id(*complete_id);
            if !ids.contains(&group_id) {
                ids.push(group_id)
            }
        }

        match (new_job.is_future(), &self.inner.last_prev_hash) {
            (true, _) => {
                self.inner.future_jobs.push((new_job.clone(), ids));
                Ok((new_job, extended_channel_ids, standard_messages))
            }
            (false, Some(_)) => {
                self.inner.add_valid_job(new_job.clone(), ids);
                Ok((new_job, extended_channel_ids, standard_messages))
            }
            (false, None) => unreachable!("non-future jobs require a prevhash"),
        }
    }

    /// Called when a `SubmitSharesStandard` message is received from the downstream. We check the
    /// shares against the channel's respective target and return `OnNewShare` to let us know if
    /// and where the shares should be relayed
    pub fn on_submit_shares_standard(
        &mut self,
        m: SubmitSharesStandard,
    ) -> Result<OnNewShare, Error> {
        let additional_coinbase_script_data = self
            .get_additional_coinbase_script_data(m.channel_id, m.job_id)
            .ok_or(Error::ShareDoNotMatchAnyJob)?;
        match self.inner.channel_to_group_id.get(&m.channel_id) {
            Some(g_id) => {
                let referenced_job = self
                    .inner
                    .get_valid_job(m.job_id)
                    .cloned()
                    .ok_or(Error::ShareDoNotMatchAnyJob)?
                    .0;
                let merkle_path = referenced_job.merkle_path.to_vec();
                let template_id = self
                    .job_creator
                    .get_template_id_from_job(referenced_job.job_id)
                    .ok_or(Error::NoTemplateForId)?;
                let target = self.job_creator.last_target();
                let prev_blockhash = self
                    .inner
                    .last_prev_hash_
                    .ok_or(Error::ShareDoNotMatchAnyJob)?;
                let bits = self
                    .inner
                    .last_prev_hash
                    .as_ref()
                    .ok_or(Error::ShareDoNotMatchAnyJob)?
                    .0
                    .nbits;
                self.inner.check_target(
                    Share::Standard((m, *g_id)),
                    target,
                    Some(template_id),
                    0,
                    merkle_path,
                    referenced_job.coinbase_tx_prefix.as_ref(),
                    referenced_job.coinbase_tx_suffix.as_ref(),
                    prev_blockhash,
                    bits,
                    Some(&additional_coinbase_script_data),
                )
            }
            None => {
                let err = SubmitSharesError {
                    channel_id: m.channel_id,
                    sequence_number: m.sequence_number,
                    error_code: SubmitSharesError::invalid_channel_error_code()
                        .to_string()
                        .try_into()
                        .unwrap(),
                };
                Ok(OnNewShare::SendErrorDownstream(err))
            }
        }
    }

    /// Called when a `SubmitSharesExtended` message is received from the downstream. We check the
    /// shares against the channel's respective target and return `OnNewShare` to let us know if
    /// and where the shares should be relayed
    pub fn on_submit_shares_extended(
        &mut self,
        m: SubmitSharesExtended,
    ) -> Result<OnNewShare, Error> {
        let target = self.job_creator.last_target();
        let additional_coinbase_script_data = self
            .get_additional_coinbase_script_data(m.channel_id, m.job_id)
            .ok_or(Error::ShareDoNotMatchAnyJob)?;
        // Select the latest custom job by channel; the pool may rewrite its wire job ID.
        // WARNING: Only the latest custom job is retained. Delayed shares for an older job
        // are checked against its replacement and may be rejected. A future lookup by job ID
        // must reconcile factory IDs with the pool's advertised wire IDs.
        if let Some(referenced_job) = self.negotiated_jobs.get(&m.channel_id) {
            let merkle_path = referenced_job.merkle_path.to_vec();
            let extended_job = job_creator::extended_job_from_custom_job(
                referenced_job,
                additional_coinbase_script_data.len() as u8,
                self.inner.extranonces.get_len() as u8,
            )?;
            let prev_blockhash = crate::utils::u256_to_block_hash(referenced_job.prev_hash.clone());
            let bits = referenced_job.nbits;
            match self.inner.check_target(
                Share::Extended(m.clone().into_static()),
                target,
                None,
                0,
                merkle_path,
                extended_job.coinbase_tx_prefix.as_ref(),
                extended_job.coinbase_tx_suffix.as_ref(),
                prev_blockhash,
                bits,
                Some(&additional_coinbase_script_data),
            ) {
                // Since this is a share for a custom job and there is no way to know if the share
                // do not met target cause pool sent a new extranonce prefix and the miner is still
                // using the old one we check also against the old one since we don't want to fail
                // in that case.
                Ok(OnNewShare::SendErrorDownstream(m_)) => {
                    match self.get_old_additional_coinbase_script_data(m.channel_id) {
                        Some(additional_coinbase_script_data) => {
                            let target = self.job_creator.last_target();
                            let merkle_path = referenced_job.merkle_path.to_vec();
                            let extended_job = job_creator::extended_job_from_custom_job(
                                referenced_job,
                                additional_coinbase_script_data.len() as u8,
                                self.inner.extranonces.get_len() as u8,
                            )?;
                            self.inner.check_target(
                                Share::Extended(m.into_static()),
                                target,
                                None,
                                0,
                                merkle_path,
                                extended_job.coinbase_tx_prefix.as_ref(),
                                extended_job.coinbase_tx_suffix.as_ref(),
                                prev_blockhash,
                                bits,
                                Some(&additional_coinbase_script_data),
                            )
                        }
                        None => Ok(OnNewShare::SendErrorDownstream(m_)),
                    }
                }
                Ok(res) => Ok(res),
                Err(err) => Err(err),
            }
        } else {
            let mut referenced_job = self
                .inner
                .get_valid_job(m.job_id)
                .cloned()
                .ok_or(Error::ShareDoNotMatchAnyJob)?
                .0;
            let merkle_path = referenced_job.merkle_path.to_vec();
            let template_id = self
                .job_creator
                .get_template_id_from_job(referenced_job.job_id)
                .ok_or(Error::NoTemplateForId)?;
            if let Some(output) = self.channel_coinbase_output(m.channel_id) {
                output.apply(&mut referenced_job)?;
            }
            if let Some(output) = self
                .inner
                .extended_job_coinbase_outputs
                .get(&(m.channel_id, m.job_id))
            {
                let suffix = referenced_job.coinbase_tx_suffix.as_ref();
                let encoded_outputs = suffix.get(4..).ok_or(Error::InvalidCoinbase)?;
                let (mut outputs, consumed): (Vec<TxOut>, usize) =
                    deserialize_partial(encoded_outputs).map_err(|_| Error::InvalidCoinbase)?;
                outputs.push(output.clone());
                referenced_job.coinbase_tx_suffix = [
                    &suffix[..4],
                    serialize(&outputs).as_slice(),
                    &encoded_outputs[consumed..],
                ]
                .concat()
                .try_into()?;
            }
            let prev_blockhash = self
                .inner
                .last_prev_hash_
                .ok_or(Error::ShareDoNotMatchAnyJob)?;
            let bits = self
                .inner
                .last_prev_hash
                .as_ref()
                .ok_or(Error::ShareDoNotMatchAnyJob)?
                .0
                .nbits;
            self.inner.check_target(
                Share::Extended(m.into_static()),
                target,
                Some(template_id),
                0,
                merkle_path,
                referenced_job.coinbase_tx_prefix.as_ref(),
                referenced_job.coinbase_tx_suffix.as_ref(),
                prev_blockhash,
                bits,
                Some(&additional_coinbase_script_data),
            )
        }
    }

    /// Reserves and returns a new group ID. Use [`Self::close_group`] to release an unused group.
    pub fn new_group_id(&mut self) -> u32 {
        let new_id = self.inner.ids.safe_lock(|ids| ids.new_group_id()).unwrap();
        // Reserve the group ID before any channels are opened in it.
        self.inner.channel_to_group_id.insert(new_id, new_id);
        new_id
    }

    /// Utility function to return a new standard channel id
    pub fn new_standard_id_for_hom(&mut self) -> u32 {
        let hom_group_id = 0;
        let new_id = self
            .inner
            .ids
            .safe_lock(|ids| ids.new_channel_id(hom_group_id))
            .unwrap();
        new_id
    }

    /// Returns the full extranonce, extranonce1 (static for channel) + extranonce2 (miner nonce
    /// space)
    pub fn extranonce_from_downstream_extranonce(
        &self,
        ext: mining_sv2::Extranonce,
    ) -> Option<mining_sv2::Extranonce> {
        self.inner
            .extranonces
            .extranonce_from_downstream_extranonce(ext)
    }

    /// Compatibility entry point retaining the behavior on main.
    /// Use [`Self::try_on_new_set_custom_mining_job`] to validate CHSEQ and handle rejected jobs.
    // TODO: Channel restoration is not active yet and still needs refinement. Once that feature
    // is complete, remove this method entirely in favor of try_on_new_set_custom_mining_job.
    pub fn on_new_set_custom_mining_job(
        &mut self,
        set_custom_mining_job: SetCustomMiningJob<'static>,
    ) -> SetCustomMiningJobSuccess {
        self.negotiated_jobs.insert(
            set_custom_mining_job.channel_id,
            set_custom_mining_job.clone(),
        );
        SetCustomMiningJobSuccess {
            channel_id: set_custom_mining_job.channel_id,
            request_id: set_custom_mining_job.request_id,
            job_id: self.inner.job_ids.next(),
        }
    }

    /// Called when a new custom mining job arrives
    ///
    /// # Errors
    /// Rejects a custom job without exactly one matching CHSEQ output when the channel has a
    /// registered output. Rejected jobs do not replace the channel's current job or consume a job ID.
    pub fn try_on_new_set_custom_mining_job(
        &mut self,
        set_custom_mining_job: SetCustomMiningJob<'static>,
    ) -> Result<SetCustomMiningJobSuccess, SetCustomMiningJobError<'static>> {
        if !self.check_custom_job_channel_coinbase_output(&set_custom_mining_job) {
            return Err(SetCustomMiningJobError {
                channel_id: set_custom_mining_job.channel_id,
                request_id: set_custom_mining_job.request_id,
                error_code: "invalid-job-param-value-coinbase_tx_outputs"
                    .to_string()
                    .try_into()
                    .unwrap(),
            });
        }
        let success = SetCustomMiningJobSuccess {
            channel_id: set_custom_mining_job.channel_id,
            request_id: set_custom_mining_job.request_id,
            job_id: self.inner.job_ids.next(),
        };
        self.negotiated_jobs
            .insert(set_custom_mining_job.channel_id, set_custom_mining_job);
        Ok(success)
    }

    fn check_custom_job_channel_coinbase_output(
        &self,
        set_custom_mining_job: &SetCustomMiningJob<'static>,
    ) -> bool {
        if let Some(output) = self.channel_coinbase_output(set_custom_mining_job.channel_id) {
            let outputs = job_creator::tx_outputs_to_costum_scripts(
                set_custom_mining_job.coinbase_tx_outputs.as_ref(),
            );
            let mut channel_outputs = outputs.iter().filter(|output| {
                output
                    .script_pubkey
                    .as_bytes()
                    .starts_with(b"\x6a\x1dCHSEQ")
            });
            return channel_outputs.next() == Some(&output.tx_out())
                && channel_outputs.next().is_none();
        }
        true
    }

    /// Get extended channel ids
    pub fn get_extended_channels_ids(&self) -> Vec<u32> {
        self.inner.extended_channels.keys().copied().collect()
    }

    /// Update coinbase outputs
    pub fn update_pool_outputs(&mut self, outs: Vec<TxOut>) {
        self.pool_coinbase_outputs = outs;
    }

    /// Calls [`ChannelFactory::update_target_for_channel`]
    /// Set a particular downstream channel target.
    pub fn update_target_for_channel(
        &mut self,
        channel_id: u32,
        new_target: Target,
    ) -> Option<bool> {
        self.inner.update_target_for_channel(channel_id, new_target)
    }

    /// Set the target for this channel. This is the upstream target.
    pub fn set_target(&mut self, new_target: &mut Target) {
        self.inner.kind.set_target(new_target);
    }

    // TODO ret can not be larger then 32 bytes maybe use the stack for it?
    #[inline(always)]
    pub fn get_additional_coinbase_script_data(
        &self,
        channel_id: u32,
        job_id: u32,
    ) -> Option<Vec<u8>> {
        debug_assert!({
            let have_old = self.job_ids_using_old_add_data.contains(&job_id);
            let not_have_old = self
                .channel_to_additional_coinbase_script_data
                .get(&channel_id)
                .unwrap()
                .1
                .is_some();
            if have_old {
                !not_have_old
            } else {
                true
            }
        });
        match self
            .channel_to_additional_coinbase_script_data
            .get(&channel_id)
        {
            Some((add_data, None)) => Some(add_data.clone()),
            Some((add_data, Some(old_data))) => {
                if self.job_ids_using_old_add_data.contains(&job_id) {
                    Some(old_data.clone())
                } else {
                    Some(add_data.clone())
                }
            }
            None => None,
        }
    }

    // TODO ret can not be larger then 32 bytes maybe use the stack for it?
    #[inline(always)]
    fn get_old_additional_coinbase_script_data(&self, channel_id: u32) -> Option<Vec<u8>> {
        self.channel_to_additional_coinbase_script_data
            .get(&channel_id)?
            .1
            .clone()
    }

    /// This set a new additional coinbase script data for a particular channel. Think to keep in
    /// mind before using this function:
    /// 1. Standard hom channels are not affected by the change
    /// 2. The new additional data MUST have the exact same len as the additonal data used to
    ///    initialize the channle factory with PoolChannelFactory::new
    /// 3. For job provided by the pool, all the non future sent before the new additional data will
    ///    have the old additional data. All the future jobs and the non future jobs sent after the
    ///    new additional data will have the new additional data
    /// 4. Custom jobs will be checked against the new additional data, if the check fail we check
    ///    against the old additional data if also this check fail we return SubmitShareError
    pub fn change_additional_coinbase_script_data(
        &mut self,
        new_data: Vec<u8>,
        channel_id: u32,
    ) -> Result<Mining, Error> {
        if self.additional_coinbase_script_data.len() == new_data.len() {
            let mut ids_for_old_data = HashSet::with_hasher(BuildNoHashHasher::default());
            for id in self.inner.id_to_job.keys() {
                ids_for_old_data.insert(*id);
            }
            self.job_ids_using_old_add_data = ids_for_old_data;
            match self
                .channel_to_additional_coinbase_script_data
                .get_mut(&channel_id)
            {
                Some(data) => {
                    data.1 = Some(data.0.clone());
                    data.0 = new_data.clone();
                    let res = SetExtranoncePrefix {
                        channel_id,
                        extranonce_prefix: new_data.try_into().expect(""),
                    };
                    Ok(Mining::SetExtranoncePrefix(res))
                }
                None => Err(Error::NotFoundChannelId),
            }
        } else {
            Err(Error::NewAdditionalCoinbaseDataLenDoNotMatch)
        }
    }

    /// Closes a mining channel and removes its group when the last member closes.
    /// WARNING: Library adopters must close every channel and release unused group reservations
    /// with [`Self::close_group`] when a downstream disconnects; the factory does not observe
    /// connection teardown.
    pub fn close_channel(&mut self, channel_id: u32) {
        self.channel_to_additional_coinbase_script_data
            .retain(|k, _| k != &channel_id);
        self.channel_coinbase_outputs.remove(&channel_id);
        self.user_identifier_to_channel
            .retain(|_, id| *id != channel_id);
        self.negotiated_jobs.remove(&channel_id);
        self.inner.close_channel(channel_id);
    }

    /// Closes every standard channel in a nonzero group and releases its reservation and job
    /// delivery tracking, including when no channels were opened in it.
    ///
    /// The shared group `0` and IDs that do not name a reserved group are ignored. Extended and
    /// header-only channels must be closed individually with [`Self::close_channel`].
    pub fn close_group(&mut self, group_id: u32) {
        if group_id == 0 || self.inner.channel_to_group_id.get(&group_id) != Some(&group_id) {
            return;
        }
        let channel_ids: HashSet<_, BuildNoHashHasher<u32>> = self
            .inner
            .standard_channels_for_non_hom_downstreams
            .values()
            .filter(|channel| channel.group_id == group_id)
            .map(|channel| channel.channel_id)
            .collect();
        if channel_ids.is_empty() {
            self.inner.remove_group(group_id);
            return;
        }
        self.inner
            .standard_channels_for_non_hom_downstreams
            .retain(|_, channel| channel.group_id != group_id);
        self.inner
            .channel_to_group_id
            .retain(|_, group| *group != group_id);
        self.channel_to_additional_coinbase_script_data
            .retain(|channel_id, _| !channel_ids.contains(channel_id));
        self.channel_coinbase_outputs
            .retain(|channel_id, _| !channel_ids.contains(channel_id));
        self.negotiated_jobs
            .retain(|channel_id, _| !channel_ids.contains(channel_id));
        self.inner
            .extended_job_coinbase_outputs
            .retain(|(channel_id, _), _| !channel_ids.contains(channel_id));
        self.inner.remove_group(group_id);
    }

    /// Compatibility adapter for a DIFF32 difficulty output in a coinbase suffix.
    /// Forwards the difficulty output to [`Self::register_extended_job_coinbase_output`].
    /// Malformed suffixes and suffixes without a difficulty output are logged and ignored.
    ///  TODO uncomment the following after this has been merged on main
    //#[deprecated(note = "Use register_extended_job_coinbase_output with the difficulty TxOut")]
    pub fn register_extended_job_variant(
        &mut self,
        channel_id: u32,
        job_id: u32,
        coinbase_suffix: Vec<u8>,
    ) {
        let output = coinbase_suffix
            .get(4..)
            .and_then(|encoded| deserialize_partial::<Vec<TxOut>>(encoded).ok())
            .and_then(|(outputs, _)| {
                outputs.into_iter().find(|output| {
                    output.value == Amount::ZERO
                        && output.script_pubkey.len() == 12
                        && output
                            .script_pubkey
                            .as_bytes()
                            .starts_with(b"\x6a\x0aDIFF32")
                })
            });
        if let Some(output) = output {
            self.register_extended_job_coinbase_output(channel_id, job_id, output);
        } else {
            warn!(
                channel_id,
                job_id, "Ignoring legacy job variant without a valid DIFF32 output"
            );
        }
    }

    /// Registers an additional coinbase output for one channel's pool-created extended job.
    /// Share validation appends it to the canonical job's coinbase outputs.
    pub fn register_extended_job_coinbase_output(
        &mut self,
        channel_id: u32,
        job_id: u32,
        output: TxOut,
    ) {
        self.inner
            .extended_job_coinbase_outputs
            .insert((channel_id, job_id), output);
    }

    /// Clones the canonical current extended job with its stable channel output, without local
    /// per-job outputs such as difficulty commitments.
    /// Returns `None` while the channel has an active negotiated/custom job.
    pub fn current_extended_job_for_channel(
        &self,
        channel_id: u32,
    ) -> Option<NewExtendedMiningJob<'static>> {
        if self.negotiated_jobs.contains_key(&channel_id) {
            return None;
        }

        let mut job = self.inner.get_last_valid_job()?.0.clone();
        if let Some(output) = self.channel_coinbase_output(channel_id) {
            output.apply(&mut job).ok()?;
        }
        Some(job)
    }

    pub fn get_extranonce_len(&self) -> usize {
        self.inner.extranonces.get_len()
    }

    pub fn get_extranonce_prefix(&self, channel_id: u32) -> Option<Vec<u8>> {
        let channel = self.inner.extended_channels.get(&channel_id)?;
        Some(channel.extranonce_prefix.to_vec())
    }
}

/// Used by proxies that want to open extended channels with upstream. If the proxy has job
/// declaration capabilities, we set the job creator and the coinbase outs.
#[derive(Debug)]
pub struct ProxyExtendedChannelFactory {
    inner: ChannelFactory,
    job_creator: Option<JobsCreators>,
    pool_coinbase_outputs: Option<Vec<TxOut>>,
    // Id assigned to the extended channel by upstream
    extended_channel_id: u32,
}

impl ProxyExtendedChannelFactory {
    /// Constructor
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        ids: Arc<Mutex<GroupId>>,
        extranonces: ExtendedExtranonce,
        job_creator: Option<JobsCreators>,
        share_per_min: f32,
        kind: ExtendedChannelKind,
        pool_coinbase_outputs: Option<Vec<TxOut>>,
        extended_channel_id: u32,
    ) -> Self {
        match &kind {
            ExtendedChannelKind::Proxy { .. } => {
                if job_creator.is_some() {
                    panic!("Channel factory of kind Proxy can not be initialized with a JobCreators");
                };
            },
            ExtendedChannelKind::ProxyJd { .. } => {
                if job_creator.is_none() {
                    panic!("Channel factory of kind ProxyJd must be initialized with a JobCreators");
                };
            }
            ExtendedChannelKind::Pool => panic!("Try to construct an ProxyExtendedChannelFactory with pool kind, kind must be Proxy or ProxyJd"),
        };
        let inner = ChannelFactory {
            ids,
            standard_channels_for_non_hom_downstreams: HashMap::with_hasher(
                BuildNoHashHasher::default(),
            ),
            standard_channels_for_hom_downstreams: HashMap::with_hasher(
                BuildNoHashHasher::default(),
            ),
            extended_channels: HashMap::with_hasher(BuildNoHashHasher::default()),
            extranonces,
            share_per_min,
            future_jobs: Vec::new(),
            last_prev_hash: None,
            last_prev_hash_: None,
            last_valid_jobs: [None, None, None],
            id_to_job: HashMap::with_hasher(BuildNoHashHasher::default()),
            extended_job_coinbase_outputs: HashMap::new(),
            added_elements: 0,
            kind,
            job_ids: Id::new(),
            channel_to_group_id: HashMap::with_hasher(BuildNoHashHasher::default()),
            future_templates: HashMap::with_hasher(BuildNoHashHasher::default()),
        };
        ProxyExtendedChannelFactory {
            inner,
            job_creator,
            pool_coinbase_outputs,
            extended_channel_id,
        }
    }

    /// Calls [`ChannelFactory::add_standard_channel`]
    pub fn add_standard_channel(
        &mut self,
        request_id: u32,
        downstream_hash_rate: f32,
        id_header_only: bool,
        id: u32,
    ) -> Result<Vec<Mining>, Error> {
        self.inner
            .add_standard_channel(request_id, downstream_hash_rate, id_header_only, id, None)
    }

    /// Calls [`ChannelFactory::new_extended_channel`]
    pub fn new_extended_channel(
        &mut self,
        request_id: u32,
        hash_rate: f32,
        min_extranonce_size: u16,
    ) -> Result<Vec<Mining>, Error> {
        self.inner
            .new_extended_channel(request_id, hash_rate, min_extranonce_size, None)
            .map(|x| x.0)
    }

    /// Called only when a new prev hash is received by a Template Provider when job declaration is
    /// used. It matches the message with a `job_id`, creates a new custom job, and calls
    /// [`ChannelFactory::on_new_prev_hash`]
    pub fn on_new_prev_hash_from_tp(
        &mut self,
        m: &SetNewPrevHashFromTp<'static>,
    ) -> Result<Option<(PartialSetCustomMiningJob, u32)>, Error> {
        if let Some(job_creator) = self.job_creator.as_mut() {
            let job_id = job_creator.on_new_prev_hash(m).unwrap_or(0);
            let new_prev_hash = StagedPhash {
                job_id,
                prev_hash: m.prev_hash.clone(),
                min_ntime: m.header_timestamp,
                nbits: m.n_bits,
            };
            let mut custom_job = None;
            if let Some(template) = self.inner.future_templates.get(&job_id) {
                custom_job = Some((
                    PartialSetCustomMiningJob {
                        version: template.version,
                        prev_hash: new_prev_hash.prev_hash.clone(),
                        min_ntime: new_prev_hash.min_ntime,
                        nbits: new_prev_hash.nbits,
                        coinbase_tx_version: template.coinbase_tx_version,
                        coinbase_prefix: template.coinbase_prefix.clone(),
                        coinbase_tx_input_n_sequence: template.coinbase_tx_input_sequence,
                        coinbase_tx_value_remaining: template.coinbase_tx_value_remaining,
                        coinbase_tx_outputs: template.coinbase_tx_outputs.clone(),
                        coinbase_tx_locktime: template.coinbase_tx_locktime,
                        merkle_path: template.merkle_path.clone(),
                        extranonce_size: self.inner.extranonces.get_len() as u16,
                        future_job: template.future_template,
                    },
                    job_id,
                ));
            }
            self.inner.future_templates = HashMap::with_hasher(BuildNoHashHasher::default());
            self.inner.on_new_prev_hash(new_prev_hash)?;
            Ok(custom_job)
        } else {
            panic!("A channel factory without job creator do not have declaration capabilities")
        }
    }

    /// Called only when a new template is received by a Template Provider when job declaration is
    /// used. It creates a new custom job and calls
    /// [`ChannelFactory::on_new_extended_mining_job`]
    #[allow(clippy::type_complexity)]
    pub fn on_new_template(
        &mut self,
        m: &mut NewTemplate<'static>,
    ) -> Result<
        (
            // downstream job_id -> downstream message (newextjob or newjob)
            HashMap<u32, Mining<'static>, BuildNoHashHasher<u32>>,
            // PartialSetCustomMiningJob to send to the pool
            Option<PartialSetCustomMiningJob>,
            // job_id registered in the channel, the one that SetNewPrevHash refer to (upstsream
            // job id)
            u32,
        ),
        Error,
    > {
        if let (Some(job_creator), Some(pool_coinbase_outputs)) = (
            self.job_creator.as_mut(),
            self.pool_coinbase_outputs.as_mut(),
        ) {
            let new_job = job_creator.on_new_template(m, true, pool_coinbase_outputs.clone(), 0)?;
            let id = new_job.job_id;
            if !new_job.is_future() && self.inner.last_prev_hash.is_some() {
                let prev_hash = self.last_prev_hash().unwrap();
                let min_ntime = self.last_min_ntime().unwrap();
                let nbits = self.last_nbits().unwrap();
                let extranonce_size = self.extranonce_size() as u16;
                let custom_mining_job = PartialSetCustomMiningJob {
                    version: m.version,
                    prev_hash,
                    min_ntime,
                    nbits,
                    coinbase_tx_version: m.coinbase_tx_version,
                    coinbase_prefix: m.coinbase_prefix.clone(),
                    coinbase_tx_input_n_sequence: m.coinbase_tx_input_sequence,
                    coinbase_tx_value_remaining: m.coinbase_tx_value_remaining,
                    coinbase_tx_outputs: m.coinbase_tx_outputs.clone(),
                    coinbase_tx_locktime: m.coinbase_tx_locktime,
                    merkle_path: m.merkle_path.clone(),
                    extranonce_size,
                    future_job: m.future_template,
                };
                return Ok((
                    self.inner.on_new_extended_mining_job(new_job, None)?,
                    Some(custom_mining_job),
                    id,
                ));
            } else if new_job.is_future() {
                self.inner
                    .future_templates
                    .insert(new_job.job_id, m.clone());
            }
            Ok((
                self.inner.on_new_extended_mining_job(new_job, None)?,
                None,
                id,
            ))
        } else {
            panic!("Either channel factory has no job creator or pool_coinbase_outputs are not yet set")
        }
    }

    /// Called when a `SubmitSharesStandard` message is received from the downstream. We check the
    /// shares against the channel's respective target and return `OnNewShare` to let us know if
    /// and where the shares should be relayed
    pub fn on_submit_shares_extended(
        &mut self,
        m: SubmitSharesExtended<'static>,
    ) -> Result<OnNewShare, Error> {
        let merkle_path = self
            .inner
            .get_valid_job(m.job_id)
            .as_ref()
            .ok_or(Error::ShareDoNotMatchAnyJob)?
            .0
            .merkle_path
            .to_vec();

        let referenced_job = self
            .inner
            .get_valid_job(m.job_id)
            .cloned()
            .ok_or(Error::ShareDoNotMatchAnyJob)?
            .0;

        if referenced_job.job_id != m.job_id {
            let error = SubmitSharesError {
                channel_id: m.channel_id,
                sequence_number: m.sequence_number,
                // Infallible unwrap we already know the len of the error code (is a
                // static string)
                error_code: SubmitSharesError::invalid_job_id_error_code()
                    .to_string()
                    .try_into()
                    .unwrap(),
            };
            return Ok(OnNewShare::SendErrorDownstream(error));
        }

        if let Some(job_creator) = self.job_creator.as_mut() {
            let template_id = job_creator
                .get_template_id_from_job(referenced_job.job_id)
                .ok_or(Error::NoTemplateForId)?;
            let bitcoin_target = job_creator.last_target();
            let prev_blockhash = self
                .inner
                .last_prev_hash_
                .ok_or(Error::ShareDoNotMatchAnyJob)?;
            let bits = self
                .inner
                .last_prev_hash
                .as_ref()
                .ok_or(Error::ShareDoNotMatchAnyJob)?
                .0
                .nbits;
            self.inner.check_target(
                Share::Extended(m),
                bitcoin_target,
                Some(template_id),
                self.extended_channel_id,
                merkle_path,
                referenced_job.coinbase_tx_prefix.as_ref(),
                referenced_job.coinbase_tx_suffix.as_ref(),
                prev_blockhash,
                bits,
                None,
            )
        } else {
            let bitcoin_target = [0; 32];
            // if there is not job_creator is not proxy duty to check if target is below or above
            // bitcoin target so we set bitcoin_target = 0.
            let prev_blockhash = self
                .inner
                .last_prev_hash_
                .ok_or(Error::ShareDoNotMatchAnyJob)?;
            let bits = self
                .inner
                .last_prev_hash
                .as_ref()
                .ok_or(Error::ShareDoNotMatchAnyJob)?
                .0
                .nbits;
            self.inner.check_target(
                Share::Extended(m),
                bitcoin_target.into(),
                None,
                self.extended_channel_id,
                merkle_path,
                referenced_job.coinbase_tx_prefix.as_ref(),
                referenced_job.coinbase_tx_suffix.as_ref(),
                prev_blockhash,
                bits,
                None,
            )
        }
    }

    /// Called when a `SubmitSharesStandard` message is received from the Downstream. We check the
    /// shares against the channel's respective target and return `OnNewShare` to let us know if
    /// and where the shares should be relayed
    pub fn on_submit_shares_standard(
        &mut self,
        m: SubmitSharesStandard,
    ) -> Result<OnNewShare, Error> {
        let merkle_path = self
            .inner
            .get_valid_job(m.job_id)
            .as_ref()
            .ok_or(Error::ShareDoNotMatchAnyJob)?
            .0
            .merkle_path
            .to_vec();
        let referenced_job = self
            .inner
            .get_valid_job(m.job_id)
            .cloned()
            .ok_or(Error::ShareDoNotMatchAnyJob)?
            .0;
        match self.inner.channel_to_group_id.get(&m.channel_id) {
            Some(g_id) => {
                if let Some(job_creator) = self.job_creator.as_mut() {
                    let template_id = job_creator
                        .get_template_id_from_job(
                            self.inner
                                .get_valid_job(m.job_id)
                                .as_ref()
                                .unwrap()
                                .0
                                .job_id,
                        )
                        .ok_or(Error::NoTemplateForId)?;
                    let bitcoin_target = job_creator.last_target();
                    let prev_blockhash = self
                        .inner
                        .last_prev_hash_
                        .ok_or(Error::ShareDoNotMatchAnyJob)?;
                    let bits = self
                        .inner
                        .last_prev_hash
                        .as_ref()
                        .ok_or(Error::ShareDoNotMatchAnyJob)?
                        .0
                        .nbits;
                    self.inner.check_target(
                        Share::Standard((m, *g_id)),
                        bitcoin_target,
                        Some(template_id),
                        self.extended_channel_id,
                        merkle_path,
                        referenced_job.coinbase_tx_prefix.as_ref(),
                        referenced_job.coinbase_tx_suffix.as_ref(),
                        prev_blockhash,
                        bits,
                        None,
                    )
                } else {
                    let bitcoin_target = [0; 32];
                    let prev_blockhash = self
                        .inner
                        .last_prev_hash_
                        .ok_or(Error::ShareDoNotMatchAnyJob)?;
                    let bits = self
                        .inner
                        .last_prev_hash
                        .as_ref()
                        .ok_or(Error::ShareDoNotMatchAnyJob)?
                        .0
                        .nbits;
                    // if there is not job_creator is not proxy duty to check if target is below or
                    // above bitcoin target so we set bitcoin_target = 0.
                    self.inner.check_target(
                        Share::Standard((m, *g_id)),
                        bitcoin_target.into(),
                        None,
                        self.extended_channel_id,
                        merkle_path,
                        referenced_job.coinbase_tx_prefix.as_ref(),
                        referenced_job.coinbase_tx_suffix.as_ref(),
                        prev_blockhash,
                        bits,
                        None,
                    )
                }
            }
            None => {
                let err = SubmitSharesError {
                    channel_id: m.channel_id,
                    sequence_number: m.sequence_number,
                    error_code: SubmitSharesError::invalid_channel_error_code()
                        .to_string()
                        .try_into()
                        .unwrap(),
                };
                Ok(OnNewShare::SendErrorDownstream(err))
            }
        }
    }

    /// Calls [`ChannelFactory::on_new_prev_hash`]
    pub fn on_new_prev_hash(&mut self, m: SetNewPrevHash<'static>) -> Result<(), Error> {
        self.inner.on_new_prev_hash(StagedPhash {
            job_id: m.job_id,
            prev_hash: m.prev_hash.clone().into_static(),
            min_ntime: m.min_ntime,
            nbits: m.nbits,
        })
    }

    /// Calls [`ChannelFactory::on_new_extended_mining_job`]
    pub fn on_new_extended_mining_job(
        &mut self,
        m: NewExtendedMiningJob<'static>,
    ) -> Result<HashMap<u32, Mining<'static>, BuildNoHashHasher<u32>>, Error> {
        self.inner.on_new_extended_mining_job(m, None)
    }

    /// Set new target
    pub fn set_target(&mut self, new_target: &mut Target) {
        self.inner.kind.set_target(new_target);
    }

    /// Get last valid job version
    pub fn last_valid_job_version(&self) -> Option<u32> {
        self.inner
            .get_last_valid_job()
            .as_ref()
            .map(|j| j.0.version)
    }

    /// Return a mining job by its `job_id`.
    /// This can be `None` if we try to fetch a stale job because we clean up the valid jobs array
    /// upon receiving a new `PrevHash`
    pub fn job(&self, job_id: u32) -> Option<&(NewExtendedMiningJob<'static>, Vec<u32>)> {
        self.inner.get_valid_job(job_id)
    }

    /// Returns the full extranonce, extranonce1 (static for channel) + extranonce2 (miner nonce
    /// space)
    pub fn extranonce_from_downstream_extranonce(
        &self,
        ext: mining_sv2::Extranonce,
    ) -> Option<mining_sv2::Extranonce> {
        self.inner
            .extranonces
            .extranonce_from_downstream_extranonce(ext)
    }

    /// Returns the most recent prev hash
    pub fn last_prev_hash(&self) -> Option<binary_sv2::U256<'static>> {
        self.inner
            .last_prev_hash
            .as_ref()
            .map(|f| f.0.prev_hash.clone())
    }

    /// Get last min ntime
    pub fn last_min_ntime(&self) -> Option<u32> {
        self.inner.last_prev_hash.as_ref().map(|f| f.0.min_ntime)
    }

    /// Get last nbits
    pub fn last_nbits(&self) -> Option<u32> {
        self.inner.last_prev_hash.as_ref().map(|f| f.0.nbits)
    }

    /// Get extranonce_size
    pub fn extranonce_size(&self) -> usize {
        self.inner.extranonces.get_len()
    }

    /// Get extranonce_2 size
    pub fn channel_extranonce2_size(&self) -> usize {
        self.inner.extranonces.get_len() - self.inner.extranonces.get_range0_len()
    }

    // Only used when the proxy is using Job Declaration
    /// Updates pool outputs
    pub fn update_pool_outputs(&mut self, outs: Vec<TxOut>) {
        self.pool_coinbase_outputs = Some(outs);
    }

    /// Get this channel id
    pub fn get_this_channel_id(&self) -> u32 {
        self.extended_channel_id
    }

    /// Returns the extranonce1 len of the upstream. For a proxy, this would
    /// be the extranonce_prefix len
    pub fn get_upstream_extranonce1_len(&self) -> usize {
        self.inner.extranonces.get_range0_len()
    }

    /// Calls [`ChannelFactory::update_target_for_channel`]
    pub fn update_target_for_channel(
        &mut self,
        channel_id: u32,
        new_target: Target,
    ) -> Option<bool> {
        self.inner.update_target_for_channel(channel_id, new_target)
    }

    pub fn get_extranonce_len(&self) -> usize {
        self.inner.extranonces.get_len()
    }
}

/// Used by proxies for tracking upstream targets.
#[derive(Debug, Clone)]
pub enum ExtendedChannelKind {
    Proxy { upstream_target: Target },
    ProxyJd { upstream_target: Target },
    Pool,
}
impl ExtendedChannelKind {
    /// Set target
    pub fn set_target(&mut self, new_target: &mut Target) {
        match self {
            ExtendedChannelKind::Proxy { upstream_target }
            | ExtendedChannelKind::ProxyJd { upstream_target } => {
                std::mem::swap(upstream_target, new_target)
            }
            ExtendedChannelKind::Pool => warn!("Try to set upstream target for a pool"),
        }
    }
}
#[cfg(test)]
mod test {
    use super::*;
    use binary_sv2::{Seq0255, B064K, U256};
    use mining_sv2::OpenStandardMiningChannel;
    use stratum_common::bitcoin::{Amount, PublicKey, Target, TxOut, WPubkeyHash};

    const BLOCK_REWARD: u64 = 2_000_000_000;

    // Block 1296 data
    // 01000000
    // c1397d4a33adeeb3383803e9ac3db4b2c2c9d6737cbabc13a534d24600000000
    // 89687b66140ac9874656270e066ed7ef81d5133ada2d0133f09322a87b161738
    // 4eb87749
    // ffff001d
    // 07cacb0e
    const _PUB_K: &str = "04c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2";
    const _BLOCK_HASH: &str = "000000009a4aed3e8ba7a978c6b50fea886fb496d66e696090a91d527200b002";
    const VERSION: u32 = 1;
    // version 01000000
    // inputs 01
    // prev out 0000000000000000000000000000000000000000000000000000000000000000ffffffff
    // script len 07
    // script 04ffff001d0177
    // sequence ffffffff
    // n inputs 01
    // amunt 00f2052a01000000
    // out lne 43
    // push 41
    // pub k 04c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2
    // checksig ac
    // locktime 00000000
    const COINBASE: &str = "01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff0704ffff001d0177ffffffff0100f2052a01000000434104c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2ac00000000";
    const COINBASE_OUTPUT: &str = "4104c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2ac";
    const MERKLE_PATH: &str = "59bf8acbc9d60dfae841abecc3882b4181f2bdd8ac6c1d94001165ab3aef50b0";
    const NONCE: &str = "07cacb0e";
    const NTIME: &str = "4eb87749";

    // Prev  block data (1295)
    //01000000
    //cf578a234f330c287354e24234ff6b86d6ab9e4ddd3e5ba71a6bcbf600000000
    //72d12b99bdb63762bedc5db30bcffbd7903721bc736dd683de37b1a3632f9000
    //time: 2e8c7749 -> 49778c2e -> 1232571438
    //nbits: ffff001d -> 4294901789
    //29444816
    const PREV_HASH: &str = "0000000046d234a513bcba7c73d6c9c2b2b43dace9033838b3eead334a7d39c1";
    const PREV_HEADER_TIMESTAMP: u32 = 1232571438;
    const PREV_HEADER_NBITS: u32 = 486604799;

    fn _get_pub_key_hash() -> WPubkeyHash {
        let into_bin = decode_hex(_PUB_K).unwrap();
        let pk = PublicKey::from_slice(&into_bin[..]);
        let hash = pk.unwrap().pubkey_hash();
        WPubkeyHash::from_raw_hash(hash.to_raw_hash())
    }

    fn get_coinbase() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        let parsed = decode_hex(COINBASE).unwrap();
        // Coinbase prefix in Sv2 is the bip34 block height in this tx there is no prefix
        let prefix = parsed[42..42].to_vec();
        let extranonce = parsed[42..49].to_vec();
        let suffix = parsed[49..].to_vec();
        (prefix, extranonce, suffix)
    }

    fn get_coinbase_outputs() -> B064K<'static> {
        decode_hex(COINBASE_OUTPUT).unwrap().try_into().unwrap()
    }

    fn get_custom_job_outputs() -> B064K<'static> {
        let out = TxOut {
            value: Amount::from_sat(BLOCK_REWARD),
            script_pubkey: decode_hex(COINBASE_OUTPUT).unwrap().into(),
        };
        stratum_common::bitcoin::consensus::serialize(&out)
            .try_into()
            .unwrap()
    }

    fn get_merkle_path() -> Seq0255<'static, U256<'static>> {
        let mut m_path = decode_hex(MERKLE_PATH).unwrap();
        m_path.reverse();
        let path: U256 = m_path.try_into().unwrap();
        vec![path].try_into().unwrap()
    }

    fn nbit_to_target(nbit: u32) -> U256<'static> {
        let mut target = Target::from_compact(CompactTarget::from_consensus(nbit))
            .to_be_bytes()
            .to_vec();
        target.reverse();
        target.try_into().unwrap()
    }

    fn decode_hex(s: &str) -> Result<Vec<u8>, std::num::ParseIntError> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
            .collect()
    }

    fn pool_channel_factory(
        additional_coinbase_script_data: Vec<u8>,
        extranonces: ExtendedExtranonce,
    ) -> PoolChannelFactory {
        let out = TxOut {
            value: Amount::from_sat(BLOCK_REWARD),
            script_pubkey: decode_hex(COINBASE_OUTPUT).unwrap().into(),
        };
        let extranonce_len = extranonces.get_len() as u8;
        PoolChannelFactory::new(
            Arc::new(Mutex::new(GroupId::new())),
            extranonces,
            JobsCreators::new(extranonce_len),
            1.0,
            ExtendedChannelKind::Pool,
            vec![out],
            additional_coinbase_script_data,
        )
        .unwrap()
    }

    fn new_template(template_id: u64) -> NewTemplate<'static> {
        let (prefix, _, _) = get_coinbase();

        NewTemplate {
            template_id,
            future_template: true,
            version: VERSION,
            coinbase_tx_version: 1,
            coinbase_prefix: prefix.try_into().unwrap(),
            coinbase_tx_input_sequence: u32::MAX,
            coinbase_tx_value_remaining: 5_000_000_000,
            coinbase_tx_outputs_count: 0,
            coinbase_tx_outputs: get_coinbase_outputs(),
            coinbase_tx_locktime: 0,
            merkle_path: get_merkle_path(),
        }
    }

    fn new_prev_hash(template_id: u64) -> SetNewPrevHashFromTp<'static> {
        let mut p_hash = decode_hex(PREV_HASH).unwrap();
        p_hash.reverse();

        SetNewPrevHashFromTp {
            template_id,
            prev_hash: p_hash.try_into().unwrap(),
            header_timestamp: PREV_HEADER_TIMESTAMP,
            n_bits: PREV_HEADER_NBITS,
            target: nbit_to_target(PREV_HEADER_NBITS),
        }
    }

    fn custom_job_with_prefix(
        channel_id: u32,
        coinbase_prefix: Vec<u8>,
    ) -> SetCustomMiningJob<'static> {
        let mut prev_hash = decode_hex(PREV_HASH).unwrap();
        prev_hash.reverse();

        SetCustomMiningJob {
            channel_id,
            request_id: 1,
            token: Vec::<u8>::new().try_into().unwrap(),
            version: VERSION,
            prev_hash: prev_hash.try_into().unwrap(),
            min_ntime: PREV_HEADER_TIMESTAMP,
            nbits: PREV_HEADER_NBITS,
            coinbase_tx_version: 2,
            coinbase_prefix: coinbase_prefix.try_into().unwrap(),
            coinbase_tx_input_n_sequence: u32::MAX,
            coinbase_tx_value_remaining: BLOCK_REWARD,
            coinbase_tx_outputs: get_custom_job_outputs(),
            coinbase_tx_locktime: 0,
            merkle_path: get_merkle_path(),
            extranonce_size: 8,
        }
    }

    fn submit_extended_share(channel_id: u32) -> SubmitSharesExtended<'static> {
        SubmitSharesExtended {
            channel_id,
            sequence_number: 1,
            job_id: 1,
            nonce: 0,
            ntime: PREV_HEADER_TIMESTAMP,
            version: VERSION,
            extranonce: vec![0; 8].try_into().unwrap(),
        }
    }

    fn channel_sequence(value: u8) -> [u8; 24] {
        let mut sequence = [0; 24];
        sequence[23] = value;
        sequence
    }

    fn channel_output_sequence(job: &NewExtendedMiningJob<'static>) -> [u8; 24] {
        let (outputs, _): (Vec<TxOut>, usize) =
            deserialize_partial(&job.coinbase_tx_suffix.as_ref()[4..]).unwrap();
        let sequences: Vec<_> = outputs
            .iter()
            .filter(|output| {
                output
                    .script_pubkey
                    .as_bytes()
                    .starts_with(b"\x6a\x1dCHSEQ")
            })
            .map(|output| {
                assert_eq!(output.value, Amount::ZERO);
                output.script_pubkey.as_bytes()[7..].try_into().unwrap()
            })
            .collect();
        assert_eq!(sequences.len(), 1);
        sequences[0]
    }

    fn open_output_channel(factory: &mut PoolChannelFactory) -> u32 {
        match &factory
            .new_extended_channel(1, 100_000_000_000_000.0, 8)
            .unwrap()[0]
        {
            Mining::OpenExtendedMiningChannelSuccess(success) => success.channel_id,
            _ => panic!("expected successful channel open"),
        }
    }

    #[test]
    fn registered_user_identifiers_handle_conflicts_close_and_restoration() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let user_identifier = b"user\x00\xff".as_slice();
        assert_eq!(factory.channel_id_for_user(user_identifier), None);
        assert!(matches!(
            factory.register_channel_user(u32::MAX, user_identifier),
            Err(Error::NotFoundChannelId)
        ));
        assert_eq!(factory.channel_id_for_user(user_identifier), None);

        let first = open_output_channel(&mut factory);
        let second = open_output_channel(&mut factory);
        factory
            .register_channel_user(first, user_identifier)
            .unwrap();
        factory
            .register_channel_user(first, user_identifier)
            .unwrap();
        assert_eq!(factory.channel_id_for_user(user_identifier), Some(first));
        assert!(matches!(
            factory.register_channel_user(second, user_identifier),
            Err(Error::ChannelIdAlreadyInUse(id)) if id == first
        ));
        assert_eq!(factory.channel_id_for_user(user_identifier), Some(first));
        factory.register_channel_user(second, b"other").unwrap();
        let prefix = factory.get_extranonce_prefix(first).unwrap();
        factory.close_channel(first);
        assert_eq!(factory.channel_id_for_user(user_identifier), None);
        assert_eq!(factory.channel_id_for_user(b"other"), Some(second));

        factory
            .replicate_pool_extended_channel(
                3,
                [255; 32].into(),
                prefix.try_into().unwrap(),
                99,
                8,
                Vec::new(),
            )
            .unwrap();
        factory.register_channel_user(99, user_identifier).unwrap();
        factory.close_channel(first);
        assert_eq!(factory.channel_id_for_user(user_identifier), Some(99));
        factory.close_channel(99);
        assert_eq!(factory.channel_id_for_user(user_identifier), None);
    }

    #[test]
    fn channel_coinbase_counter_carries_without_changing_factory_prefix() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        let (base_job, _, _) = factory
            .on_new_template_for_extended_fanout(&mut new_template(10))
            .unwrap();
        for index in (16..24).rev() {
            let mut previous = [0; 24];
            previous[..16].fill(0x42);
            previous[index + 1..].fill(u8::MAX);
            factory.last_channel_coinbase_sequence = Some(previous);
            let mut expected = [0; 24];
            expected[..16].fill(0x42);
            expected[index] = 1;

            let channel_id = open_output_channel(&mut factory);
            let output = factory.channel_coinbase_output(channel_id).unwrap();
            assert_eq!(output.0, expected);
            assert_eq!(factory.last_channel_coinbase_sequence, Some(expected));
            let mut job = base_job.clone();
            output.apply(&mut job).unwrap();
            assert_eq!(channel_output_sequence(&job), expected);
        }
    }

    #[test]
    fn channel_coinbase_outputs_share_factory_prefix_and_reset_counter_on_restart() {
        let mut previous =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        let initial = previous.last_channel_coinbase_sequence.unwrap();
        assert_eq!(&initial[16..], &[0; 8]);
        previous = previous.with_channel_coinbase_outputs();
        assert_eq!(previous.last_channel_coinbase_sequence, Some(initial));
        let channel_id = open_output_channel(&mut previous);
        let prefix = previous.get_extranonce_prefix(channel_id).unwrap();
        let old_output = previous.channel_coinbase_output(channel_id).unwrap();
        assert_eq!(&old_output.0[..16], &initial[..16]);
        assert_eq!(&old_output.0[16..], &1_u64.to_be_bytes());
        for counter in 2_u64..=3 {
            let id = open_output_channel(&mut previous);
            let output = previous.channel_coinbase_output(id).unwrap();
            assert_eq!(&output.0[..16], &initial[..16]);
            assert_eq!(&output.0[16..], &counter.to_be_bytes());
            previous.close_channel(id);
        }
        drop(previous);

        let mut restarted =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        restarted
            .replicate_pool_extended_channel(
                1,
                [255; 32].into(),
                prefix.clone().try_into().unwrap(),
                channel_id,
                8,
                Vec::new(),
            )
            .unwrap();
        assert_eq!(restarted.get_extranonce_prefix(channel_id).unwrap(), prefix);
        let restored_output = restarted.channel_coinbase_output(channel_id).unwrap();
        assert_ne!(&restored_output.0[..16], &old_output.0[..16]);
        assert_eq!(&restored_output.0[16..], &1_u64.to_be_bytes());
    }

    #[test]
    fn close_group_releases_empty_reservations_alongside_extended_channels() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let extended_id = open_output_channel(&mut factory);
        for _ in 0..100 {
            let group_id = factory.new_group_id();
            factory.close_group(group_id);
            factory.close_group(group_id);
            assert_eq!(factory.inner.channel_to_group_id.len(), 1);
            assert_eq!(
                factory.inner.channel_to_group_id.get(&extended_id),
                Some(&0)
            );
            assert!(factory.inner.extended_channels.contains_key(&extended_id));
        }
        factory.close_channel(extended_id);
        assert!(factory.inner.channel_to_group_id.is_empty());
    }

    #[test]
    fn close_group_closes_members_and_clears_job_tracking() {
        let mut factory =
            pool_channel_factory(vec![42], ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        let group_id = factory.new_group_id();
        let other_group = factory.new_group_id();
        let channel_ids: Vec<_> = [group_id, group_id, other_group]
            .iter()
            .map(
                |group| match &factory.add_standard_channel(1, 1.0, false, *group).unwrap()[0] {
                    Mining::OpenStandardMiningChannelSuccess(success) => success.channel_id,
                    _ => panic!("expected standard channel open"),
                },
            )
            .collect();
        let hom_id = factory.new_standard_id_for_hom();
        factory.add_standard_channel(2, 1.0, true, hom_id).unwrap();
        let extended_id = open_output_channel(&mut factory);
        let mut custom = custom_job_with_prefix(extended_id, vec![0]);
        let mut outputs = custom.coinbase_tx_outputs.to_vec();
        outputs.extend(serialize(
            &factory
                .channel_coinbase_output(extended_id)
                .unwrap()
                .tx_out(),
        ));
        custom.coinbase_tx_outputs = outputs.try_into().unwrap();
        factory.try_on_new_set_custom_mining_job(custom).unwrap();
        factory.on_new_template(&mut new_template(10)).unwrap();
        factory
            .on_new_prev_hash_from_tp(&new_prev_hash(10))
            .unwrap();
        factory.on_new_template(&mut new_template(11)).unwrap();

        factory.close_group(group_id);
        factory.close_group(group_id);

        for channel_id in &channel_ids[..2] {
            assert!(!factory.inner.channel_to_group_id.contains_key(channel_id));
            assert!(!factory
                .channel_to_additional_coinbase_script_data
                .contains_key(channel_id));
        }
        assert!(!factory.inner.channel_to_group_id.contains_key(&group_id));
        assert_eq!(
            factory
                .inner
                .standard_channels_for_non_hom_downstreams
                .len(),
            1
        );
        assert_eq!(
            factory.inner.channel_to_group_id.get(&other_group),
            Some(&other_group)
        );
        assert_eq!(
            factory.inner.channel_to_group_id.get(&channel_ids[2]),
            Some(&other_group)
        );
        assert!(factory
            .channel_to_additional_coinbase_script_data
            .contains_key(&channel_ids[2]));
        assert!(factory
            .inner
            .standard_channels_for_hom_downstreams
            .contains_key(&hom_id));
        assert!(factory.inner.extended_channels.contains_key(&extended_id));
        assert!(factory.channel_coinbase_output(extended_id).is_some());
        assert!(factory.negotiated_jobs.contains_key(&extended_id));
        for (_, groups) in factory
            .inner
            .future_jobs
            .iter()
            .chain(factory.inner.last_valid_jobs.iter().flatten())
        {
            assert!(!groups.contains(&group_id));
            assert!(groups.contains(&other_group));
        }
        let groups = &factory.inner.last_prev_hash.as_ref().unwrap().1;
        assert!(!groups.contains(&group_id));
        assert!(groups.contains(&other_group));

        let messages = factory.on_new_template(&mut new_template(12)).unwrap();
        assert!(!messages.contains_key(&group_id));
        assert!(messages.contains_key(&other_group));
        assert!(messages.contains_key(&hom_id));
        assert!(messages.contains_key(&extended_id));
        factory
            .replicate_pool_extended_channel(
                3,
                [255; 32].into(),
                vec![1; 8].try_into().unwrap(),
                group_id,
                8,
                vec![42],
            )
            .unwrap();
        factory.close_group(group_id);
        assert!(factory.inner.extended_channels.contains_key(&group_id));
        assert_eq!(factory.inner.channel_to_group_id.get(&group_id), Some(&0));
    }

    #[test]
    fn close_group_ignores_channel_ids_and_unknown_groups() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let group_id = factory.new_group_id();
        let standard_id = match &factory
            .add_standard_channel(1, 1.0, false, group_id)
            .unwrap()[0]
        {
            Mining::OpenStandardMiningChannelSuccess(success) => success.channel_id,
            _ => panic!("expected standard channel open"),
        };
        let extended_id = open_output_channel(&mut factory);
        for id in [standard_id, extended_id, u32::MAX] {
            factory.close_group(id);
        }
        assert_eq!(factory.inner.channel_to_group_id.len(), 3);
        assert_eq!(
            factory.inner.channel_to_group_id.get(&standard_id),
            Some(&group_id)
        );
        assert!(factory
            .channel_to_additional_coinbase_script_data
            .contains_key(&standard_id));
        assert!(factory
            .channel_to_additional_coinbase_script_data
            .contains_key(&extended_id));
        assert!(factory.inner.extended_channels.contains_key(&extended_id));
        assert_eq!(
            factory
                .inner
                .standard_channels_for_non_hom_downstreams
                .len(),
            1
        );
    }

    #[test]
    fn close_channel_removes_group_only_after_its_last_member() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let group_id = factory.new_group_id();
        let other_group = factory.new_group_id();
        let channel_ids: Vec<_> = [group_id, group_id, other_group]
            .iter()
            .map(
                |group| match &factory.add_standard_channel(1, 1.0, false, *group).unwrap()[0] {
                    Mining::OpenStandardMiningChannelSuccess(success) => success.channel_id,
                    _ => panic!("expected standard channel open"),
                },
            )
            .collect();
        factory.on_new_template(&mut new_template(10)).unwrap();
        factory
            .on_new_prev_hash_from_tp(&new_prev_hash(10))
            .unwrap();
        factory.on_new_template(&mut new_template(11)).unwrap();

        factory.close_channel(channel_ids[0]);
        factory.close_channel(channel_ids[0]);
        assert!(!factory
            .inner
            .channel_to_group_id
            .contains_key(&channel_ids[0]));
        assert_eq!(
            factory
                .inner
                .standard_channels_for_non_hom_downstreams
                .len(),
            2
        );
        assert_eq!(
            factory.inner.channel_to_group_id.get(&group_id),
            Some(&group_id)
        );
        for (_, groups) in factory
            .inner
            .future_jobs
            .iter()
            .chain(factory.inner.last_valid_jobs.iter().flatten())
        {
            assert!(groups.contains(&group_id));
        }
        assert!(factory
            .inner
            .last_prev_hash
            .as_ref()
            .unwrap()
            .1
            .contains(&group_id));
        assert!(matches!(
            factory.replicate_pool_extended_channel(
                1,
                [255; 32].into(),
                vec![1; 8].try_into().unwrap(),
                group_id,
                8,
                Vec::new(),
            ),
            Err(Error::ChannelIdAlreadyInUse(id)) if id == group_id
        ));

        factory.close_channel(channel_ids[1]);
        assert!(!factory.inner.channel_to_group_id.contains_key(&group_id));
        assert!(!factory
            .inner
            .channel_to_group_id
            .contains_key(&channel_ids[1]));
        assert_eq!(
            factory
                .inner
                .standard_channels_for_non_hom_downstreams
                .len(),
            1
        );
        assert_eq!(
            factory.inner.channel_to_group_id.get(&channel_ids[2]),
            Some(&other_group)
        );
        assert_eq!(
            factory.inner.channel_to_group_id.get(&other_group),
            Some(&other_group)
        );
        for (_, groups) in factory
            .inner
            .future_jobs
            .iter()
            .chain(factory.inner.last_valid_jobs.iter().flatten())
        {
            assert!(!groups.contains(&group_id));
            assert!(groups.contains(&other_group));
        }
        assert!(!factory
            .inner
            .last_prev_hash
            .as_ref()
            .unwrap()
            .1
            .contains(&group_id));
        assert!(factory
            .inner
            .last_prev_hash
            .as_ref()
            .unwrap()
            .1
            .contains(&other_group));
        factory
            .replicate_pool_extended_channel(
                1,
                [255; 32].into(),
                vec![1; 8].try_into().unwrap(),
                group_id,
                8,
                Vec::new(),
            )
            .unwrap();
        assert!(factory.new_group_id() > channel_ids[2]);
    }

    #[test]
    fn close_channel_preserves_shared_group_zero() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let channel_id = match &factory.add_standard_channel(1, 1.0, false, 0).unwrap()[0] {
            Mining::OpenStandardMiningChannelSuccess(success) => success.channel_id,
            _ => panic!("expected standard channel open"),
        };
        let hom_id = factory.new_standard_id_for_hom();
        factory.add_standard_channel(2, 1.0, true, hom_id).unwrap();
        let extended_id = open_output_channel(&mut factory);
        factory.close_group(0);
        assert_eq!(factory.inner.channel_to_group_id.len(), 4);
        assert_eq!(
            factory
                .inner
                .standard_channels_for_non_hom_downstreams
                .len(),
            1
        );
        assert!(factory
            .channel_to_additional_coinbase_script_data
            .contains_key(&channel_id));
        factory.close_channel(channel_id);
        assert!(!factory.inner.channel_to_group_id.contains_key(&channel_id));
        assert_eq!(factory.inner.channel_to_group_id.get(&0), Some(&0));
        assert!(factory
            .inner
            .standard_channels_for_hom_downstreams
            .contains_key(&hom_id));
        assert!(factory.inner.extended_channels.contains_key(&extended_id));
        factory.close_channel(hom_id);
        factory.close_channel(extended_id);
        assert_eq!(factory.inner.channel_to_group_id.len(), 1);
        assert_eq!(factory.inner.channel_to_group_id.get(&0), Some(&0));
    }

    #[test]
    fn close_channel_does_not_retain_groups_after_repeated_opens_and_closes() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let mut last_id = 0;
        for _ in 0..2000 {
            let group_id = factory.new_group_id();
            assert!(group_id > last_id);
            let channel_id = match &factory
                .add_standard_channel(1, 1.0, false, group_id)
                .unwrap()[0]
            {
                Mining::OpenStandardMiningChannelSuccess(success) => success.channel_id,
                _ => panic!("expected standard channel open"),
            };
            assert!(channel_id > group_id);
            factory.close_channel(channel_id);
            assert!(factory.inner.channel_to_group_id.is_empty());
            assert!(factory
                .inner
                .standard_channels_for_non_hom_downstreams
                .is_empty());
            assert!(factory
                .channel_to_additional_coinbase_script_data
                .is_empty());
            last_id = channel_id;
        }
        assert!(factory.new_group_id() > last_id);
    }

    #[test]
    fn channel_coinbase_outputs_leave_grouped_standard_jobs_unmarked() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        factory.last_channel_coinbase_sequence = Some([0; 24]);
        let group_id = factory.new_group_id();
        let channel_id = open_output_channel(&mut factory);
        let opened = factory
            .add_standard_channel(2, 1.0, false, group_id)
            .unwrap();
        let standard_id = match &opened[0] {
            Mining::OpenStandardMiningChannelSuccess(success) => success.channel_id,
            _ => panic!("expected standard channel open"),
        };

        let messages = factory.on_new_template(&mut new_template(10)).unwrap();
        assert_eq!(messages.len(), 2);
        let standard_job = match messages.get(&group_id).unwrap() {
            Mining::NewExtendedMiningJob(job) => job,
            _ => panic!("expected grouped standard job"),
        };
        assert_eq!(
            standard_job.coinbase_tx_suffix,
            factory.inner.future_jobs[0].0.coinbase_tx_suffix
        );
        match messages.get(&channel_id).unwrap() {
            Mining::NewExtendedMiningJob(job) => {
                assert_eq!(channel_output_sequence(job), channel_sequence(1))
            }
            _ => panic!("expected extended channel job"),
        }
        let mut prev_hash = new_prev_hash(10);
        prev_hash.target = [255; 32].into();
        factory.on_new_prev_hash_from_tp(&prev_hash).unwrap();
        assert!(matches!(
            factory.on_submit_shares_standard(SubmitSharesStandard {
                channel_id: standard_id,
                sequence_number: 1,
                job_id: standard_job.job_id,
                nonce: 0,
                ntime: PREV_HEADER_TIMESTAMP,
                version: VERSION,
            }),
            Ok(OnNewShare::ShareMeetBitcoinTarget(_))
        ));
    }

    #[test]
    fn channel_coinbase_outputs_cover_opens_restores_templates_and_replays() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        factory.last_channel_coinbase_sequence = Some([0; 24]);
        let first = open_output_channel(&mut factory);
        assert!(matches!(
            factory.new_extended_channel(2, 1.0, 9).unwrap()[0],
            Mining::OpenMiningChannelError(_)
        ));
        let second = open_output_channel(&mut factory);
        let messages = factory.on_new_template(&mut new_template(10)).unwrap();
        for (channel_id, sequence) in [(first, 1), (second, 2)] {
            match messages.get(&channel_id).unwrap() {
                Mining::NewExtendedMiningJob(job) => {
                    assert_eq!(channel_output_sequence(job), channel_sequence(sequence))
                }
                _ => panic!(),
            }
        }
        factory
            .on_new_prev_hash_from_tp(&new_prev_hash(10))
            .unwrap();
        factory.on_new_template(&mut new_template(11)).unwrap();
        assert_eq!(
            channel_output_sequence(&factory.current_extended_job_for_channel(second).unwrap()),
            channel_sequence(2)
        );

        let prefix = factory.get_extranonce_prefix(first).unwrap();
        let restore = |factory: &mut PoolChannelFactory| {
            factory.replicate_pool_extended_channel(
                3,
                [255; 32].into(),
                prefix.clone().try_into().unwrap(),
                99,
                8,
                Vec::new(),
            )
        };
        let restored = restore(&mut factory).unwrap();
        assert_eq!(factory.get_extranonce_prefix(99), Some(prefix));
        assert_eq!(
            factory.channel_coinbase_output(first),
            Some(ChannelCoinbaseOutput(channel_sequence(1)))
        );
        let cached_jobs: Vec<_> = restored
            .iter()
            .filter_map(|message| match message {
                Mining::NewExtendedMiningJob(job) => Some(job),
                _ => None,
            })
            .collect();
        assert_eq!(cached_jobs.len(), 2); // Current and future jobs.
        for job in cached_jobs {
            assert_eq!(channel_output_sequence(job), channel_sequence(3));
        }
        factory.close_channel(first);
        assert!(factory.channel_coinbase_output(first).is_none());
        let fourth = open_output_channel(&mut factory);
        assert_eq!(
            factory.channel_coinbase_output(fourth),
            Some(ChannelCoinbaseOutput(channel_sequence(4)))
        );

        let (base, channel_ids, _) = factory
            .on_new_template_for_extended_fanout(&mut new_template(12))
            .unwrap();
        for channel_id in channel_ids {
            let mut job = base.clone();
            let output = factory.channel_coinbase_output(channel_id).unwrap();
            output.apply(&mut job).unwrap();
            output.apply(&mut job).unwrap();
            assert_eq!(channel_output_sequence(&job), output.0);
        }
        let mut exhausted = factory.last_channel_coinbase_sequence.unwrap();
        exhausted[16..].fill(u8::MAX);
        factory.last_channel_coinbase_sequence = Some(exhausted);
        let channel_count = factory.inner.extended_channels.len();
        assert!(matches!(
            factory.new_extended_channel(4, 1.0, 8),
            Err(Error::ChannelCoinbaseSequenceExhausted)
        ));
        assert!(matches!(
            factory.replicate_pool_extended_channel(
                5,
                [255; 32].into(),
                vec![0xfe; 8].try_into().unwrap(),
                100,
                8,
                Vec::new(),
            ),
            Err(Error::ChannelCoinbaseSequenceExhausted)
        ));
        assert_eq!(factory.inner.extended_channels.len(), channel_count);
        assert_eq!(factory.last_channel_coinbase_sequence, Some(exhausted));
    }

    #[test]
    fn channel_coinbase_output_failed_open_does_not_consume_sequence() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        factory.last_channel_coinbase_sequence = Some([0; 24]);
        // The cached base fits B064K, but adding the channel output would overflow it.
        factory.pool_coinbase_outputs[0].script_pubkey = ScriptBuf::from_bytes(vec![0; 65_500]);
        factory.on_new_template(&mut new_template(10)).unwrap();
        assert!(matches!(
            factory.new_extended_channel(1, 1.0, 8),
            Err(Error::BinarySv2Error(_))
        ));
        assert!(factory.inner.extended_channels.is_empty());
        assert!(factory
            .channel_to_additional_coinbase_script_data
            .is_empty());
        assert!(factory.channel_coinbase_outputs.is_empty());
        assert_eq!(factory.last_channel_coinbase_sequence, Some([0; 24]));
        factory.inner.future_jobs.clear();
        let channel_id = open_output_channel(&mut factory);
        assert_eq!(
            factory.channel_coinbase_output(channel_id),
            Some(ChannelCoinbaseOutput(channel_sequence(1)))
        );
    }

    #[test]
    fn channel_coinbase_output_preserves_outputs_witness_and_compact_size() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let mut template = new_template(10);
        template.coinbase_tx_version = 2;
        template.coinbase_prefix = vec![3, 1, 0, 0, 0].try_into().unwrap();
        let (mut job, _, _) = factory
            .on_new_template_for_extended_fanout(&mut template)
            .unwrap();
        let coinbase = [
            job.coinbase_tx_prefix.as_ref(),
            &[0; 16],
            job.coinbase_tx_suffix.as_ref(),
        ]
        .concat();
        let mut tx: stratum_common::bitcoin::Transaction =
            stratum_common::bitcoin::consensus::deserialize(&coinbase).unwrap();
        assert!(!tx.input[0].witness.is_empty());
        let unrelated = TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::new_op_return(b"other"),
        };
        let difficulty = TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::new_op_return(b"DIFF32abcd"),
        };
        tx.output.resize(250, tx.output[0].clone());
        tx.output.extend([unrelated, difficulty]);
        let original_outputs = tx.output.clone();
        let split = job.coinbase_tx_prefix.len() + 16;
        let encoded = serialize(&tx);
        job.coinbase_tx_suffix = encoded[split..].to_vec().try_into().unwrap();
        let original_prefix = job.coinbase_tx_prefix.clone();
        ChannelCoinbaseOutput(channel_sequence(1))
            .apply(&mut job)
            .unwrap();
        assert_eq!(&job.coinbase_tx_suffix.as_ref()[4..7], &[0xfd, 0xfd, 0]);
        assert_eq!(
            job.coinbase_tx_suffix.len() - (encoded.len() - split),
            ChannelCoinbaseOutput::additional_coinbase_weight() / 4
        );
        ChannelCoinbaseOutput(channel_sequence(1))
            .apply(&mut job)
            .unwrap();
        assert_eq!(job.coinbase_tx_prefix, original_prefix);
        let coinbase = [
            job.coinbase_tx_prefix.as_ref(),
            &[0; 16],
            job.coinbase_tx_suffix.as_ref(),
        ]
        .concat();
        let composed: stratum_common::bitcoin::Transaction =
            stratum_common::bitcoin::consensus::deserialize(&coinbase).unwrap();
        assert_eq!(composed.input, tx.input);
        assert_eq!(composed.lock_time, tx.lock_time);
        assert_eq!(composed.version, tx.version);
        assert_eq!(composed.output[..252], original_outputs);
        assert_eq!(composed.output.len(), 253);
        assert_eq!(channel_output_sequence(&job), channel_sequence(1));
    }

    #[test]
    fn colliding_channels_validate_distinct_work_with_and_without_per_job_output() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        factory.last_channel_coinbase_sequence = Some([0; 24]);
        let channel_id = open_output_channel(&mut factory);
        let prefix = factory.get_extranonce_prefix(channel_id).unwrap();
        let other_channel = 99;
        factory
            .replicate_pool_extended_channel(
                2,
                [255; 32].into(),
                prefix.clone().try_into().unwrap(),
                other_channel,
                8,
                Vec::new(),
            )
            .unwrap();
        assert_eq!(factory.get_extranonce_prefix(other_channel), Some(prefix));
        let job = match factory
            .on_new_template(&mut new_template(10))
            .unwrap()
            .remove(&channel_id)
            .unwrap()
        {
            Mining::NewExtendedMiningJob(job) => job,
            _ => panic!(),
        };
        assert_eq!(channel_output_sequence(&job), channel_sequence(1));
        assert_eq!(
            factory.channel_coinbase_output(other_channel),
            Some(ChannelCoinbaseOutput(channel_sequence(2)))
        );
        let mut prevhash = new_prev_hash(10);
        let mut target_bytes = [255; 32];
        target_bytes[31] = 127;
        prevhash.target = target_bytes.into();
        let target: mining_sv2::Target = target_bytes.into();
        factory.on_new_prev_hash_from_tp(&prevhash).unwrap();
        for id in [channel_id, other_channel] {
            factory.inner.extended_channels.get_mut(&id).unwrap().target = [0; 32].into();
        }
        let extranonce = [
            factory.get_extranonce_prefix(channel_id).unwrap(),
            vec![0; 8],
        ]
        .concat();
        let share_hash = |job: &NewExtendedMiningJob<'static>, nonce| -> mining_sv2::Target {
            let root: [u8; 32] = crate::utils::merkle_root_from_path(
                job.coinbase_tx_prefix.as_ref(),
                job.coinbase_tx_suffix.as_ref(),
                &extranonce,
                &job.merkle_path.to_vec(),
                &[],
            )
            .unwrap()
            .try_into()
            .unwrap();
            let header = Header {
                version: Version::from_consensus(VERSION as i32),
                prev_blockhash: crate::utils::u256_to_block_hash(prevhash.prev_hash.clone()),
                merkle_root: (*Hash::from_bytes_ref(&root)).into(),
                time: PREV_HEADER_TIMESTAMP,
                bits: CompactTarget::from_consensus(PREV_HEADER_NBITS),
                nonce,
            };
            let bytes: [u8; 32] = *header.block_hash().to_raw_hash().as_ref();
            bytes.into()
        };
        for local_output in [false, true] {
            let mut job = job.clone();
            if local_output {
                let suffix = job.coinbase_tx_suffix.as_ref();
                let (mut outputs, consumed): (Vec<TxOut>, usize) =
                    deserialize_partial(&suffix[4..]).unwrap();
                let output = TxOut {
                    value: Amount::ZERO,
                    script_pubkey: ScriptBuf::new_op_return(b"DIFF32abcd"),
                };
                outputs.push(output.clone());
                job.coinbase_tx_suffix =
                    [&suffix[..4], &serialize(&outputs), &suffix[4 + consumed..]]
                        .concat()
                        .try_into()
                        .unwrap();
                factory.register_extended_job_coinbase_output(channel_id, job.job_id, output);
                factory.register_extended_job_coinbase_output(
                    other_channel,
                    job.job_id,
                    outputs.last().unwrap().clone(),
                );
            }
            assert_eq!(channel_output_sequence(&job), channel_sequence(1));
            // Use this channel's correct scriptSig and change ONLY the channel-output payload.
            let mut wrong_job = job.clone();
            let mut wrong_suffix = wrong_job.coinbase_tx_suffix.to_vec();
            let tag = wrong_suffix
                .windows(7)
                .position(|bytes| bytes == b"\x6a\x1dCHSEQ")
                .unwrap();
            wrong_suffix[tag + 7..tag + 31].copy_from_slice(&channel_sequence(2));
            wrong_job.coinbase_tx_suffix = wrong_suffix.try_into().unwrap();
            let wrong_nonce = (0..1000)
                .find(|nonce| {
                    share_hash(&wrong_job, *nonce) <= target && share_hash(&job, *nonce) > target
                })
                .unwrap();
            let mut share = submit_extended_share(channel_id);
            share.job_id = job.job_id;
            share.nonce = wrong_nonce;
            assert!(matches!(
                factory.on_submit_shares_extended(share.clone()).unwrap(),
                OnNewShare::SendErrorDownstream(_)
            ));
            share.channel_id = other_channel;
            match factory.on_submit_shares_extended(share.clone()).unwrap() {
                OnNewShare::ShareMeetBitcoinTarget((_, _, coinbase, _)) => assert_eq!(
                    coinbase,
                    [
                        wrong_job.coinbase_tx_prefix.as_ref(),
                        &extranonce,
                        wrong_job.coinbase_tx_suffix.as_ref()
                    ]
                    .concat(),
                ),
                result => panic!("expected colliding channel's coinbase, got {:?}", result),
            }
            share.channel_id = channel_id;
            share.nonce = (0..1000)
                .find(|nonce| share_hash(&job, *nonce) <= target)
                .unwrap();
            match factory.on_submit_shares_extended(share).unwrap() {
                OnNewShare::ShareMeetBitcoinTarget((_, _, coinbase, _)) => assert_eq!(
                    coinbase,
                    [
                        job.coinbase_tx_prefix.as_ref(),
                        &extranonce,
                        job.coinbase_tx_suffix.as_ref()
                    ]
                    .concat(),
                ),
                result => panic!("expected exact coinbase, got {:?}", result),
            }
        }
    }

    #[test]
    fn replicate_pool_extended_channel_registers_prefix_and_additional_data() {
        let additional_coinbase_script_data = vec![1, 2, 3, 4, 5, 6];
        let extranonces = ExtendedExtranonce::new(0..0, 0..10, 10..16);
        let mut channel =
            pool_channel_factory(additional_coinbase_script_data.clone(), extranonces);
        let group_id = channel.new_group_id();
        let extranonce_prefix = vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let target = vec![255; 32].try_into().unwrap();
        let channel_id = 42;

        let result = channel
            .replicate_pool_extended_channel(
                7,
                target,
                extranonce_prefix.clone().try_into().unwrap(),
                channel_id,
                6,
                additional_coinbase_script_data.clone(),
            )
            .unwrap();

        let success = match &result[0] {
            Mining::OpenExtendedMiningChannelSuccess(success) => success,
            _ => panic!(),
        };
        let mut downstream_extranonce_prefix = additional_coinbase_script_data.clone();
        downstream_extranonce_prefix.extend(extranonce_prefix.clone());

        assert_eq!(success.request_id, 7);
        assert_eq!(success.channel_id, channel_id);
        assert_eq!(success.extranonce_size, 6);
        assert_eq!(
            success.extranonce_prefix.clone().to_vec(),
            downstream_extranonce_prefix
        );
        assert!(channel.get_extended_channels_ids().contains(&channel_id));
        assert_eq!(
            channel.get_extranonce_prefix(channel_id).unwrap(),
            extranonce_prefix
        );
        assert_eq!(
            channel
                .get_additional_coinbase_script_data(channel_id, 1)
                .unwrap(),
            additional_coinbase_script_data
        );
        for conflicting_id in [0, group_id, channel_id] {
            assert!(matches!(
                channel.replicate_pool_extended_channel(
                    8,
                    [255; 32].into(),
                    vec![0; 10].try_into().unwrap(),
                    conflicting_id,
                    6,
                    additional_coinbase_script_data.clone(),
                ),
                Err(Error::ChannelIdAlreadyInUse(_))
            ));
        }
        assert_eq!(channel.new_group_id(), 43);
        assert_eq!(channel.new_standard_id_for_hom(), 44);
    }

    #[test]
    fn replicate_pool_extended_channel_returns_current_job_and_prev_hash() {
        let additional_coinbase_script_data = vec![1, 2, 3, 4, 5, 6];
        let extranonces = ExtendedExtranonce::new(0..0, 0..10, 10..16);
        let mut channel =
            pool_channel_factory(additional_coinbase_script_data.clone(), extranonces);
        let template_id = 10;
        let mut template = new_template(template_id);
        channel.on_new_template(&mut template).unwrap();
        let prev_hash_from_tp = new_prev_hash(template_id);
        let current_job_id = channel
            .on_new_prev_hash_from_tp(&prev_hash_from_tp)
            .unwrap();

        let target = vec![255; 32].try_into().unwrap();
        let channel_id = 42;
        let result = channel
            .replicate_pool_extended_channel(
                7,
                target,
                vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
                    .try_into()
                    .unwrap(),
                channel_id,
                6,
                additional_coinbase_script_data,
            )
            .unwrap();

        assert_eq!(result.len(), 3);
        let success = match &result[0] {
            Mining::OpenExtendedMiningChannelSuccess(success) => success,
            _ => panic!(),
        };
        let job = match &result[1] {
            Mining::NewExtendedMiningJob(job) => job,
            _ => panic!(),
        };
        let prev_hash = match &result[2] {
            Mining::SetNewPrevHash(prev_hash) => prev_hash,
            _ => panic!(),
        };

        assert_eq!(success.request_id, 7);
        assert_eq!(success.channel_id, channel_id);
        assert_eq!(job.channel_id, channel_id);
        assert_eq!(job.job_id, current_job_id);
        assert!(job.is_future());
        assert_eq!(prev_hash.channel_id, channel_id);
        assert_eq!(prev_hash.job_id, job.job_id);
        assert_eq!(prev_hash.min_ntime, PREV_HEADER_TIMESTAMP);
        assert_eq!(prev_hash.nbits, PREV_HEADER_NBITS);
    }

    #[test]
    fn replicate_pool_extended_channel_rejects_duplicate_prefix_without_channel_outputs() {
        let additional_coinbase_script_data = vec![1, 2, 3, 4, 5, 6];
        let extranonces = ExtendedExtranonce::new(0..0, 0..10, 10..16);
        let mut channel =
            pool_channel_factory(additional_coinbase_script_data.clone(), extranonces);
        let extranonce_prefix = vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19];

        channel
            .replicate_pool_extended_channel(
                7,
                vec![255; 32].try_into().unwrap(),
                extranonce_prefix.clone().try_into().unwrap(),
                42,
                6,
                additional_coinbase_script_data.clone(),
            )
            .unwrap();

        let result = channel.replicate_pool_extended_channel(
            8,
            vec![255; 32].try_into().unwrap(),
            extranonce_prefix.try_into().unwrap(),
            43,
            6,
            additional_coinbase_script_data,
        );

        assert!(matches!(result, Err(Error::ExtranoncePrefixAlreadyInUse)));
        assert!(channel.get_extranonce_prefix(43).is_none());
    }

    #[test]
    fn replicate_pool_extended_channel_rejects_collision_with_unmarked_channel() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        let channel_id = open_output_channel(&mut factory);
        let prefix = factory.get_extranonce_prefix(channel_id).unwrap();
        // The JD mock helper does not assign a CHSEQ output.
        factory
            .replicate_upstream_extended_channel_only_jd(
                [255; 32].into(),
                prefix.clone().try_into().unwrap(),
                42,
                8,
            )
            .unwrap();
        let last_sequence = factory.last_channel_coinbase_sequence;
        assert!(matches!(
            factory.replicate_pool_extended_channel(
                2,
                [255; 32].into(),
                prefix.try_into().unwrap(),
                43,
                8,
                Vec::new(),
            ),
            Err(Error::ExtranoncePrefixAlreadyInUse)
        ));
        assert!(factory.get_extranonce_prefix(43).is_none());
        assert_eq!(factory.last_channel_coinbase_sequence, last_sequence);
    }

    #[test]
    fn replicate_pool_extended_channel_preserves_full_prefix_on_collision() {
        let additional_data = vec![1, 2, 3, 4, 5, 6];
        let mut factory = pool_channel_factory(
            additional_data.clone(),
            ExtendedExtranonce::new(0..0, 0..10, 10..16),
        )
        .with_channel_coinbase_outputs();
        let prefix = vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        for channel_id in [42, 43, 44] {
            let messages = factory
                .replicate_pool_extended_channel(
                    channel_id,
                    [255; 32].into(),
                    prefix.clone().try_into().unwrap(),
                    channel_id,
                    6,
                    additional_data.clone(),
                )
                .unwrap();
            match &messages[0] {
                Mining::OpenExtendedMiningChannelSuccess(success) => {
                    assert_eq!(success.channel_id, channel_id);
                    assert_eq!(success.extranonce_size, 6);
                    assert_eq!(
                        success.extranonce_prefix.inner_as_ref(),
                        [additional_data.as_slice(), prefix.as_slice()].concat()
                    );
                }
                _ => panic!("expected successful channel restoration"),
            }
            assert_eq!(
                factory.get_extranonce_prefix(channel_id),
                Some(prefix.clone())
            );
        }
        let outputs: HashSet<_> = [42, 43, 44]
            .iter()
            .map(|id| factory.channel_coinbase_output(*id).unwrap().0)
            .collect();
        assert_eq!(outputs.len(), 3);
    }

    #[test]
    fn new_extended_channel_skips_restored_prefix() {
        let additional_coinbase_script_data = vec![1, 2, 3, 4, 5, 6];
        let extranonces = ExtendedExtranonce::new(0..0, 0..10, 10..16);
        let mut channel =
            pool_channel_factory(additional_coinbase_script_data.clone(), extranonces);
        let restored_id = channel.new_standard_id_for_hom();
        let restored_prefix = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 1];

        channel
            .replicate_pool_extended_channel(
                7,
                vec![255; 32].try_into().unwrap(),
                restored_prefix.clone().try_into().unwrap(),
                restored_id,
                6,
                additional_coinbase_script_data,
            )
            .unwrap();

        let result = channel
            .new_extended_channel(8, 100_000_000_000_000.0, 6)
            .unwrap();
        let fresh_channel_id = match &result[0] {
            Mining::OpenExtendedMiningChannelSuccess(success) => success.channel_id,
            _ => panic!(),
        };

        assert_eq!(
            channel.get_extranonce_prefix(restored_id).unwrap(),
            restored_prefix
        );
        assert_eq!(
            channel.get_extranonce_prefix(fresh_channel_id).unwrap(),
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
        );
    }

    #[test]
    fn replicate_pool_extended_channel_rejects_additional_data_len_mismatch() {
        let extranonces = ExtendedExtranonce::new(0..0, 0..10, 10..16);
        let mut channel = pool_channel_factory(vec![1, 2, 3, 4, 5, 6], extranonces);
        let target = vec![255; 32].try_into().unwrap();
        let channel_id = 42;

        let result = channel.replicate_pool_extended_channel(
            7,
            target,
            vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
                .try_into()
                .unwrap(),
            channel_id,
            6,
            vec![1, 2, 3, 4, 5],
        );

        assert!(matches!(
            result,
            Err(Error::NewAdditionalCoinbaseDataLenDoNotMatch)
        ));
        assert!(channel.get_extranonce_prefix(channel_id).is_none());
    }

    #[test]
    fn replicate_pool_extended_channel_rejects_prefix_len_mismatch() {
        let extranonces = ExtendedExtranonce::new(0..0, 0..10, 10..16);
        let mut channel = pool_channel_factory(vec![1, 2, 3, 4, 5, 6], extranonces);
        let target = vec![255; 32].try_into().unwrap();
        let channel_id = 42;

        let result = channel.replicate_pool_extended_channel(
            7,
            target,
            vec![10, 11, 12, 13, 14, 15, 16, 17, 18].try_into().unwrap(),
            channel_id,
            6,
            vec![1, 2, 3, 4, 5, 6],
        );

        assert!(matches!(result, Err(Error::InvalidExtranonceSize(10, 9))));
        assert!(channel.get_extranonce_prefix(channel_id).is_none());
    }

    #[test]
    fn replicate_pool_extended_channel_rejects_extranonce_size_mismatch() {
        let extranonces = ExtendedExtranonce::new(0..0, 0..10, 10..16);
        let mut channel = pool_channel_factory(vec![1, 2, 3, 4, 5, 6], extranonces);
        let target = vec![255; 32].try_into().unwrap();
        let channel_id = 42;

        let result = channel.replicate_pool_extended_channel(
            7,
            target,
            vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
                .try_into()
                .unwrap(),
            channel_id,
            5,
            vec![1, 2, 3, 4, 5, 6],
        );

        assert!(matches!(result, Err(Error::InvalidExtranonceSize(6, 5))));
        assert!(channel.get_extranonce_prefix(channel_id).is_none());
    }

    #[test]
    fn test_complete_mining_round() {
        let (prefix, coinbase_extranonce, _) = get_coinbase();

        // Initialize a Channel of type Pool
        let out = TxOut {value: Amount::from_sat(BLOCK_REWARD), script_pubkey: decode_hex("4104c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2ac").unwrap().into()};
        let additional_coinbase_script_data = "".to_string();
        let creator = JobsCreators::new(7);
        let share_per_min = 1.0;
        // Create an ExtendedExtranonce of len 7:
        // upstream part is 0 bytes cause we are a pool so no more upstreams
        // self part is 7 bytes
        // downstream part is 0 cause in the test the downstream is HOM so we do not need to
        // reserve space for downstream
        let mut inner = coinbase_extranonce.clone();
        inner[6] = 0;
        let extranonces = ExtendedExtranonce::new_with_inner_only_test(0..0, 0..0, 0..7, inner);

        let ids = Arc::new(Mutex::new(GroupId::new()));
        let channel_kind = ExtendedChannelKind::Pool;
        let mut channel = PoolChannelFactory::new(
            ids,
            extranonces,
            creator,
            share_per_min,
            channel_kind,
            vec![out],
            additional_coinbase_script_data.into_bytes(),
        )
        .unwrap();

        // Build a NewTemplate
        let new_template = NewTemplate {
            template_id: 10,
            future_template: true,
            version: VERSION,
            coinbase_tx_version: 1,
            coinbase_prefix: prefix.try_into().unwrap(),
            coinbase_tx_input_sequence: u32::MAX,
            coinbase_tx_value_remaining: 5_000_000_000,
            coinbase_tx_outputs_count: 0,
            coinbase_tx_outputs: get_coinbase_outputs(),
            coinbase_tx_locktime: 0,
            merkle_path: get_merkle_path(),
        };

        // "Send" the NewTemplate to the channel
        let _ = channel.on_new_template(&mut (new_template.clone()));

        // Build a PrevHash
        let mut p_hash = decode_hex(PREV_HASH).unwrap();
        p_hash.reverse();
        let prev_hash = SetNewPrevHashFromTp {
            template_id: 10,
            prev_hash: p_hash.try_into().unwrap(),
            header_timestamp: PREV_HEADER_TIMESTAMP,
            n_bits: PREV_HEADER_NBITS,
            target: nbit_to_target(PREV_HEADER_NBITS),
        };

        // "Send" the SetNewPrevHash to channel
        let _ = channel.on_new_prev_hash_from_tp(&prev_hash);

        // Build open standard channel
        let open_standard_channel = OpenStandardMiningChannel {
            request_id: 100.into(),
            user_identity: "Gigi".to_string().try_into().unwrap(),
            nominal_hash_rate: 100_000_000_000_000.0,
            max_target: [255; 32].try_into().unwrap(),
        };

        // "Send" the OpenStandardMiningChannel to channel
        let result = loop {
            let id = channel.new_standard_id_for_hom();
            let result = channel
                .add_standard_channel(
                    open_standard_channel.get_request_id_as_u32(),
                    open_standard_channel.nominal_hash_rate,
                    true,
                    id,
                )
                .unwrap();
            let downsteram_extranonce = match &result[0] {
                Mining::OpenStandardMiningChannelSuccess(msg) => {
                    msg.extranonce_prefix.clone().to_vec()
                }
                _ => panic!(),
            };
            if downsteram_extranonce == coinbase_extranonce {
                break result;
            }
        };
        let mut result = result.iter();

        // Get the expected job id and channel_id
        let mut channel_id = u32::MAX;
        let job_id = loop {
            match result.next().unwrap() {
                Mining::OpenStandardMiningChannelSuccess(success) => {
                    channel_id = success.channel_id
                }
                Mining::SetNewPrevHash(_) => (),
                Mining::NewMiningJob(job) => break job.job_id,
                _ => panic!(),
            }
        };
        // make sure job management in channel factory is updated
        (0..job_id - 1).for_each(|_| {
            channel.job_creator.reset_new_templates(None);
            let _ = channel.on_new_template(&mut (new_template.clone()));
            let _ = channel.on_new_prev_hash_from_tp(&prev_hash);
        });

        // Build the success share
        let share = SubmitSharesStandard {
            channel_id,
            sequence_number: 2,
            job_id,
            nonce: u32::from_le_bytes(decode_hex(NONCE).unwrap().try_into().unwrap()),
            ntime: u32::from_le_bytes(decode_hex(NTIME).unwrap().try_into().unwrap()),
            version: 1,
        };

        // "Send" the Share to channel
        match channel.on_submit_shares_standard(share).unwrap() {
            OnNewShare::SendErrorDownstream(e) => panic!(
                "{:?} \n {}",
                e,
                std::str::from_utf8(&e.error_code.to_vec()[..]).unwrap()
            ),
            OnNewShare::SendSubmitShareUpstream(_) => panic!(),
            OnNewShare::RelaySubmitShareUpstream => panic!(),
            OnNewShare::ShareMeetBitcoinTarget(_) => assert!(true),
            OnNewShare::ShareMeetDownstreamTarget => panic!(),
        };
    }
    #[test]
    fn test_extranonce_prefix_in_hom() {
        let extranonce_prefix1 = [10, 11, 12];
        let (prefix, _, _) = get_coinbase();

        // Initialize a Channel of type Pool
        let out = TxOut {value: Amount::from_sat(BLOCK_REWARD), script_pubkey: decode_hex("4104c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2ac").unwrap().into()};
        let creator = JobsCreators::new(7);
        let share_per_min = 1.0;
        let extranonces = ExtendedExtranonce::new(0..0, 0..0, 0..7);

        let ids = Arc::new(Mutex::new(GroupId::new()));
        let channel_kind = ExtendedChannelKind::Pool;
        let mut channel = PoolChannelFactory::new(
            ids,
            extranonces,
            creator,
            share_per_min,
            channel_kind,
            vec![out],
            extranonce_prefix1.clone().into(),
        )
        .unwrap();

        // Build a NewTemplate
        let new_template = NewTemplate {
            template_id: 10,
            future_template: true,
            version: VERSION,
            coinbase_tx_version: 1,
            coinbase_prefix: prefix.try_into().unwrap(),
            coinbase_tx_input_sequence: u32::MAX,
            coinbase_tx_value_remaining: 5_000_000_000,
            coinbase_tx_outputs_count: 0,
            coinbase_tx_outputs: get_coinbase_outputs(),
            coinbase_tx_locktime: 0,
            merkle_path: get_merkle_path(),
        };

        // "Send" the NewTemplate to the channel
        let _ = channel.on_new_template(&mut (new_template.clone()));

        // Build a PrevHash
        let mut p_hash = decode_hex(PREV_HASH).unwrap();
        p_hash.reverse();
        let prev_hash = SetNewPrevHashFromTp {
            template_id: 10,
            prev_hash: p_hash.try_into().unwrap(),
            header_timestamp: PREV_HEADER_TIMESTAMP,
            n_bits: PREV_HEADER_NBITS,
            target: nbit_to_target(PREV_HEADER_NBITS),
        };

        // "Send" the SetNewPrevHash to channel
        let _ = channel.on_new_prev_hash_from_tp(&prev_hash);

        let result = channel
            .add_standard_channel(100, 100_000_000_000_000.0, true, 2)
            .unwrap();
        let extranonce_prefix = match &result[0] {
            Mining::OpenStandardMiningChannelSuccess(msg) => msg.extranonce_prefix.clone().to_vec(),
            _ => panic!(),
        };
        assert!(&extranonce_prefix.to_vec()[0..3] == extranonce_prefix1);
    }
    #[test]
    fn test_extranonce_prefix_in_extended() {
        let extranonce_prefix1 = [10, 11, 12];
        let extranonce_prefix2 = [14, 11, 12];
        let (prefix, _, _) = get_coinbase();

        // Initialize a Channel of type Pool
        let out = TxOut {value: Amount::from_sat(BLOCK_REWARD), script_pubkey: decode_hex("4104c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2ac").unwrap().into()};
        let creator = JobsCreators::new(16);
        let share_per_min = 1.0;
        let extranonces = ExtendedExtranonce::new(0..0, 0..8, 8..16);

        let ids = Arc::new(Mutex::new(GroupId::new()));
        let channel_kind = ExtendedChannelKind::Pool;
        let mut channel = PoolChannelFactory::new(
            ids,
            extranonces,
            creator,
            share_per_min,
            channel_kind,
            vec![out],
            extranonce_prefix1.clone().into(),
        )
        .unwrap();

        // Build a NewTemplate
        let new_template = NewTemplate {
            template_id: 10,
            future_template: true,
            version: VERSION,
            coinbase_tx_version: 1,
            coinbase_prefix: prefix.try_into().unwrap(),
            coinbase_tx_input_sequence: u32::MAX,
            coinbase_tx_value_remaining: 5_000_000_000,
            coinbase_tx_outputs_count: 0,
            coinbase_tx_outputs: get_coinbase_outputs(),
            coinbase_tx_locktime: 0,
            merkle_path: get_merkle_path(),
        };

        // "Send" the NewTemplate to the channel
        let _ = channel.on_new_template(&mut (new_template.clone()));

        // Build a PrevHash
        let mut p_hash = decode_hex(PREV_HASH).unwrap();
        p_hash.reverse();
        let prev_hash = SetNewPrevHashFromTp {
            template_id: 10,
            prev_hash: p_hash.try_into().unwrap(),
            header_timestamp: PREV_HEADER_TIMESTAMP,
            n_bits: PREV_HEADER_NBITS,
            target: nbit_to_target(PREV_HEADER_NBITS),
        };

        let _ = channel.on_new_prev_hash_from_tp(&prev_hash);

        let result = channel
            .new_extended_channel(100, 100_000_000_000_000.0, 2)
            .unwrap();
        let (extranonce_prefix, channel_id) = match &result[0] {
            Mining::OpenExtendedMiningChannelSuccess(msg) => {
                (msg.extranonce_prefix.clone().to_vec(), msg.channel_id)
            }
            _ => panic!(),
        };
        assert!(&extranonce_prefix.to_vec()[0..3] == extranonce_prefix1);
        match channel
            .change_additional_coinbase_script_data(extranonce_prefix2.to_vec(), channel_id)
        {
            Ok(Mining::SetExtranoncePrefix(msg)) => {
                assert!(&msg.extranonce_prefix.to_vec()[0..3] == extranonce_prefix2);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn extended_fanout_rejects_non_future_template_without_mutating_job_creator() {
        let (prefix, _, _) = get_coinbase();
        let out = TxOut {value: Amount::from_sat(BLOCK_REWARD), script_pubkey: decode_hex("4104c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2ac").unwrap().into()};
        let creator = JobsCreators::new(7);
        let share_per_min = 1.0;
        let extranonces = ExtendedExtranonce::new(0..0, 0..0, 0..7);
        let ids = Arc::new(Mutex::new(GroupId::new()));
        let channel_kind = ExtendedChannelKind::Pool;
        let mut channel = PoolChannelFactory::new(
            ids,
            extranonces,
            creator,
            share_per_min,
            channel_kind,
            vec![out],
            Vec::new(),
        )
        .unwrap();

        let id = channel.new_standard_id_for_hom();
        channel
            .add_standard_channel(100, 100_000_000_000_000.0, true, id)
            .unwrap();
        let job_ids_before = channel.inner.job_ids.clone();

        let mut p_hash = decode_hex(PREV_HASH).unwrap();
        p_hash.reverse();
        let prev_hash = SetNewPrevHashFromTp {
            template_id: 10,
            prev_hash: p_hash.try_into().unwrap(),
            header_timestamp: PREV_HEADER_TIMESTAMP,
            n_bits: PREV_HEADER_NBITS,
            target: nbit_to_target(PREV_HEADER_NBITS),
        };
        channel.job_creator.on_new_prev_hash(&prev_hash);

        let mut new_template = NewTemplate {
            template_id: 10,
            future_template: false,
            version: VERSION,
            coinbase_tx_version: 1,
            coinbase_prefix: prefix.try_into().unwrap(),
            coinbase_tx_input_sequence: u32::MAX,
            coinbase_tx_value_remaining: 5_000_000_000,
            coinbase_tx_outputs_count: 0,
            coinbase_tx_outputs: get_coinbase_outputs(),
            coinbase_tx_locktime: 0,
            merkle_path: get_merkle_path(),
        };

        assert!(matches!(
            channel.on_new_template_for_extended_fanout(&mut new_template),
            Err(Error::JobIsNotFutureButPrevHashNotPresent)
        ));
        assert!(channel.job_creator.get_template_id_from_job(1).is_none());
        assert_eq!(channel.inner.job_ids, job_ids_before);
    }

    #[test]
    #[allow(deprecated)]
    fn deprecated_job_variant_forwards_the_difficulty_output() {
        for marked in [false, true] {
            let mut factory =
                pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
            if marked {
                factory = factory.with_channel_coinbase_outputs();
            }
            let channel_id = open_output_channel(&mut factory);
            let messages = factory.on_new_template(&mut new_template(10)).unwrap();
            let job = match messages.get(&channel_id).unwrap() {
                Mining::NewExtendedMiningJob(job) => job.clone(),
                _ => panic!("expected extended job"),
            };
            let output = TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new_op_return(b"DIFF32abcd"),
            };
            let suffix = job.coinbase_tx_suffix.as_ref();
            let (mut outputs, consumed): (Vec<TxOut>, usize) =
                deserialize_partial(&suffix[4..]).unwrap();
            outputs.push(output.clone());
            let variant = [&suffix[..4], &serialize(&outputs), &suffix[4 + consumed..]].concat();

            let future_jobs = std::mem::take(&mut factory.inner.future_jobs);
            factory.register_extended_job_variant(channel_id, job.job_id, variant.clone());
            factory.inner.future_jobs = future_jobs;
            assert_eq!(
                factory
                    .inner
                    .extended_job_coinbase_outputs
                    .get(&(channel_id, job.job_id)),
                Some(&output)
            );
            for invalid in [Vec::new(), suffix.to_vec(), vec![0; 4]] {
                factory.register_extended_job_variant(channel_id, job.job_id, invalid);
                assert_eq!(
                    factory
                        .inner
                        .extended_job_coinbase_outputs
                        .get(&(channel_id, job.job_id)),
                    Some(&output),
                    "suffixes without DIFF32 must preserve the registered output"
                );
            }
            let mut prev_hash = new_prev_hash(10);
            prev_hash.target = [255; 32].into();
            factory.on_new_prev_hash_from_tp(&prev_hash).unwrap();
            // The adapter also accepts a job after it moves from the future cache to the valid cache.
            factory.register_extended_job_variant(channel_id, job.job_id, variant.clone());
            let mut share = submit_extended_share(channel_id);
            share.job_id = job.job_id;
            match factory.on_submit_shares_extended(share).unwrap() {
                OnNewShare::ShareMeetBitcoinTarget((_, _, coinbase, _)) => assert_eq!(
                    coinbase,
                    [
                        job.coinbase_tx_prefix.to_vec(),
                        factory.get_extranonce_prefix(channel_id).unwrap(),
                        vec![0; 8],
                        variant,
                    ]
                    .concat()
                ),
                result => panic!("expected accepted share, got {:?}", result),
            }
        }
    }

    #[test]
    fn extended_job_coinbase_outputs_are_selected_by_channel_and_job_id() {
        let extranonces = ExtendedExtranonce::new(0..0, 0..8, 8..16);
        let mut channel = pool_channel_factory(Vec::new(), extranonces);
        let channel_id_1 = match &channel
            .new_extended_channel(100, 100_000_000_000_000.0, 8)
            .unwrap()[0]
        {
            Mining::OpenExtendedMiningChannelSuccess(success) => success.channel_id,
            _ => panic!(),
        };
        let channel_id_2 = match &channel
            .new_extended_channel(101, 100_000_000_000_000.0, 8)
            .unwrap()[0]
        {
            Mining::OpenExtendedMiningChannelSuccess(success) => success.channel_id,
            _ => panic!(),
        };

        let template_id = 10;
        let mut template = new_template(template_id);
        let messages = channel.on_new_template(&mut template).unwrap();
        let job_1 = match messages.get(&channel_id_1).unwrap() {
            Mining::NewExtendedMiningJob(job) => job.clone(),
            _ => panic!(),
        };
        let job_2 = match messages.get(&channel_id_2).unwrap() {
            Mining::NewExtendedMiningJob(job) => job.clone(),
            _ => panic!(),
        };
        assert_eq!(job_1.job_id, job_2.job_id);

        let output_1 = TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::new_op_return(b"DIFF32abcd"),
        };
        let output_2 = TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::new_op_return(b"DIFF32efgh"),
        };
        let job_id = job_1.job_id;
        channel.register_extended_job_coinbase_output(channel_id_1, job_id, output_1.clone());
        channel.register_extended_job_coinbase_output(channel_id_2, job_id, output_2.clone());

        let mut prev_hash = new_prev_hash(template_id);
        prev_hash.target = vec![255; 32].try_into().unwrap();
        channel.on_new_prev_hash_from_tp(&prev_hash).unwrap();

        for (channel_id, job, output) in [
            (channel_id_1, job_1, output_1),
            (channel_id_2, job_2, output_2),
        ] {
            let mut share = submit_extended_share(channel_id);
            share.job_id = job_id;
            let result = channel.on_submit_shares_extended(share).unwrap();
            let coinbase = match result {
                OnNewShare::ShareMeetBitcoinTarget((_, _, coinbase, _)) => coinbase,
                other => panic!("expected bitcoin-target share, got {:?}", other),
            };
            let canonical_coinbase = [
                job.coinbase_tx_prefix.to_vec(),
                channel.get_extranonce_prefix(channel_id).unwrap(),
                vec![0; 8],
                job.coinbase_tx_suffix.to_vec(),
            ]
            .concat();
            let mut expected_coinbase: stratum_common::bitcoin::Transaction =
                stratum_common::bitcoin::consensus::deserialize(&canonical_coinbase).unwrap();
            expected_coinbase.output.push(output);
            assert_eq!(coinbase, serialize(&expected_coinbase));
        }
    }

    #[test]
    fn current_extended_job_for_channel_returns_only_the_canonical_job() {
        let extranonces = ExtendedExtranonce::new(0..0, 0..8, 8..16);
        let mut channel = pool_channel_factory(Vec::new(), extranonces);
        let channel_id = match &channel
            .new_extended_channel(100, 100_000_000_000_000.0, 8)
            .unwrap()[0]
        {
            Mining::OpenExtendedMiningChannelSuccess(success) => success.channel_id,
            _ => panic!(),
        };

        assert!(channel
            .current_extended_job_for_channel(channel_id)
            .is_none());

        let template_id = 10;
        let mut template = new_template(template_id);
        channel.on_new_template(&mut template).unwrap();
        channel
            .on_new_prev_hash_from_tp(&new_prev_hash(template_id))
            .unwrap();

        let canonical_job = channel.inner.get_last_valid_job().unwrap().0.clone();
        channel.register_extended_job_coinbase_output(
            channel_id,
            canonical_job.job_id,
            TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new_op_return(b"DIFF32abcd"),
            },
        );

        let current_job = channel
            .current_extended_job_for_channel(channel_id)
            .unwrap();
        assert_eq!(current_job, canonical_job);
    }

    #[test]
    fn legacy_custom_job_api_keeps_main_behavior_and_success_return_type() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let channel_id = open_output_channel(&mut factory);
        let custom = custom_job_with_prefix(channel_id, Vec::new());
        let success: SetCustomMiningJobSuccess =
            factory.on_new_set_custom_mining_job(custom.clone());
        assert_eq!(success.channel_id, channel_id);
        assert_eq!(success.request_id, custom.request_id);
        assert_eq!(factory.negotiated_jobs.get(&channel_id), Some(&custom));
    }

    #[test]
    fn invalid_custom_job_does_not_poison_factory_or_replace_previous_job() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        let channel_id = open_output_channel(&mut factory);
        let mut valid = custom_job_with_prefix(channel_id, Vec::new());
        let mut outputs = valid.coinbase_tx_outputs.to_vec();
        outputs.extend(serialize(
            &factory
                .channel_coinbase_output(channel_id)
                .unwrap()
                .tx_out(),
        ));
        valid.coinbase_tx_outputs = outputs.try_into().unwrap();
        let accepted = factory
            .try_on_new_set_custom_mining_job(valid.clone())
            .unwrap();
        let previous_job_ids = factory.inner.job_ids.clone();

        let factory = Mutex::new(factory);
        let mut invalid = custom_job_with_prefix(channel_id, Vec::new());
        invalid.request_id = 42;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            factory.safe_lock(|factory| factory.try_on_new_set_custom_mining_job(invalid))
        }));
        let error = result
            .expect("invalid CHSEQ must not panic")
            .expect("invalid CHSEQ must not poison the shared factory")
            .expect_err("missing CHSEQ must be rejected");
        assert_eq!(error.channel_id, channel_id);
        assert_eq!(error.request_id, 42);
        assert_eq!(
            error.error_code.as_ref(),
            b"invalid-job-param-value-coinbase_tx_outputs"
        );
        factory
            .safe_lock(|factory| {
                assert_eq!(factory.negotiated_jobs.get(&channel_id), Some(&valid));
                assert_eq!(factory.inner.job_ids, previous_job_ids);
                let next = factory.try_on_new_set_custom_mining_job(valid).unwrap();
                assert_eq!(next.job_id, accepted.job_id + 1);
            })
            .expect("invalid CHSEQ must not poison the shared factory");
    }

    #[test]
    fn colliding_custom_jobs_reject_invalid_channel_output_before_registration() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16))
                .with_channel_coinbase_outputs();
        let first = open_output_channel(&mut factory);
        let prefix = factory.get_extranonce_prefix(first).unwrap();
        let second = 99;
        factory
            .replicate_pool_extended_channel(
                2,
                [255; 32].into(),
                prefix.try_into().unwrap(),
                second,
                8,
                Vec::new(),
            )
            .unwrap();
        let mut prev_hash = new_prev_hash(10);
        prev_hash.target = [255; 32].into();
        factory.job_creator.on_new_prev_hash(&prev_hash);
        let first_output = factory.channel_coinbase_output(first).unwrap().tx_out();
        let second_output = factory.channel_coinbase_output(second).unwrap().tx_out();
        for (channel_id, correct, wrong) in [
            (first, first_output.clone(), second_output.clone()),
            (second, second_output, first_output),
        ] {
            let mut nonzero = correct.clone();
            nonzero.value = Amount::from_sat(1);
            for (markers, valid) in [
                (vec![correct.clone()], true),
                (vec![], false),
                (vec![wrong.clone()], false),
                (vec![correct.clone(), correct.clone()], false),
                (vec![correct.clone(), wrong], false),
                (vec![nonzero], false),
            ] {
                let mut custom = custom_job_with_prefix(channel_id, vec![0x02, 0xe8, 0x03, 0]);
                let mut outputs = get_custom_job_outputs().to_vec();
                for marker in &markers {
                    outputs.extend(serialize(marker));
                }
                custom.request_id = 42;
                custom.coinbase_tx_outputs = outputs.clone().try_into().unwrap();
                let previous_job_ids = factory.inner.job_ids.clone();
                let previous_outputs = factory
                    .negotiated_jobs
                    .get(&channel_id)
                    .map(|job| job.coinbase_tx_outputs.clone());
                let result = factory.try_on_new_set_custom_mining_job(custom);
                if valid {
                    let success = result.unwrap();
                    let mut share = submit_extended_share(channel_id);
                    share.job_id = success.job_id;
                    match factory.on_submit_shares_extended(share).unwrap() {
                        OnNewShare::ShareMeetBitcoinTarget((_, _, coinbase, _)) => {
                            let tx: stratum_common::bitcoin::Transaction =
                                stratum_common::bitcoin::consensus::deserialize(&coinbase).unwrap();
                            assert_eq!(tx.output.last(), Some(&correct));
                        }
                        result => panic!("expected accepted custom share, got {:?}", result),
                    }
                    assert_eq!(
                        factory.negotiated_jobs[&channel_id]
                            .coinbase_tx_outputs
                            .as_ref(),
                        outputs
                    );
                } else {
                    let error = result.expect_err("invalid CHSEQ must be rejected");
                    assert_eq!(error.channel_id, channel_id);
                    assert_eq!(error.request_id, 42);
                    assert_eq!(
                        error.error_code.as_ref(),
                        b"invalid-job-param-value-coinbase_tx_outputs"
                    );
                    assert_eq!(factory.inner.job_ids, previous_job_ids);
                    assert_eq!(
                        factory
                            .negotiated_jobs
                            .get(&channel_id)
                            .map(|job| job.coinbase_tx_outputs.clone()),
                        previous_outputs
                    );
                }
            }
        }
    }

    #[test]
    fn custom_shares_use_latest_channel_job_and_preserve_pool_wire_ids() {
        let mut factory =
            pool_channel_factory(Vec::new(), ExtendedExtranonce::new(0..0, 0..8, 8..16));
        let channel_id = open_output_channel(&mut factory);
        let other_channel_id = open_output_channel(&mut factory);
        // Use a permissive target to isolate job selection from nonce search.
        let mut prev_hash = new_prev_hash(10);
        prev_hash.target = [255; 32].into();
        factory.job_creator.on_new_prev_hash(&prev_hash);

        let first = custom_job_with_prefix(channel_id, vec![0x02, 0xe8, 0x03, 0]);
        let first_ack = factory
            .try_on_new_set_custom_mining_job(first.clone())
            .unwrap();
        let mut share = submit_extended_share(channel_id);
        // The pool offsets the factory's ID before acknowledging the job downstream.
        share.job_id = first_ack.job_id.wrapping_add(1_000_000_000);
        match factory.on_submit_shares_extended(share.clone()).unwrap() {
            OnNewShare::ShareMeetBitcoinTarget((accepted, _, coinbase, _)) => {
                assert_eq!(accepted.get_job_id(), share.job_id);
                let tx: stratum_common::bitcoin::Transaction =
                    stratum_common::bitcoin::consensus::deserialize(&coinbase).unwrap();
                assert_eq!(tx.lock_time.to_consensus_u32(), 0);
            }
            result => panic!("expected accepted custom share, got {:?}", result),
        }

        let mut other = custom_job_with_prefix(other_channel_id, vec![0x02, 0xe8, 0x03, 0]);
        other.coinbase_tx_locktime = 2;
        let other_ack = factory.try_on_new_set_custom_mining_job(other).unwrap();

        let mut second = first;
        second.request_id = 2;
        second.coinbase_tx_locktime = 1;
        let second_ack = factory.try_on_new_set_custom_mining_job(second).unwrap();
        assert_ne!(first_ack.job_id, second_ack.job_id);
        for (channel_id, job_id, lock_time) in [
            (channel_id, second_ack.job_id, 1),
            // Selection uses the channel's latest job, even if the wire ID is unchanged.
            (channel_id, first_ack.job_id, 1),
            (other_channel_id, other_ack.job_id, 2),
        ] {
            share.channel_id = channel_id;
            share.job_id = job_id.wrapping_add(1_000_000_000);
            share.sequence_number += 1;
            match factory.on_submit_shares_extended(share.clone()).unwrap() {
                OnNewShare::ShareMeetBitcoinTarget((accepted, _, coinbase, _)) => {
                    assert_eq!(accepted.get_job_id(), share.job_id);
                    let tx: stratum_common::bitcoin::Transaction =
                        stratum_common::bitcoin::consensus::deserialize(&coinbase).unwrap();
                    assert_eq!(tx.lock_time.to_consensus_u32(), lock_time);
                }
                result => panic!("expected accepted custom share, got {:?}", result),
            }
        }

        factory.close_channel(channel_id);
        assert!(!factory.negotiated_jobs.contains_key(&channel_id));
        assert!(factory.negotiated_jobs.contains_key(&other_channel_id));
    }

    #[test]
    fn current_extended_job_for_channel_returns_none_for_custom_job() {
        let extranonces = ExtendedExtranonce::new(0..0, 0..8, 8..16);
        let mut channel = pool_channel_factory(Vec::new(), extranonces);
        let channel_id = match &channel
            .new_extended_channel(100, 100_000_000_000_000.0, 8)
            .unwrap()[0]
        {
            Mining::OpenExtendedMiningChannelSuccess(success) => success.channel_id,
            _ => panic!(),
        };

        let template_id = 10;
        let mut template = new_template(template_id);
        channel.on_new_template(&mut template).unwrap();
        channel
            .on_new_prev_hash_from_tp(&new_prev_hash(template_id))
            .unwrap();
        assert!(channel
            .current_extended_job_for_channel(channel_id)
            .is_some());

        channel
            .try_on_new_set_custom_mining_job(custom_job_with_prefix(channel_id, Vec::new()))
            .unwrap();

        assert!(channel
            .current_extended_job_for_channel(channel_id)
            .is_none());
    }

    #[test]
    fn stale_extended_job_coinbase_output_cannot_make_evicted_base_job_valid() {
        let extranonces = ExtendedExtranonce::new(0..0, 0..8, 8..16);
        let mut channel = pool_channel_factory(Vec::new(), extranonces);
        let channel_id = match &channel
            .new_extended_channel(100, 100_000_000_000_000.0, 8)
            .unwrap()[0]
        {
            Mining::OpenExtendedMiningChannelSuccess(success) => success.channel_id,
            _ => panic!(),
        };

        let template_id = 10;
        let mut template = new_template(template_id);
        let messages = channel.on_new_template(&mut template).unwrap();
        let stale_job = match messages.get(&channel_id).unwrap() {
            Mining::NewExtendedMiningJob(job) => job.clone(),
            _ => panic!(),
        };
        let stale_job_id = stale_job.job_id;
        let output = TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::new_op_return(b"DIFF32abcd"),
        };
        channel.register_extended_job_coinbase_output(channel_id, stale_job_id, output.clone());
        channel
            .on_new_prev_hash_from_tp(&new_prev_hash(template_id))
            .unwrap();

        for template_id in 11..14 {
            let mut template = new_template(template_id);
            template.future_template = false;
            channel.on_new_template(&mut template).unwrap();
        }

        assert!(channel.inner.get_valid_job(stale_job_id).is_none());
        assert!(!channel
            .inner
            .extended_job_coinbase_outputs
            .contains_key(&(channel_id, stale_job_id)));

        channel.register_extended_job_coinbase_output(channel_id, stale_job_id, output);
        assert!(channel
            .inner
            .extended_job_coinbase_outputs
            .contains_key(&(channel_id, stale_job_id)));
        let mut share = submit_extended_share(channel_id);
        share.job_id = stale_job_id;
        assert!(matches!(
            channel.on_submit_shares_extended(share),
            Err(Error::ShareDoNotMatchAnyJob)
        ));
    }

    #[test]
    fn malformed_custom_job_coinbase_prefix_returns_error_instead_of_panicking() {
        let out = TxOut {
            value: Amount::from_sat(BLOCK_REWARD),
            script_pubkey: decode_hex(
                "4104c6d0969c2d98a5c19ba7c36c7937c5edbd60ff2a01397c4afe54f16cd641667ea0049ba6f9e1796ba3c8e49e1b504c532ebbaaa1010c3f7d9b83a8ea7fd800e2ac",
            )
            .unwrap()
            .into(),
        };
        let creator = JobsCreators::new(16);
        let share_per_min = 1.0;
        let extranonces = ExtendedExtranonce::new(0..0, 0..8, 8..16);
        let ids = Arc::new(Mutex::new(GroupId::new()));
        let channel_kind = ExtendedChannelKind::Pool;
        let mut channel = PoolChannelFactory::new(
            ids,
            extranonces,
            creator,
            share_per_min,
            channel_kind,
            vec![out],
            Vec::new(),
        )
        .unwrap();

        let result = channel
            .new_extended_channel(100, 100_000_000_000_000.0, 2)
            .unwrap();
        let channel_id = match &result[0] {
            Mining::OpenExtendedMiningChannelSuccess(msg) => msg.channel_id,
            _ => panic!(),
        };

        let malformed_prefix = vec![0x4c];
        channel
            .try_on_new_set_custom_mining_job(custom_job_with_prefix(
                channel_id,
                malformed_prefix.clone(),
            ))
            .unwrap();

        assert!(matches!(
            channel.on_submit_shares_extended(submit_extended_share(channel_id)),
            Err(Error::InvalidBip34Bytes(bytes)) if bytes == malformed_prefix
        ));
        //panic!();
    }
}
