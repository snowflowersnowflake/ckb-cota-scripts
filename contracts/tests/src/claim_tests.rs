use crate::constants::{
    BYTE32_ZEROS, CLAIM_NFT_SMT_TYPE, DEFINE_NFT_SMT_TYPE, HOLD_NFT_SMT_TYPE,
    WITHDRAWAL_NFT_SMT_TYPE,
};
use crate::{assert_script_error, Loader};
use ckb_testtool::ckb_types::{
    bytes::Bytes,
    core::{TransactionBuilder, TransactionView},
    packed::*,
    prelude::*,
};
use ckb_testtool::context::random_out_point;
use ckb_testtool::{builtin::ALWAYS_SUCCESS, context::Context};
use cota_smt::smt::blake2b_256;
use cota_smt::{
    common::{Byte32, Byte32Builder, BytesBuilder, CotaId, Uint16, Uint32, *},
    smt::{Blake2bHasher, H256, SMT},
    transfer::*,
};
use rand::{thread_rng, Rng};

const MAX_CYCLES: u64 = 70_000_000;

// error numbers
const SMT_PROOF_VERIFY_FAILED: i8 = 9;
const COTA_NFT_SMT_TYPE_ERROR: i8 = 23;
const COTA_NFT_ACTION_ERROR: i8 = 24;
const COTA_NFT_WITHDRAW_DEP_ERROR: i8 = 33;
const CLAIMED_COTA_WITHDRAWAL_SMT_VERIFY_FAILED: i8 = 34;

#[derive(PartialEq, Copy, Clone)]
enum ClaimError {
    NoError,
    SMTProofVerifyFailed,
    CoTANFTSmtTypeError,
    CoTANFTActionError,
    CoTANFTWithdrawalDepError,
    ClaimedCoTAWithdrawalSMTVerifyFailed,
}

const CLAIM_COTA: u8 = 4;

fn generate_withdrawal_cota_nft_smt_data(
    cota_input_out_point: OutPoint,
    to_lock: Script,
    withdrawal_count: usize,
) -> (
    [u8; 32],
    Vec<CotaNFTId>,
    Vec<WithdrawalCotaNFTValue>,
    Vec<u8>,
) {
    let leaves_count = 100;
    let mut withdrawal_smt = SMT::default();

    let mut rng = thread_rng();
    for _ in 0..leaves_count {
        let key: H256 = rng.gen::<[u8; 32]>().into();
        let value: H256 = H256::from([255u8; 32]);
        withdrawal_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let mut withdrawal_keys: Vec<CotaNFTId> = Vec::new();
    let mut withdrawal_values: Vec<WithdrawalCotaNFTValue> = Vec::new();
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(withdrawal_count * 2);

    let cota_id_vec: Vec<u8> = hex::decode("157a3633c3477d84b604a25e5fca5ca681762c10").unwrap();
    for index in 0..withdrawal_count {
        let token_index = Uint32::from_slice(&[0u8, 0u8, 0u8, index as u8]).unwrap();
        let hold_key = CotaNFTIdBuilder::default()
            .cota_id(CotaId::from_slice(&cota_id_vec).unwrap())
            .smt_type(Uint16::from_slice(&HOLD_NFT_SMT_TYPE.to_be_bytes()).unwrap())
            .index(token_index.clone())
            .build();

        let mut hold_key_bytes = [0u8; 32];
        hold_key_bytes[0..26].copy_from_slice(hold_key.as_slice());
        let key = H256::from(hold_key_bytes);

        let hold_value = CotaNFTInfoBuilder::default()
            .characteristic(Characteristic::from_slice(&[5u8; 20]).unwrap())
            .configure(Byte::from(0u8))
            .state(Byte::from(0u8))
            .build();
        update_leaves.push((key, H256::from(BYTE32_ZEROS)));
        withdrawal_smt
            .update(key, H256::from(BYTE32_ZEROS))
            .expect("SMT update leave error");

        let withdrawal_key = CotaNFTIdBuilder::default()
            .cota_id(CotaId::from_slice(&cota_id_vec).unwrap())
            .smt_type(Uint16::from_slice(&WITHDRAWAL_NFT_SMT_TYPE.to_be_bytes()).unwrap())
            .index(token_index)
            .build();
        let mut withdrawal_key_bytes = [0u8; 32];
        withdrawal_key_bytes[0..26].copy_from_slice(withdrawal_key.as_slice());
        let key = H256::from(withdrawal_key_bytes);
        withdrawal_keys.push(withdrawal_key);

        let withdrawal_value = WithdrawalCotaNFTValueBuilder::default()
            .nft_info(hold_value)
            .out_point(OutPointSlice::from_slice(&cota_input_out_point.as_slice()[12..]).unwrap())
            .to(LockHashSlice::from_slice(&to_lock.calc_script_hash().as_slice()[0..20]).unwrap())
            .build();
        let value = H256::from(blake2b_256(withdrawal_value.as_slice()));
        withdrawal_values.push(withdrawal_value.clone());

        withdrawal_smt
            .update(key, value)
            .expect("SMT update leave error");
        update_leaves.push((key, value));
    }

    let root_hash = withdrawal_smt.root().clone();
    let mut root_hash_bytes = [0u8; 32];
    root_hash_bytes.copy_from_slice(root_hash.as_slice());

    let withdrawal_compact_merkle_proof = withdrawal_smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let withdrawal_compact_merkle_proof_compiled = withdrawal_compact_merkle_proof
        .compile(update_leaves.clone())
        .unwrap();

    let verify_result = withdrawal_compact_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "withdrawal smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = withdrawal_compact_merkle_proof_compiled.into();

    (
        root_hash_bytes,
        withdrawal_keys,
        withdrawal_values,
        merkel_proof_vec,
    )
}

fn generate_claimed_cota_nft_smt_data(
    claim_error: ClaimError,
    withdrawal_cota_out_point: OutPoint,
    withdrawal_keys: Vec<CotaNFTId>,
    withdrawal_values: Vec<WithdrawalCotaNFTValue>,
    withdrawal_proof: Vec<u8>,
    claim_count: usize,
) -> ([u8; 32], [u8; 32], Vec<u8>) {
    let claim_smt_type = if claim_error == ClaimError::CoTANFTSmtTypeError {
        DEFINE_NFT_SMT_TYPE
    } else {
        CLAIM_NFT_SMT_TYPE
    };

    let leaves_count = 100;
    let mut smt = SMT::default();
    let mut rng = thread_rng();
    for _ in 0..leaves_count {
        let key: H256 = rng.gen::<[u8; 32]>().into();
        let value: H256 = H256::from([255u8; 32]);
        smt.update(key, value).expect("SMT update leave error");
    }

    let old_smt_root = smt.root().clone();
    let mut old_root_hash_bytes = [0u8; 32];
    old_root_hash_bytes.copy_from_slice(old_smt_root.as_slice());

    let mut hold_keys: Vec<CotaNFTId> = Vec::new();
    let mut hold_values: Vec<CotaNFTInfo> = Vec::new();
    let mut claimed_keys: Vec<ClaimCotaNFTKey> = Vec::new();
    let mut claimed_values: Vec<Byte32> = Vec::new();
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(claim_count * 2);
    for index in 0..claim_count {
        let withdrawal_key = withdrawal_keys.get(index).unwrap().clone();
        let mut hold_key_vec = [0u8; 32];
        hold_key_vec[0..2].copy_from_slice(&HOLD_NFT_SMT_TYPE.to_be_bytes());
        hold_key_vec[2..22].copy_from_slice(withdrawal_key.cota_id().as_slice());
        hold_key_vec[22..26].copy_from_slice(withdrawal_key.index().as_slice());
        let mut key = H256::from(hold_key_vec);
        let hold_key = CotaNFTIdBuilder::default()
            .smt_type(Uint16::from_slice(&HOLD_NFT_SMT_TYPE.to_be_bytes()).unwrap())
            .cota_id(withdrawal_key.cota_id().clone())
            .index(withdrawal_key.index().clone())
            .build();
        hold_keys.push(hold_key);

        let withdrawal_value = withdrawal_values.get(index).unwrap().clone();
        let mut hold_value_vec = [0u8; 32];
        hold_value_vec[0..22].copy_from_slice(withdrawal_value.nft_info().as_slice());
        let mut value: H256 = H256::from(hold_value_vec);
        hold_values.push(withdrawal_value.nft_info().clone());

        update_leaves.push((key, value));
        smt.update(key, value).expect("SMT update leave error");

        let cota_out_point =
            OutPointSlice::from_slice(&withdrawal_cota_out_point.as_slice()[12..36]).unwrap();
        let nft_id = CotaNFTIdBuilder::default()
            .smt_type(Uint16::from_slice(&claim_smt_type.to_be_bytes()).unwrap())
            .cota_id(withdrawal_key.cota_id())
            .index(withdrawal_key.index())
            .build();
        let claimed_key = ClaimCotaNFTKeyBuilder::default()
            .nft_id(nft_id)
            .out_point(cota_out_point)
            .build();
        claimed_keys.push(claimed_key.clone());
        key = H256::from(blake2b_256(claimed_key.as_slice()));

        value = H256::from([255u8; 32]);
        claimed_values.push(
            Byte32Builder::default()
                .set([Byte::from(255u8); 32])
                .build(),
        );

        update_leaves.push((key, value));
        smt.update(key, value).expect("SMT update leave error");
    }
    let root_hash = smt.root().clone();

    let mut root_hash_bytes = [0u8; 32];
    root_hash_bytes.copy_from_slice(root_hash.as_slice());

    let claim_mint_merkle_proof = smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let claim_mint_merkle_proof_compiled = claim_mint_merkle_proof
        .compile(update_leaves.clone())
        .unwrap();
    let verify_result = claim_mint_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");

    assert!(verify_result, "smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = claim_mint_merkle_proof_compiled.into();

    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let withdraw_merkel_proof_bytes = BytesBuilder::default()
        .extend(withdrawal_proof.iter().map(|v| Byte::from(*v)))
        .build();

    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Claim ".as_bytes());
    action_vec.extend((claimed_keys.len() as u32).to_be_bytes());
    action_vec.extend(" NFTs".as_bytes());

    if claim_error == ClaimError::CoTANFTActionError {
        action_vec.reverse();
    }

    let action_bytes = BytesBuilder::default()
        .set(action_vec.iter().map(|v| Byte::from(*v)).collect())
        .build();

    let claim_entries = ClaimCotaNFTEntriesBuilder::default()
        .hold_keys(HoldCotaNFTKeyVecBuilder::default().set(hold_keys).build())
        .hold_values(
            HoldCotaNFTValueVecBuilder::default()
                .set(hold_values)
                .build(),
        )
        .claim_keys(
            ClaimCotaNFTKeyVecBuilder::default()
                .set(claimed_keys)
                .build(),
        )
        .claim_values(
            ClaimCotaNFTValueVecBuilder::default()
                .set(claimed_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .action(action_bytes)
        .withdrawal_proof(withdraw_merkel_proof_bytes)
        .build();

    (
        old_root_hash_bytes,
        root_hash_bytes,
        Vec::from(claim_entries.as_slice()),
    )
}

fn create_test_context(claim_error: ClaimError) -> (Context, TransactionView) {
    let mut context = Context::default();
    let cota_bin: Bytes = Loader::default().load_binary("cota-type");
    let cota_out_point = context.deploy_cell(cota_bin);
    let cota_type_script_dep = CellDepBuilder::default()
        .out_point(cota_out_point.clone())
        .build();

    let smt_bin: Bytes = Loader::default().load_binary("ckb_smt");
    let smt_out_point = context.deploy_cell(smt_bin);
    let smt_dep = CellDepBuilder::default().out_point(smt_out_point).build();

    // deploy always_success script
    let always_success_out_point = context.deploy_cell(ALWAYS_SUCCESS.clone());

    // prepare scripts
    let lock_script = context
        .build_script(
            &always_success_out_point,
            Bytes::from(hex::decode("157a3633c3477d84b604a25e5fca5ca681762c10").unwrap()),
        )
        .expect("script");
    let lock_hash = blake2b_256(lock_script.as_slice());
    let mut lock_hash_160_bytes = [Byte::from(0u8); 20];
    lock_hash_160_bytes.copy_from_slice(
        &lock_hash.clone()[0..20]
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>(),
    );
    let lock_hash_160 = lock_hash[0..20].to_vec();

    let lock_script_dep = CellDepBuilder::default()
        .out_point(always_success_out_point)
        .build();

    let cota_type_args = Bytes::from(lock_hash_160);
    let cota_type_script = context
        .build_script(&cota_out_point, cota_type_args)
        .expect("script");

    let mut withdraw_cell_dep_script = cota_type_script.clone();

    if claim_error == ClaimError::CoTANFTWithdrawalDepError {
        withdraw_cell_dep_script = cota_type_script
            .clone()
            .as_builder()
            .hash_type(Byte::from(1u8))
            .build()
    };

    let cota_input_out_point = random_out_point();

    let (withdraw_smt_root, withdraw_keys, withdraw_values, withdraw_smt_proof) =
        generate_withdrawal_cota_nft_smt_data(cota_input_out_point.clone(), lock_script.clone(), 2);

    let withdraw_cell_data = {
        let mut data = vec![0u8];
        data.extend(&withdraw_smt_root[..]);
        Bytes::from(data)
    };

    let withdraw_out_point = context.create_cell(
        CellOutput::new_builder()
            .capacity(500u64.pack())
            .lock(lock_script.clone())
            .type_(Some(withdraw_cell_dep_script.clone()).pack())
            .build(),
        withdraw_cell_data.clone(),
    );

    let withdraw_cell_dep = CellDepBuilder::default()
        .out_point(withdraw_out_point)
        .build();

    let withdraw_nft_smt_proof = if claim_error == ClaimError::ClaimedCoTAWithdrawalSMTVerifyFailed
    {
        withdraw_smt_proof[1..].to_vec()
    } else {
        withdraw_smt_proof.to_vec()
    };
    let (old_root_hash, root_hash, witness_data) = generate_claimed_cota_nft_smt_data(
        claim_error,
        cota_input_out_point.clone(),
        withdraw_keys,
        withdraw_values,
        withdraw_nft_smt_proof,
        2,
    );

    let mut compact_nft_data_vec: Vec<u8> = vec![];
    let version = [0u8];
    compact_nft_data_vec.extend(&version);
    compact_nft_data_vec.extend(&old_root_hash[..]);

    context.create_cell_with_out_point(
        cota_input_out_point.clone(),
        CellOutput::new_builder()
            .capacity(500u64.pack())
            .lock(lock_script.clone())
            .type_(Some(cota_type_script.clone()).pack())
            .build(),
        Bytes::from(compact_nft_data_vec),
    );

    let compact_nft_input = CellInput::new_builder()
        .previous_output(cota_input_out_point.clone())
        .build();

    let inputs = vec![compact_nft_input.clone()];

    let outputs = vec![CellOutput::new_builder()
        .capacity(500u64.pack())
        .lock(lock_script.clone())
        .type_(Some(cota_type_script.clone()).pack())
        .build()];

    let outputs_data: Vec<Bytes> = match claim_error {
        ClaimError::SMTProofVerifyFailed => vec![Bytes::from(
            hex::decode("0054dfaba38275883ef9b6d5fb02053b71dbba19630ff5f2ec01d5d6965366c1f7")
                .unwrap(),
        )],
        _ => {
            let mut data_vec = vec![];
            let version = [0u8];
            data_vec.extend(&version);
            data_vec.extend(&root_hash[..]);
            vec![Bytes::from(data_vec)]
        }
    };

    let mut witness_data_vec = vec![];
    witness_data_vec.extend(&[CLAIM_COTA]);
    witness_data_vec.extend(&witness_data);
    let witness_args = WitnessArgsBuilder::default()
        .input_type(Some(Bytes::from(witness_data_vec)).pack())
        .build();

    let witnesses = vec![witness_args.as_bytes()];

    let cell_deps = vec![
        withdraw_cell_dep,
        lock_script_dep,
        cota_type_script_dep,
        smt_dep,
    ];

    // build transaction
    let tx = TransactionBuilder::default()
        .inputs(inputs)
        .outputs(outputs)
        .outputs_data(outputs_data.pack())
        .cell_deps(cell_deps)
        .witnesses(witnesses.pack())
        .build();
    (context, tx)
}

#[test]
fn test_claim_cota_cell_success() {
    let (mut context, tx) = create_test_context(ClaimError::NoError);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_claim_cota_smt_proof_verify_error() {
    let (mut context, tx) = create_test_context(ClaimError::SMTProofVerifyFailed);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, SMT_PROOF_VERIFY_FAILED);
}

#[test]
fn test_cota_withdrawal_smt_proof_verify_error() {
    let (mut context, tx) = create_test_context(ClaimError::ClaimedCoTAWithdrawalSMTVerifyFailed);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, CLAIMED_COTA_WITHDRAWAL_SMT_VERIFY_FAILED);
}

#[test]
fn test_cota_withdraw_dep_error() {
    let (mut context, tx) = create_test_context(ClaimError::CoTANFTWithdrawalDepError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_WITHDRAW_DEP_ERROR);
}

#[test]
fn test_withdraw_cota_smt_type_error() {
    let (mut context, tx) = create_test_context(ClaimError::CoTANFTSmtTypeError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_SMT_TYPE_ERROR);
}

#[test]
fn test_withdraw_cota_action_error() {
    let (mut context, tx) = create_test_context(ClaimError::CoTANFTActionError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_ACTION_ERROR);
}
