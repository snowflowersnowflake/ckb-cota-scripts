use crate::constants::{DEFINE_NFT_SMT_TYPE, HOLD_NFT_SMT_TYPE};
use crate::{assert_script_error, Loader};
use ckb_testtool::ckb_types::{
    bytes::Bytes,
    core::{TransactionBuilder, TransactionView},
    packed::*,
    prelude::*,
};
use ckb_testtool::context::random_out_point;
use ckb_testtool::{builtin::ALWAYS_SUCCESS, context::Context};
use cota_smt::{
    common::{BytesBuilder, Uint16, Uint32, *},
    smt::{Blake2bHasher, H256, SMT},
    update::*,
};
use rand::{thread_rng, Rng};

const MAX_CYCLES: u64 = 70_000_000;

// error numbers
const WITNESS_TYPE_PARSE_ERROR: i8 = 8;
const SMT_PROOF_VERIFY_FAILED: i8 = 9;
const COTA_IMMUTABLE_FIELDS_ERROR: i8 = 22;
const COTA_NFT_SMT_TYPE_ERROR: i8 = 23;
const COTA_NFT_ACTION_ERROR: i8 = 24;
const COTA_LOCKED_NFT_CANNOT_UPDATE_INFO: i8 = 35;
const COTA_LOCKED_NFT_CANNOT_CLAIM: i8 = 36;
const COTA_NFT_CLAIM_ERROR: i8 = 37;
const COTA_NFT_LOCK_ERROR: i8 = 38;

#[derive(PartialEq, Copy, Clone)]
enum UpdateError {
    NoError,
    WitnessTypeParseError,
    SMTProofVerifyFailed,
    CoTAImmutableFieldsError,
    CoTANFTSmtTypeError,
    CoTANFTActionError,
    CoTALockedNFTCannotUpdateInfo,
    CoTALockedNFTCannotClaim,
    CoTANFTClaimError,
    CoTANFTLockError,
}

const UPDATE_COTA: u8 = 5;

fn generator_hold_value(is_new: bool, update_error: UpdateError) -> (H256, CotaNFTInfo) {
    let mut char = 0u8;
    let mut configure = 0u8;
    let mut state = 0u8;

    match update_error {
        UpdateError::CoTAImmutableFieldsError => {
            if is_new {
                configure = 0;
            } else {
                configure = 1;
            }
        }
        UpdateError::CoTALockedNFTCannotUpdateInfo => {
            state = 2;
            if is_new {
                char = 10;
            } else {
                char = 5;
            }
        }
        UpdateError::CoTALockedNFTCannotClaim => {
            if is_new {
                state = 3;
            } else {
                state = 2;
            }
        }
        UpdateError::CoTANFTLockError => {
            configure = 2;
            if is_new {
                state = 2;
            } else {
                state = 0;
            }
        }
        UpdateError::CoTANFTClaimError => {
            if is_new {
                state = 0;
            } else {
                state = 1;
            }
        }
        _ => {
            if is_new {
                char = 10u8;
            } else {
                char = 5u8;
            }
        }
    }
    let nft_info = CotaNFTInfoBuilder::default()
        .characteristic(Characteristic::from_slice(&[char; 20]).unwrap())
        .configure(Byte::from(configure))
        .state(Byte::from(state))
        .build();
    let mut nft_info_bytes = [0u8; 32];
    nft_info_bytes[0..22].copy_from_slice(nft_info.as_slice());
    (H256::from(nft_info_bytes), nft_info)
}

fn generate_update_cota_smt_data(
    update_error: UpdateError,
    update_count: usize,
) -> ([u8; 32], [u8; 32], Vec<u8>) {
    let leaves_count = 100;
    let mut before_update_smt = SMT::default();
    let mut after_update_smt = SMT::default();

    let mut rng = thread_rng();
    for _ in 0..leaves_count {
        let key: H256 = rng.gen::<[u8; 32]>().into();
        let value: H256 = H256::from([255u8; 32]);
        before_update_smt
            .update(key, value)
            .expect("SMT update leave error");
        after_update_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let cota_id_vec: Vec<u8> = hex::decode("157a3633c3477d84b604a25e5fca5ca681762c10").unwrap();

    let hold_smt_type = if update_error == UpdateError::CoTANFTSmtTypeError {
        DEFINE_NFT_SMT_TYPE
    } else {
        HOLD_NFT_SMT_TYPE
    };

    let mut hold_keys: Vec<CotaNFTId> = Vec::new();
    let mut hold_old_values: Vec<CotaNFTInfo> = Vec::new();
    let mut hold_new_values: Vec<CotaNFTInfo> = Vec::new();
    let mut old_update_leaves: Vec<(H256, H256)> = Vec::with_capacity(update_count);
    let mut new_update_leaves: Vec<(H256, H256)> = Vec::with_capacity(update_count);

    for index in 0..update_count {
        let token_index = Uint32::from_slice(&[0, 0, 0, index as u8]).unwrap();
        let hold_key = CotaNFTIdBuilder::default()
            .cota_id(CotaId::from_slice(&cota_id_vec).unwrap())
            .index(token_index)
            .smt_type(Uint16::from_slice(&hold_smt_type.to_be_bytes()).unwrap())
            .build();
        let mut hold_key_bytes = [0u8; 32];
        hold_key_bytes[0..26].copy_from_slice(hold_key.as_slice());
        let key = H256::from(hold_key_bytes);
        hold_keys.push(hold_key);

        let (value, old_nft_info) = generator_hold_value(false, update_error);
        hold_old_values.push(old_nft_info.clone());
        old_update_leaves.push((key, value));
        before_update_smt
            .update(key, value)
            .expect("SMT update leave error");

        let (value, new_nft_info) = generator_hold_value(true, update_error);
        hold_new_values.push(new_nft_info.clone());
        new_update_leaves.push((key, value));
        after_update_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let old_smt_root = before_update_smt.root().clone();
    let mut old_root_hash_bytes = [0u8; 32];
    old_root_hash_bytes.copy_from_slice(old_smt_root.as_slice());

    let root_hash = after_update_smt.root().clone();
    let mut root_hash_bytes = [0u8; 32];
    root_hash_bytes.copy_from_slice(root_hash.as_slice());

    let update_info_merkle_proof = after_update_smt
        .merkle_proof(old_update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let update_info_merkle_proof_compiled = update_info_merkle_proof
        .compile(old_update_leaves.clone())
        .unwrap();
    let verify_result = update_info_merkle_proof_compiled
        .verify::<Blake2bHasher>(&old_smt_root, old_update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "before updating smt proof verify failed");

    let verify_result = update_info_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, new_update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "after updating smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = update_info_merkle_proof_compiled.into();
    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let action_vec = if update_error == UpdateError::CoTANFTActionError {
        "Update NFT information error".as_bytes().to_vec()
    } else {
        "Update NFT information".as_bytes().to_vec()
    };
    let action_bytes = BytesBuilder::default()
        .set(action_vec.iter().map(|v| Byte::from(*v)).collect())
        .build();

    let update_entries = UpdateCotaNFTEntriesBuilder::default()
        .hold_keys(
            HoldCotaNFTKeyVecBuilder::default()
                .extend(hold_keys)
                .build(),
        )
        .hold_old_values(
            HoldCotaNFTValueVecBuilder::default()
                .extend(hold_old_values)
                .build(),
        )
        .hold_new_values(
            HoldCotaNFTValueVecBuilder::default()
                .extend(hold_new_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .action(action_bytes)
        .build();

    (
        old_root_hash_bytes,
        root_hash_bytes,
        Vec::from(update_entries.as_slice()),
    )
}

fn create_test_context(update_error: UpdateError) -> (Context, TransactionView) {
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
    let lock_hash_160_vec = &lock_script.calc_script_hash().as_bytes()[0..20];

    let lock_script_dep = CellDepBuilder::default()
        .out_point(always_success_out_point)
        .build();

    // prepare cells
    let cota_type_script = context
        .build_script(&cota_out_point, Bytes::copy_from_slice(lock_hash_160_vec))
        .expect("script");

    let (old_root_hash, root_hash, witness_data) = generate_update_cota_smt_data(update_error, 5);

    let mut cota_data_vec: Vec<u8> = vec![];
    let version = [0u8];
    cota_data_vec.extend(&version);
    cota_data_vec.extend(&old_root_hash[..]);

    let cota_input_out_point = random_out_point();
    context.create_cell_with_out_point(
        cota_input_out_point.clone(),
        CellOutput::new_builder()
            .capacity(500u64.pack())
            .lock(lock_script.clone())
            .type_(Some(cota_type_script.clone()).pack())
            .build(),
        Bytes::from(cota_data_vec),
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

    let outputs_data: Vec<Bytes> = match update_error {
        UpdateError::SMTProofVerifyFailed => vec![Bytes::from(
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

    let error_witness_args = WitnessArgsBuilder::default()
        .input_type(
            Some(Bytes::from(
                hex::decode("0154dfaba38275883ef9b6d5fb02053b71dbba19630ff5f2ec01d5d6965366c1f7")
                    .unwrap(),
            ))
            .pack(),
        )
        .build();

    let mut witness_data_vec = vec![];
    witness_data_vec.extend(&[UPDATE_COTA]);
    witness_data_vec.extend(&witness_data);
    let witness_args = WitnessArgsBuilder::default()
        .input_type(Some(Bytes::from(witness_data_vec)).pack())
        .build();

    let witnesses = match update_error {
        UpdateError::WitnessTypeParseError => vec![error_witness_args.as_bytes()],
        _ => vec![witness_args.as_bytes()],
    };

    let cell_deps = vec![lock_script_dep, cota_type_script_dep, smt_dep];

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
fn test_update_cota_nft_success() {
    let (mut context, tx) = create_test_context(UpdateError::NoError);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_update_cota_smt_proof_verify_error() {
    let (mut context, tx) = create_test_context(UpdateError::SMTProofVerifyFailed);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, SMT_PROOF_VERIFY_FAILED);
}

#[test]
fn test_update_cota_witness_type_parse_error() {
    let (mut context, tx) = create_test_context(UpdateError::WitnessTypeParseError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, WITNESS_TYPE_PARSE_ERROR);
}

#[test]
fn test_update_cota_nft_smt_type_error() {
    let (mut context, tx) = create_test_context(UpdateError::CoTANFTSmtTypeError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_SMT_TYPE_ERROR);
}

#[test]
fn test_update_locked_cota_nft_cannot_update_info_error() {
    let (mut context, tx) = create_test_context(UpdateError::CoTALockedNFTCannotUpdateInfo);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_LOCKED_NFT_CANNOT_UPDATE_INFO);
}

#[test]
fn test_update_cota_nft_locked_error() {
    let (mut context, tx) = create_test_context(UpdateError::CoTANFTLockError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_LOCK_ERROR);
}

#[test]
fn test_update_cota_nft_claim_error() {
    let (mut context, tx) = create_test_context(UpdateError::CoTANFTClaimError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_CLAIM_ERROR);
}

#[test]
fn test_update_cota_nft_immutable_fields_error() {
    let (mut context, tx) = create_test_context(UpdateError::CoTAImmutableFieldsError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_IMMUTABLE_FIELDS_ERROR);
}

#[test]
fn test_update_cota_nft_locked_cannot_claim_error() {
    let (mut context, tx) = create_test_context(UpdateError::CoTALockedNFTCannotClaim);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_LOCKED_NFT_CANNOT_CLAIM);
}

#[test]
fn test_update_cota_nft_action_error() {
    let (mut context, tx) = create_test_context(UpdateError::CoTANFTActionError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_ACTION_ERROR);
}
