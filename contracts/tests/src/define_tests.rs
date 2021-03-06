use crate::constants::{BYTE32_ZEROS, DEFINE_NFT_SMT_TYPE, HOLD_NFT_SMT_TYPE};
use crate::{assert_script_error, Loader};
use blake2b_rs::Blake2bBuilder;
use ckb_testtool::ckb_types::{
    bytes::Bytes,
    core::{TransactionBuilder, TransactionView},
    packed::*,
    prelude::*,
};
use ckb_testtool::context::random_out_point;
use ckb_testtool::{builtin::ALWAYS_SUCCESS, context::Context};
use cota_smt::define::DefineCotaNFTEntriesBuilder;
use cota_smt::{
    common::{BytesBuilder, Uint16, Uint32, *},
    smt::{Blake2bHasher, H256, SMT},
};
use rand::{thread_rng, Rng};

const MAX_CYCLES: u64 = 70_000_000;

// error numbers
const WITNESS_TYPE_PARSE_ERROR: i8 = 8;
const SMT_PROOF_VERIFY_FAILED: i8 = 9;
const COTA_CELLS_COUNT_ERROR: i8 = 16;
const COTA_TYPE_ARGS_NOT_EQUAL_LOCK_HASH: i8 = 18;
const COTA_DATA_INVALID: i8 = 19;
const COTA_CELL_SMT_ROOT_ERROR: i8 = 20;
const COTA_DEFINE_ISSUED_ERROR: i8 = 21;
const COTA_NFT_SMT_TYPE_ERROR: i8 = 23;
const COTA_NFT_ACTION_ERROR: i8 = 24;
const COTA_CELL_LOCK_NOT_SAME: i8 = 25;
const COTA_ID_INVALID: i8 = 26;
const COTA_CELL_DATA_NOT_SAME: i8 = 39;

#[derive(PartialEq, Copy, Clone)]
enum DefineError {
    NoError,
    UnlimitedTotal,
    WitnessTypeParseError,
    SMTProofVerifyFailed,
    CoTACellsCountError,
    CoTATypeArgsNotEqualLockHash,
    CoTADataInvalid,
    CoTACellSMTRootError,
    CoTADefineIssuedError,
    CoTANFTSmtTypeError,
    CoTANFTActionError,
    CoTACellLockNotSame,
    CoTAIdInvalid,
    CoTACellDataNotSame,
}

const DEFINE_COTA: u8 = 1;

fn generate_define_cota_nft_smt_data(
    define_error: DefineError,
    first_input: CellInput,
    define_count: usize,
) -> ([u8; 32], [u8; 32], Vec<u8>) {
    if define_count > 1 {
        panic!("define count should be 1");
    }
    let mut blake2b = Blake2bBuilder::new(32)
        .personal(b"ckb-default-hash")
        .build();
    blake2b.update(first_input.as_slice());
    blake2b.update(&[0u8]);
    let mut ret = [0; 32];
    blake2b.finalize(&mut ret);

    let mut cota_id = [0u8; 20];
    if define_error == DefineError::CoTAIdInvalid {
        cota_id.copy_from_slice(&ret[10..30]);
    } else {
        cota_id.copy_from_slice(&ret[0..20]);
    }

    let total_vec = if define_error == DefineError::UnlimitedTotal {
        [0u8, 0u8, 0u8, 0u8]
    } else {
        [0u8, 0u8, 0u8, 100u8]
    };
    let issued_vec = if define_error == DefineError::CoTADefineIssuedError {
        [0u8, 0u8, 0u8, 100u8]
    } else {
        [0u8, 0u8, 0u8, 0u8]
    };

    let leaves_count = 100;
    let mut define_smt = SMT::default();

    let mut rng = thread_rng();
    for _ in 0..leaves_count {
        let key: H256 = rng.gen::<[u8; 32]>().into();
        let value: H256 = H256::from([255u8; 32]);
        define_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let old_smt_root = define_smt.root().clone();
    let mut old_root_hash_bytes = [0u8; 32];
    old_root_hash_bytes.copy_from_slice(old_smt_root.as_slice());

    let mut define_keys: Vec<DefineCotaNFTId> = Vec::new();
    let mut define_values: Vec<DefineCotaNFTValue> = Vec::new();
    let mut update_old_leaves: Vec<(H256, H256)> = Vec::with_capacity(define_count);
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(define_count);

    let define_smt_type = if define_error == DefineError::CoTANFTSmtTypeError {
        HOLD_NFT_SMT_TYPE
    } else {
        DEFINE_NFT_SMT_TYPE
    };
    for _ in 0..define_count {
        let cota_nft_id = CotaId::from_slice(&cota_id).unwrap();
        let smt_type = Uint16::from_slice(&define_smt_type.to_be_bytes()).unwrap();
        let define_key = DefineCotaNFTIdBuilder::default()
            .cota_id(cota_nft_id)
            .smt_type(smt_type)
            .build();

        define_keys.push(define_key.clone());

        let mut define_key_bytes = [0u8; 32];
        define_key_bytes[0..22].copy_from_slice(define_key.as_slice());

        let key = H256::from(define_key_bytes);

        let define_value = DefineCotaNFTValueBuilder::default()
            .total(Uint32::from_slice(&total_vec).unwrap())
            .issued(Uint32::from_slice(&issued_vec).unwrap())
            .configure(Byte::from(3))
            .build();

        let mut define_cota_bytes = [0u8; 32];
        define_cota_bytes[0..9].copy_from_slice(define_value.as_slice());
        let value = H256::from(define_cota_bytes);

        define_values.push(define_value.clone());
        update_leaves.push((key, value));
        update_old_leaves.push((key, H256::from(BYTE32_ZEROS)));
        define_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let root_hash = define_smt.root().clone();
    let mut root_hash_bytes = [0u8; 32];
    root_hash_bytes.copy_from_slice(root_hash.as_slice());

    let define_cota_merkle_proof = define_smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let define_cota_merkle_proof_compiled = define_cota_merkle_proof
        .clone()
        .compile(update_leaves.clone())
        .unwrap();
    let verify_result = define_cota_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "smt proof verify failed");

    let verify_old_leaves_result = define_cota_merkle_proof_compiled
        .verify::<Blake2bHasher>(&old_smt_root, update_old_leaves.clone())
        .expect("old smt proof verify failed");
    assert!(verify_old_leaves_result, "old smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = define_cota_merkle_proof_compiled.into();
    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Create a new NFT collection with ".as_bytes());
    let define_total = if define_error == DefineError::UnlimitedTotal {
        "unlimited".as_bytes()
    } else {
        &[0, 0, 0, 100u8]
    };
    action_vec.extend(define_total);
    action_vec.extend(" edition".as_bytes());
    if define_error == DefineError::CoTANFTActionError {
        action_vec.reverse();
    }
    let action_bytes = BytesBuilder::default()
        .set(action_vec.iter().map(|v| Byte::from(*v)).collect())
        .build();

    let define_entries = DefineCotaNFTEntriesBuilder::default()
        .define_keys(
            DefineCotaNFTKeyVecBuilder::default()
                .set(define_keys)
                .build(),
        )
        .define_values(
            DefineCotaNFTValueVecBuilder::default()
                .set(define_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .action(action_bytes)
        .build();

    (
        old_root_hash_bytes,
        root_hash_bytes,
        Vec::from(define_entries.as_slice()),
    )
}

fn create_test_context(define_error: DefineError) -> (Context, TransactionView) {
    // deploy cota-type script
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
    let lock_hash = lock_script.calc_script_hash().as_bytes();
    let lock_hash_160_vec = if define_error == DefineError::CoTATypeArgsNotEqualLockHash {
        &lock_hash[10..30]
    } else {
        &lock_hash[0..20]
    };

    let to_lock_script = context
        .build_script(
            &always_success_out_point,
            Bytes::from(hex::decode("7164f48d7a5bf2298166f8d81b81ea4e908e16ad").unwrap()),
        )
        .expect("script");

    let lock_script_dep = CellDepBuilder::default()
        .out_point(always_success_out_point)
        .build();

    let cota_input_out_point = random_out_point();
    let define_cota_nft_input = CellInput::new_builder()
        .previous_output(cota_input_out_point.clone())
        .build();

    let cota_type_script = context
        .build_script(&cota_out_point, Bytes::copy_from_slice(lock_hash_160_vec))
        .expect("script");

    let (old_root_hash, root_hash, witness_data) =
        generate_define_cota_nft_smt_data(define_error, define_cota_nft_input.clone(), 1);

    let mut cota_nft_data_vec: Vec<u8> = vec![];
    let version = [0u8];
    cota_nft_data_vec.extend(&version);
    cota_nft_data_vec.extend(&old_root_hash[..]);

    context.create_cell_with_out_point(
        cota_input_out_point.clone(),
        CellOutput::new_builder()
            .capacity(500u64.pack())
            .lock(lock_script.clone())
            .type_(Some(cota_type_script.clone()).pack())
            .build(),
        Bytes::from(cota_nft_data_vec),
    );

    let define_cota_nft_input = CellInput::new_builder()
        .previous_output(cota_input_out_point.clone())
        .build();

    let inputs = vec![define_cota_nft_input.clone()];

    let cota_type_opt: ScriptOpt = if define_error == DefineError::CoTACellsCountError {
        ScriptOptBuilder::default().set(None).build()
    } else {
        Some(cota_type_script.clone()).pack()
    };

    let output_lock_script = if define_error == DefineError::CoTACellLockNotSame {
        to_lock_script.clone()
    } else {
        lock_script.clone()
    };
    let outputs = vec![CellOutput::new_builder()
        .capacity(500u64.pack())
        .lock(output_lock_script)
        .type_(cota_type_opt)
        .build()];

    let outputs_data: Vec<Bytes> = match define_error {
        DefineError::SMTProofVerifyFailed => vec![Bytes::from(
            hex::decode("0054dfaba38275883ef9b6d5fb02053b71dbba19630ff5f2ec01d5d6965366c1f7")
                .unwrap(),
        )],
        DefineError::CoTADataInvalid => vec![Bytes::from(hex::decode("001234").unwrap())],
        DefineError::CoTACellSMTRootError => {
            let mut data_vec = vec![];
            let version = [0u8];
            data_vec.extend(&version);
            vec![Bytes::from(data_vec)]
        }
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
    witness_data_vec.extend(&[DEFINE_COTA]);
    witness_data_vec.extend(&witness_data);
    let witness_args = WitnessArgsBuilder::default()
        .input_type(Some(Bytes::from(witness_data_vec)).pack())
        .build();

    let witnesses = match define_error {
        DefineError::WitnessTypeParseError => vec![error_witness_args.as_bytes()],
        DefineError::CoTACellDataNotSame => vec![WitnessArgsBuilder::default().build().as_bytes()],
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
fn test_define_cota_nft_cell_success() {
    let (mut context, tx) = create_test_context(DefineError::NoError);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_define_cota_nft_cell_with_unlimited_total_success() {
    let (mut context, tx) = create_test_context(DefineError::UnlimitedTotal);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_define_cota_smt_proof_verify_error() {
    let (mut context, tx) = create_test_context(DefineError::SMTProofVerifyFailed);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, SMT_PROOF_VERIFY_FAILED);
}

#[test]
fn test_define_cota_nft_witness_type_parse_error() {
    let (mut context, tx) = create_test_context(DefineError::WitnessTypeParseError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, WITNESS_TYPE_PARSE_ERROR);
}

#[test]
fn test_define_cota_nft_smt_root_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTACellSMTRootError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_CELL_SMT_ROOT_ERROR);
}

#[test]
fn test_define_cota_nft_smt_type_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTANFTSmtTypeError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_SMT_TYPE_ERROR);
}

#[test]
fn test_define_destroy_cota_cell_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTACellsCountError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_CELLS_COUNT_ERROR);
}

#[test]
fn test_define_cota_type_args_not_equal_lock_hash_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTATypeArgsNotEqualLockHash);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_TYPE_ARGS_NOT_EQUAL_LOCK_HASH);
}

#[test]
fn test_define_cota_data_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTADataInvalid);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_DATA_INVALID);
}

#[test]
fn test_define_cota_issued_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTADefineIssuedError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_DEFINE_ISSUED_ERROR);
}

#[test]
fn test_define_cota_action_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTANFTActionError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_ACTION_ERROR);
}

#[test]
fn test_define_cota_lock_not_same_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTACellLockNotSame);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_CELL_LOCK_NOT_SAME);
}

#[test]
fn test_define_cota_id_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTAIdInvalid);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_ID_INVALID);
}

#[test]
fn test_cota_cell_data_not_same_error() {
    let (mut context, tx) = create_test_context(DefineError::CoTACellDataNotSame);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_CELL_DATA_NOT_SAME);
}
