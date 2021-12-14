use crate::constants::{
    BYTE10_ZEROS, BYTE23_ZEROS, BYTE32_ZEROS, BYTE6_ZEROS, DEFINE_NFT_SMT_TYPE, HOLD_NFT_SMT_TYPE,
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
use cota_smt::mint::MintCotaNFTEntriesBuilder;
use cota_smt::smt::blake2b_256;
use cota_smt::{
    common::{BytesBuilder, Uint16Builder, Uint32Builder, *},
    smt::{Blake2bHasher, H256, SMT},
};
use rand::{thread_rng, Rng};

const MAX_CYCLES: u64 = 70_000_000;

// error numbers
const WITNESS_TYPE_PARSE_ERROR: i8 = 8;
const SMT_PROOF_VERIFY_FAILED: i8 = 9;
const COTA_DEFINE_ISSUED_ERROR: i8 = 21;
const COTA_IMMUTABLE_FIELDS_ERROR: i8 = 22;
const COTA_NFT_SMT_TYPE_ERROR: i8 = 23;
const COTA_NFT_ACTION_ERROR: i8 = 24;
const COTA_NFT_TOKEN_INDEX_ERROR: i8 = 27;
const COTA_OUT_POINT_ERROR: i8 = 28;

#[derive(PartialEq, Copy, Clone)]
enum WithdrawalError {
    NoError,
    SingleAction,
    WitnessTypeParseError,
    SMTProofVerifyFailed,
    CoTADefineIssuedError,
    CoTAImmutableFieldsError,
    CoTANFTSmtTypeError,
    CoTANFTActionError,
    CoTANFTTokenIndexError,
    CoTAOutPointError,
}

const MINT_COTA: u8 = 2;

fn generate_mint_cota_nft_smt_data(
    withdrawal_error: WithdrawalError,
    out_point: OutPoint,
    to_lock: Script,
    withdrawal_count: usize,
) -> ([u8; 32], [u8; 32], Vec<u8>) {
    let mut define_smt_type = [Byte::from(0); 2];
    define_smt_type.copy_from_slice(
        &DEFINE_NFT_SMT_TYPE
            .to_be_bytes()
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>(),
    );

    let mut withdrawal_smt_type = [Byte::from(0); 2];
    let smt_type = if withdrawal_error == WithdrawalError::CoTANFTSmtTypeError {
        HOLD_NFT_SMT_TYPE
    } else {
        WITHDRAWAL_NFT_SMT_TYPE
    };
    withdrawal_smt_type.copy_from_slice(
        &smt_type
            .to_be_bytes()
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>(),
    );

    let total_bytes = [Byte::from(0), Byte::from(0), Byte::from(0), Byte::from(100)];
    let old_issued_bytes = [Byte::from(0), Byte::from(0), Byte::from(0), Byte::from(25)];
    let new_issued_bytes = match withdrawal_error {
        WithdrawalError::CoTADefineIssuedError => {
            [Byte::from(0), Byte::from(0), Byte::from(0), Byte::from(30)]
        }
        WithdrawalError::CoTANFTActionError | WithdrawalError::SingleAction => {
            [Byte::from(0), Byte::from(0), Byte::from(0), Byte::from(26)]
        }
        _ => [Byte::from(0), Byte::from(0), Byte::from(0), Byte::from(35)],
    };
    let characteristic_bytes: Vec<Byte> = [5u8; 20].iter().map(|v| Byte::from(*v)).collect();
    let mut characteristic: [Byte; 20] = [Byte::from(0); 20];
    characteristic.copy_from_slice(&characteristic_bytes);

    let leaves_count = 100;
    let mut mint_new_smt = SMT::default();
    let mut mint_old_smt = SMT::default();

    let mut rng = thread_rng();
    for _ in 0..leaves_count {
        let key: H256 = rng.gen::<[u8; 32]>().into();
        let value: H256 = H256::from([255u8; 32]);
        mint_new_smt
            .update(key, value)
            .expect("SMT update leave error");
        mint_old_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let mut define_keys: Vec<DefineCotaNFTId> = Vec::new();
    let mut define_old_values: Vec<DefineCotaNFTValue> = Vec::new();
    let mut define_new_values: Vec<DefineCotaNFTValue> = Vec::new();
    let mut withdrawal_keys: Vec<CotaNFTId> = Vec::new();
    let mut withdrawal_values: Vec<WithdrawalCotaNFTValue> = Vec::new();
    let mut update_old_leaves: Vec<(H256, H256)> = Vec::with_capacity(withdrawal_count + 1);
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(withdrawal_count + 1);

    let cota_id_vec: Vec<u8> = hex::decode("157a3633c3477d84b604a25e5fca5ca681762c10").unwrap();
    let cota_id_bytes: Vec<Byte> = cota_id_vec.iter().map(|v| Byte::from(*v)).collect();
    let mut cota_id: [Byte; 20] = [Byte::from(0); 20];
    cota_id.copy_from_slice(&cota_id_bytes);
    let smt_type = Uint16Builder::default().set(define_smt_type).build();
    let define_key = DefineCotaNFTIdBuilder::default()
        .cota_id(CotaIdBuilder::default().set(cota_id).build())
        .smt_type(smt_type)
        .build();
    define_keys.push(define_key.clone());

    let mut define_key_vec = Vec::new();
    define_key_vec.extend(define_key.as_slice());
    define_key_vec.extend(&BYTE10_ZEROS);
    let mut define_key_bytes = [0u8; 32];
    define_key_bytes.copy_from_slice(&define_key_vec);

    let key = H256::from(define_key_bytes);

    let define_old_value = DefineCotaNFTValueBuilder::default()
        .total(Uint32Builder::default().set(total_bytes).build())
        .issued(Uint32Builder::default().set(old_issued_bytes).build())
        .configure(Byte::from(3))
        .build();
    let mut define_cota_info_vec = Vec::new();
    define_cota_info_vec.extend(define_old_value.as_slice());
    define_cota_info_vec.extend(&BYTE23_ZEROS);
    let mut define_cota_bytes = [0u8; 32];
    define_cota_bytes.copy_from_slice(&define_cota_info_vec);
    let old_value = H256::from(define_cota_bytes);
    define_old_values.push(define_old_value);
    update_old_leaves.push((key, old_value));

    let define_new_value = DefineCotaNFTValueBuilder::default()
        .total(Uint32Builder::default().set(total_bytes).build())
        .issued(Uint32Builder::default().set(new_issued_bytes).build())
        .configure(Byte::from(3))
        .build();
    let mut define_cota_info_vec = Vec::new();
    define_cota_info_vec.extend(define_new_value.as_slice());
    define_cota_info_vec.extend(&BYTE23_ZEROS);
    let mut define_cota_bytes = [0u8; 32];
    define_cota_bytes.copy_from_slice(&define_cota_info_vec);
    let new_value = H256::from(define_cota_bytes);

    define_new_values.push(define_new_value);
    update_leaves.push((key, new_value));

    mint_old_smt
        .update(key, old_value)
        .expect("SMT update leave error");
    mint_new_smt
        .update(key, new_value)
        .expect("SMT update leave error");

    let mut out_point_bytes = [Byte::from(0); 24];
    out_point_bytes.copy_from_slice(
        &out_point.as_slice()[12..]
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>(),
    );

    let mut to_lock_bytes = [Byte::from(0); 20];
    to_lock_bytes.copy_from_slice(
        &to_lock.calc_script_hash().as_slice()[0..20]
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>(),
    );

    let issued_base = if withdrawal_error == WithdrawalError::CoTANFTTokenIndexError {
        10u8
    } else {
        25u8
    };
    for index in 0..withdrawal_count {
        let total_index_bytes = [
            Byte::from(0),
            Byte::from(0),
            Byte::from(0),
            Byte::from(index as u8 + issued_base),
        ];
        let token_index = Uint32Builder::default().set(total_index_bytes).build();
        let withdrawal_key = CotaNFTIdBuilder::default()
            .cota_id(CotaIdBuilder::default().set(cota_id).build())
            .smt_type(Uint16Builder::default().set(withdrawal_smt_type).build())
            .index(token_index)
            .build();
        withdrawal_keys.push(withdrawal_key.clone());

        let mut withdrawal_key_vec = Vec::new();
        withdrawal_key_vec.extend(withdrawal_key.as_slice());
        withdrawal_key_vec.extend(&BYTE6_ZEROS);
        let mut withdrawal_key_bytes = [0u8; 32];
        withdrawal_key_bytes.copy_from_slice(&withdrawal_key_vec);
        let key = H256::from(withdrawal_key_bytes);

        let configure = if withdrawal_error == WithdrawalError::CoTAImmutableFieldsError {
            0u8
        } else {
            3u8
        };
        let cota_info = CotaNFTInfoBuilder::default()
            .configure(Byte::from(configure))
            .state(Byte::from(3))
            .characteristic(CharacteristicBuilder::default().set(characteristic).build())
            .build();
        let withdrawal_value = WithdrawalCotaNFTValueBuilder::default()
            .nft_info(cota_info)
            .out_point(OutPointSliceBuilder::default().set(out_point_bytes).build())
            .to(LockHashSliceBuilder::default().set(to_lock_bytes).build())
            .build();
        let value = H256::from(blake2b_256(withdrawal_value.as_slice()));

        withdrawal_values.push(withdrawal_value.clone());
        update_leaves.push((key, value));
        update_old_leaves.push((key, H256::from(BYTE32_ZEROS)));
        mint_old_smt
            .update(key, H256::from(BYTE32_ZEROS))
            .expect("SMT update leave error");
        mint_new_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let old_smt_root = mint_old_smt.root().clone();
    let mut old_root_hash_bytes = [0u8; 32];
    old_root_hash_bytes.copy_from_slice(old_smt_root.as_slice());

    let root_hash = mint_new_smt.root().clone();
    let mut root_hash_bytes = [0u8; 32];
    root_hash_bytes.copy_from_slice(root_hash.as_slice());

    let mint_new_cota_merkle_proof = mint_new_smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let mint_new_cota_merkle_proof_compiled = mint_new_cota_merkle_proof
        .clone()
        .compile(update_leaves.clone())
        .unwrap();
    let verify_result = mint_new_cota_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "smt proof verify failed");

    let mint_old_cota_merkle_proof = mint_new_smt
        .merkle_proof(update_old_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let mint_old_cota_old_merkle_proof_compiled = mint_old_cota_merkle_proof
        .compile(update_old_leaves.clone())
        .unwrap();
    let verify_old_leaves_result = mint_old_cota_old_merkle_proof_compiled
        .verify::<Blake2bHasher>(&old_smt_root, update_old_leaves.clone())
        .expect("old smt proof verify failed");
    assert!(verify_old_leaves_result, "old smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = mint_new_cota_merkle_proof_compiled.into();
    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Mint an NFT ".as_bytes());
    action_vec.extend(cota_id_vec);
    action_vec.extend(" to ".as_bytes());
    action_vec.extend(to_lock.as_slice());

    if withdrawal_error == WithdrawalError::CoTANFTActionError {
        action_vec.reverse();
    }
    let action_bytes = BytesBuilder::default()
        .set(action_vec.iter().map(|v| Byte::from(*v)).collect())
        .build();

    let mint_entries = MintCotaNFTEntriesBuilder::default()
        .define_keys(
            DefineCotaNFTKeyVecBuilder::default()
                .set(define_keys)
                .build(),
        )
        .define_old_values(
            DefineCotaNFTValueVecBuilder::default()
                .set(define_old_values)
                .build(),
        )
        .define_new_values(
            DefineCotaNFTValueVecBuilder::default()
                .set(define_new_values)
                .build(),
        )
        .withdrawal_keys(
            WithdrawalCotaNFTKeyVecBuilder::default()
                .set(withdrawal_keys)
                .build(),
        )
        .withdrawal_values(
            WithdrawalCotaNFTValueVecBuilder::default()
                .set(withdrawal_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .action(action_bytes)
        .build();

    (
        old_root_hash_bytes,
        root_hash_bytes,
        Vec::from(mint_entries.as_slice()),
    )
}

fn create_test_context(withdrawal_error: WithdrawalError) -> (Context, TransactionView) {
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
    let lock_hash_160_vec = &lock_hash[0..20];

    let to_lock = context
        .build_script(
            &always_success_out_point,
            Bytes::from(hex::decode("7164f48d7a5bf2298166f8d81b81ea4e908e16ad").unwrap()),
        )
        .expect("script");

    let lock_script_dep = CellDepBuilder::default()
        .out_point(always_success_out_point)
        .build();

    let cota_input_out_point = random_out_point();

    let cota_type_script = context
        .build_script(&cota_out_point, Bytes::copy_from_slice(lock_hash_160_vec))
        .expect("script");

    let withdrawal_count = match withdrawal_error {
        WithdrawalError::CoTANFTActionError | WithdrawalError::SingleAction => 1,
        _ => 10,
    };
    let out_point = if withdrawal_error == WithdrawalError::CoTAOutPointError {
        random_out_point()
    } else {
        cota_input_out_point.clone()
    };

    let (old_root_hash, root_hash, witness_data) =
        generate_mint_cota_nft_smt_data(withdrawal_error, out_point, to_lock, withdrawal_count);

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

    let mint_cota_nft_input = CellInput::new_builder()
        .previous_output(cota_input_out_point.clone())
        .build();

    let inputs = vec![mint_cota_nft_input.clone()];

    let outputs = vec![CellOutput::new_builder()
        .capacity(500u64.pack())
        .lock(lock_script)
        .type_(Some(cota_type_script.clone()).pack())
        .build()];

    let outputs_data: Vec<Bytes> = match withdrawal_error {
        WithdrawalError::SMTProofVerifyFailed => vec![Bytes::from(
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
    witness_data_vec.extend(&[MINT_COTA]);
    witness_data_vec.extend(&witness_data);
    let witness_args = WitnessArgsBuilder::default()
        .input_type(Some(Bytes::from(witness_data_vec)).pack())
        .build();

    let witnesses = match withdrawal_error {
        WithdrawalError::WitnessTypeParseError => vec![error_witness_args.as_bytes()],
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
fn test_mint_cota_nft_cell_success() {
    let (mut context, tx) = create_test_context(WithdrawalError::NoError);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_mint_cota_nft_cell_single_action_success() {
    let (mut context, tx) = create_test_context(WithdrawalError::SingleAction);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_mint_cota_smt_proof_verify_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::SMTProofVerifyFailed);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, SMT_PROOF_VERIFY_FAILED);
}

#[test]
fn test_mint_cota_nft_witness_type_parse_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::WitnessTypeParseError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, WITNESS_TYPE_PARSE_ERROR);
}

#[test]
fn test_mint_cota_nft_smt_type_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTANFTSmtTypeError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_SMT_TYPE_ERROR);
}

#[test]
fn test_mint_cota_issued_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTADefineIssuedError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_DEFINE_ISSUED_ERROR);
}

#[test]
fn test_mint_cota_action_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTANFTActionError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_ACTION_ERROR);
}

#[test]
fn test_mint_cota_out_point_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTAOutPointError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_OUT_POINT_ERROR);
}

#[test]
fn test_mint_cota_token_index_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTANFTTokenIndexError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_TOKEN_INDEX_ERROR);
}

#[test]
fn test_mint_cota_configure_not_same_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTAImmutableFieldsError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_IMMUTABLE_FIELDS_ERROR);
}
