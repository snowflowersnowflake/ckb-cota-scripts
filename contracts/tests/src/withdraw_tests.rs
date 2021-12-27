use crate::constants::{
    BYTE32_ZEROS, DEFINE_NFT_SMT_TYPE, HOLD_NFT_SMT_TYPE, WITHDRAWAL_NFT_SMT_TYPE,
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
use cota_smt::{
    common::{BytesBuilder, CotaId, Uint16, Uint32, *},
    smt::{blake2b_256, Blake2bHasher, H256, SMT},
    transfer::*,
};
use rand::{thread_rng, Rng};

const MAX_CYCLES: u64 = 70_000_000;

// error numbers
const SMT_PROOF_VERIFY_FAILED: i8 = 9;
const COTA_NFT_SMT_TYPE_ERROR: i8 = 23;
const COTA_NFT_ACTION_ERROR: i8 = 24;
const COTA_OUT_POINT_ERROR: i8 = 28;
const COTA_LOCKED_NFT_CANNOT_TRANSFER: i8 = 29;
const COTA_NFT_CANNOT_TRANSFER_BEFORE_CLAIM: i8 = 30;
const COTA_NFT_CANNOT_TRANSFER_AFTER_CLAIM: i8 = 31;
const COTA_WITHDRAWAL_NFT_INFO_ERROR: i8 = 32;

#[derive(PartialEq, Copy, Clone)]
enum WithdrawalError {
    NoError,
    SingleAction,
    SMTProofVerifyFailed,
    CoTALockedNFTCannotTransfer,
    CoTANFTCannotTransferBeforeClaim,
    CoTANFTCannotTransferAfterClaim,
    CoTAWithdrawalNFTInfoError,
    CoTANFTSmtTypeError,
    CoTANFTActionError,
    CoTAOutPointError,
}

const WITHDRAW_TRANSFER: u8 = 3;

fn generate_withdrawal_cota_smt_data(
    withdrawal_error: WithdrawalError,
    out_point: OutPoint,
    to_lock: Script,
    withdrawal_count: usize,
) -> ([u8; 32], [u8; 32], Vec<u8>) {
    let withdrawal_smt_type = if withdrawal_error == WithdrawalError::CoTANFTSmtTypeError {
        DEFINE_NFT_SMT_TYPE
    } else {
        WITHDRAWAL_NFT_SMT_TYPE
    };

    let leaves_count = 100;
    let mut before_withdrawal_smt = SMT::default();
    let mut after_withdrawal_smt = SMT::default();

    let mut rng = thread_rng();
    for _ in 0..leaves_count {
        let key: H256 = rng.gen::<[u8; 32]>().into();
        let value: H256 = H256::from([255u8; 32]);
        before_withdrawal_smt
            .update(key, value)
            .expect("SMT update leave error");
        after_withdrawal_smt
            .update(key, value)
            .expect("SMT update leave error");
    }

    let mut hold_keys: Vec<CotaNFTId> = Vec::new();
    let mut hold_values: Vec<CotaNFTInfo> = Vec::new();
    let mut withdrawal_keys: Vec<CotaNFTId> = Vec::new();
    let mut withdrawal_values: Vec<WithdrawalCotaNFTValue> = Vec::new();
    let mut old_update_leaves: Vec<(H256, H256)> = Vec::with_capacity(withdrawal_count * 2);
    let mut new_update_leaves: Vec<(H256, H256)> = Vec::with_capacity(withdrawal_count * 2);

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
        hold_keys.push(hold_key.clone());

        let state = if withdrawal_error == WithdrawalError::CoTALockedNFTCannotTransfer {
            2u8
        } else if withdrawal_error == WithdrawalError::CoTANFTCannotTransferAfterClaim {
            1u8
        } else {
            0u8
        };
        let configure = if withdrawal_error == WithdrawalError::CoTANFTCannotTransferBeforeClaim {
            16u8
        } else if withdrawal_error == WithdrawalError::CoTANFTCannotTransferAfterClaim {
            32u8
        } else {
            0u8
        };
        let mut hold_value = CotaNFTInfoBuilder::default()
            .characteristic(Characteristic::from_slice(&[5u8; 20]).unwrap())
            .configure(Byte::from(configure))
            .state(Byte::from(state))
            .build();
        let mut hold_value_bytes = [0u8; 32];
        hold_value_bytes[0..22].copy_from_slice(hold_value.as_slice());
        let value = H256::from(hold_value_bytes);
        hold_values.push(hold_value.clone());

        old_update_leaves.push((key, value));
        before_withdrawal_smt
            .update(key, value)
            .expect("SMT update leave error");
        new_update_leaves.push((key, H256::from(BYTE32_ZEROS)));
        after_withdrawal_smt
            .update(key, H256::from(BYTE32_ZEROS))
            .expect("SMT update leave error");

        let withdrawal_key = CotaNFTIdBuilder::default()
            .cota_id(CotaId::from_slice(&cota_id_vec).unwrap())
            .smt_type(Uint16::from_slice(&withdrawal_smt_type.to_be_bytes()).unwrap())
            .index(token_index)
            .build();
        let mut withdrawal_key_bytes = [0u8; 32];
        withdrawal_key_bytes[0..26].copy_from_slice(withdrawal_key.as_slice());
        let key = H256::from(withdrawal_key_bytes);
        withdrawal_keys.push(withdrawal_key);

        if withdrawal_error == WithdrawalError::CoTAWithdrawalNFTInfoError {
            hold_value = hold_value.as_builder().configure(Byte::from(2u8)).build();
        }
        let to_lock_bytes = BytesBuilder::default()
            .set(to_lock.as_slice().iter().map(|v| Byte::from(*v)).collect())
            .build();
        let withdrawal_value = WithdrawalCotaNFTValueBuilder::default()
            .nft_info(hold_value)
            .out_point(OutPointSlice::from_slice(&out_point.as_slice()[12..]).unwrap())
            .to_lock(to_lock_bytes)
            .build();
        let value = H256::from(blake2b_256(withdrawal_value.as_slice()));
        withdrawal_values.push(withdrawal_value.clone());

        before_withdrawal_smt
            .update(key, H256::from([0u8; 32]))
            .expect("SMT update leave error");
        after_withdrawal_smt
            .update(key, value)
            .expect("SMT update leave error");
        old_update_leaves.push((key, H256::from([0u8; 32])));
        new_update_leaves.push((key, value));
    }

    let old_smt_root = before_withdrawal_smt.root().clone();
    let mut old_root_hash_bytes = [0u8; 32];
    old_root_hash_bytes.copy_from_slice(old_smt_root.as_slice());

    let root_hash = after_withdrawal_smt.root().clone();
    let mut root_hash_bytes = [0u8; 32];
    root_hash_bytes.copy_from_slice(root_hash.as_slice());

    let withdrawal_mint_merkle_proof = after_withdrawal_smt
        .merkle_proof(old_update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let withdrawal_mint_merkle_proof_compiled = withdrawal_mint_merkle_proof
        .compile(old_update_leaves.clone())
        .unwrap();
    let verify_result = withdrawal_mint_merkle_proof_compiled
        .verify::<Blake2bHasher>(&old_smt_root, old_update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "before withdrawal smt proof verify failed");

    let verify_result = withdrawal_mint_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, new_update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "after withdrawal smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = withdrawal_mint_merkle_proof_compiled.into();
    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Transfer an NFT ".as_bytes());
    action_vec.extend(cota_id_vec);
    action_vec.extend(" to ".as_bytes());
    action_vec.extend(to_lock.as_slice());

    if withdrawal_error == WithdrawalError::CoTANFTActionError {
        action_vec.reverse();
    }
    let action_bytes = BytesBuilder::default()
        .set(action_vec.iter().map(|v| Byte::from(*v)).collect())
        .build();

    let withdrawal_entries = WithdrawalCotaNFTEntriesBuilder::default()
        .hold_keys(HoldCotaNFTKeyVecBuilder::default().set(hold_keys).build())
        .hold_values(
            HoldCotaNFTValueVecBuilder::default()
                .set(hold_values)
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
        Vec::from(withdrawal_entries.as_slice()),
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
    let lock_hash_160_vec = &lock_script.calc_script_hash().as_bytes()[0..20];

    let to_lock = context
        .build_script(
            &always_success_out_point,
            Bytes::from(hex::decode("7164f48d7a5bf2298166f8d81b81ea4e908e16ad").unwrap()),
        )
        .expect("script");

    let lock_script_dep = CellDepBuilder::default()
        .out_point(always_success_out_point)
        .build();

    // prepare cells
    let cota_type_script = context
        .build_script(&cota_out_point, Bytes::copy_from_slice(lock_hash_160_vec))
        .expect("script");

    let cota_input_out_point = random_out_point();

    let out_point = if withdrawal_error == WithdrawalError::CoTAOutPointError {
        random_out_point()
    } else {
        cota_input_out_point.clone()
    };
    let withdrawal_count = match withdrawal_error {
        WithdrawalError::CoTANFTActionError | WithdrawalError::SingleAction => 1,
        _ => 5,
    };
    let (old_root_hash, root_hash, witness_data) =
        generate_withdrawal_cota_smt_data(withdrawal_error, out_point, to_lock, withdrawal_count);

    let mut cota_data_vec: Vec<u8> = vec![];
    let version = [0u8];
    cota_data_vec.extend(&version);
    cota_data_vec.extend(&old_root_hash[..]);

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

    let mut witness_data_vec = vec![];
    witness_data_vec.extend(&[WITHDRAW_TRANSFER]);
    witness_data_vec.extend(&witness_data);
    let witness_args = WitnessArgsBuilder::default()
        .input_type(Some(Bytes::from(witness_data_vec)).pack())
        .build();

    let witnesses = vec![witness_args.as_bytes()];

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
fn test_withdraw_cota_cell_success() {
    let (mut context, tx) = create_test_context(WithdrawalError::NoError);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_withdraw_cota_cell_single_action_success() {
    let (mut context, tx) = create_test_context(WithdrawalError::SingleAction);

    let tx = context.complete_tx(tx);
    // run
    let cycles = context
        .verify_tx(&tx, MAX_CYCLES)
        .expect("pass verification");
    println!("consume cycles: {}", cycles);
}

#[test]
fn test_withdraw_cota_smt_proof_verify_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::SMTProofVerifyFailed);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, SMT_PROOF_VERIFY_FAILED);
}

#[test]
fn test_withdraw_cota_out_point_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTAOutPointError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_OUT_POINT_ERROR);
}

#[test]
fn test_withdraw_cota_nft_info_not_same_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTAWithdrawalNFTInfoError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_WITHDRAWAL_NFT_INFO_ERROR);
}

#[test]
fn test_withdraw_cota_smt_type_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTANFTSmtTypeError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_SMT_TYPE_ERROR);
}

#[test]
fn test_withdraw_locked_cota_nft_cannot_transfer_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTALockedNFTCannotTransfer);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_LOCKED_NFT_CANNOT_TRANSFER);
}

#[test]
fn test_withdraw_unclaimed_cota_nft_cannot_transfer_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTANFTCannotTransferBeforeClaim);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_CANNOT_TRANSFER_BEFORE_CLAIM);
}

#[test]
fn test_withdraw_claimed_cota_nft_cannot_transfer_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTANFTCannotTransferAfterClaim);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_CANNOT_TRANSFER_AFTER_CLAIM);
}

#[test]
fn test_withdraw_cota_action_error() {
    let (mut context, tx) = create_test_context(WithdrawalError::CoTANFTActionError);

    let tx = context.complete_tx(tx);
    // run
    let err = context.verify_tx(&tx, MAX_CYCLES).unwrap_err();
    assert_script_error(err, COTA_NFT_ACTION_ERROR);
}
