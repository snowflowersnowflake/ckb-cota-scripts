use crate::claim::verify_cota_claim_smt;
use crate::define::verify_cota_define_smt;
use crate::mint::verify_cota_mint_smt;
use crate::update::verify_cota_update_smt;
use crate::withdraw::verify_cota_withdraw_smt;
use ckb_std::high_level::{load_cell_data, load_cell_lock_hash};
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, packed::*, prelude::*},
    high_level::load_script,
};
use core::result::Result;
use script_utils::cota::Cota;
use script_utils::error::Error;
use script_utils::helper::{
    check_registry_cells_exist, check_type_args_not_equal_lock_hash, count_cells_by_type,
    load_group_input_witness_args_with_type, Action,
};

const TYPE_ARGS_LEN: usize = 20;

const CREATE: u8 = 1;
const MINT: u8 = 2;
const WITHDRAW: u8 = 3;
const CLAIM: u8 = 4;
const UPDATE: u8 = 5;

fn check_cota<'a>(cota_type: &'a Script) -> impl Fn(&Script) -> bool + 'a {
    move |type_: &Script| cota_type.as_slice() == type_.as_slice()
}

fn parse_cota_action(cota_type: &Script) -> Result<Action, Error> {
    let inputs_count = count_cells_by_type(Source::GroupInput, &check_cota(cota_type));
    let outputs_count = count_cells_by_type(Source::GroupOutput, &check_cota(cota_type));
    match (inputs_count, outputs_count) {
        (0, 1) => Ok(Action::Create),
        (1, 1) => Ok(Action::Update),
        _ => Err(Error::CoTACellsCountError),
    }
}

fn handle_creation(cota_type: &Script) -> Result<(), Error> {
    if !check_registry_cells_exist()? {
        return Err(Error::CoTARegistryCellExistError);
    }
    if check_type_args_not_equal_lock_hash(&cota_type, Source::GroupOutput)? {
        return Err(Error::CoTATypeArgsNotEqualLockHash);
    }
    let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
    // CoTA cell data only has version filed
    if output_cota.smt_root.is_some() {
        return Err(Error::CoTADataInvalid);
    }
    Ok(())
}

fn handle_update(cota_type: &Script) -> Result<(), Error> {
    let input_lock_hash = load_cell_lock_hash(0, Source::GroupInput)?;
    let output_lock_hash = load_cell_lock_hash(0, Source::GroupOutput)?;
    if input_lock_hash != output_lock_hash {
        return Err(Error::CoTACellLockNotSame);
    }

    if check_type_args_not_equal_lock_hash(&cota_type, Source::GroupOutput)? {
        return Err(Error::CoTATypeArgsNotEqualLockHash);
    }

    let witness_args = load_group_input_witness_args_with_type(cota_type)?;
    if let Some(witness_args_type) = witness_args.input_type().to_opt() {
        let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
        if output_cota.smt_root.is_none() {
            return Err(Error::CoTACellSMTRootError);
        }
        let witness_args_input_type: Bytes = witness_args_type.unpack();
        match u8::from(witness_args_input_type[0]) {
            CREATE => verify_cota_define_smt(witness_args_input_type)?,
            MINT => verify_cota_mint_smt(witness_args_input_type)?,
            WITHDRAW => verify_cota_withdraw_smt(witness_args_input_type)?,
            CLAIM => verify_cota_claim_smt(cota_type, witness_args_input_type)?,
            UPDATE => verify_cota_update_smt(witness_args_input_type)?,
            _ => return Err(Error::WitnessTypeParseError),
        }
    } else {
        let output_cota_cell_data = load_cell_data(0, Source::GroupOutput)?;
        let input_cota_cell_data = load_cell_data(0, Source::GroupInput)?;
        if output_cota_cell_data != input_cota_cell_data {
            return Err(Error::CoTACellDataNotSame);
        }
    }
    Ok(())
}

pub fn main() -> Result<(), Error> {
    let cota_type = load_script()?;
    let type_args: Bytes = cota_type.args().unpack();
    if type_args.len() != TYPE_ARGS_LEN {
        return Err(Error::TypeArgsInvalid);
    }

    match parse_cota_action(&cota_type)? {
        Action::Create => handle_creation(&cota_type)?,
        Action::Update => handle_update(&cota_type)?,
    }

    Ok(())
}
