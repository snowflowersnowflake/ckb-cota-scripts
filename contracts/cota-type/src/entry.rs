use ckb_std::high_level::load_cell_data;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, packed::*, prelude::*},
    high_level::load_script,
};
use core::result::Result;
use script_utils::cota::Cota;
use script_utils::error::Error;
use script_utils::helper::{
    check_registry_cells_exist, check_type_args_not_equal_lock_hash, count_cells_by_type, Action,
};

const TYPE_ARGS_LEN: usize = 20;

fn check_cota<'a>(cota_type: &'a Script) -> impl Fn(&Script) -> bool + 'a {
    move |type_: &Script| cota_type.as_slice() == type_.as_slice()
}

fn parse_cota_action(cota_type: &Script) -> Result<Action, Error> {
    let inputs_count = count_cells_by_type(Source::GroupInput, &check_cota(cota_type));
    let outputs_count = count_cells_by_type(Source::GroupOutput, &check_cota(cota_type));
    match (inputs_count, outputs_count) {
        (0, 1) => Ok(Action::Create),
        (1, 1) => Ok(Action::Update),
        _ => Err(Error::RegistryCellsCountError),
    }
}

fn handle_creation(cota_type: &Script) -> Result<(), Error> {
    if !check_registry_cells_exist()? {
        return Err(Error::CoTARegistryCellExistError);
    }
    if check_type_args_not_equal_lock_hash(cota_type, Source::GroupOutput)? {
        return Err(Error::CoTATypeArgsNotEqualLockHash);
    }
    let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
    // CoTA cell data only has version filed
    if output_cota.smt_root.is_some() {
        return Err(Error::CoTADataInvalid);
    }
    Ok(())
}

fn handle_update() -> Result<(), Error> {
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
        Action::Update => handle_update()?,
    }

    Ok(())
}
