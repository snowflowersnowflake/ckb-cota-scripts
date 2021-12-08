use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, packed::*, prelude::*},
    high_level::{load_cell_type, load_script},
};
use core::result::Result;
use script_utils::error::Error;
use script_utils::helper::{check_registry_cells_exist, Action};

const TYPE_ARGS_LEN: usize = 20;

fn parse_cota_action(cota_type: &Script) -> Result<Action, Error> {
    let check_cota = |source| {
        load_cell_type(0, source).map_or(false, |type_opt| {
            type_opt.map_or(false, |type_| type_.as_slice() == cota_type.as_slice())
        })
    };
    match (check_cota(Source::Input), check_cota(Source::Output)) {
        (false, true) => Ok(Action::Create),
        (true, true) => Ok(Action::Update),
        _ => Err(Error::CoTACellsCountError),
    }
}

fn handle_creation() -> Result<(), Error> {
    if !check_registry_cells_exist()? {
        return Err(Error::CoTARegistryCellExistError);
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
        Action::Create => handle_creation()?,
        Action::Update => handle_update()?,
    }

    Ok(())
}
