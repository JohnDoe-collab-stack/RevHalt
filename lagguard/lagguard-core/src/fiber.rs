use crate::{types::*, domain::ProductDomain, rel::BitRow};
use anyhow::{Result, bail};

#[derive(Clone, Debug)]
pub enum Observable {
    Unit,
    Projection { resources: Vec<ResourceId> },
}

pub fn observable_from_json(j: &ObservableJson) -> Result<Observable> {
    match j.r#type.as_str() {
        "unit" => Ok(Observable::Unit),
        "projection" => Ok(Observable::Projection { resources: j.resources.clone().unwrap_or_default() }),
        _ => bail!("unsupported observable"),
    }
}

// MVP: si obs=Unit => fiber = all states
pub fn fiber_all(domain: &ProductDomain) -> BitRow {
    let mut r = BitRow::new(domain.size() as usize);
    for i in 0..domain.size() as usize { r.set(i); }
    r
}
