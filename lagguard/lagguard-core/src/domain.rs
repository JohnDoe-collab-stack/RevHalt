use crate::types::*;
use anyhow::{Result, bail};

#[derive(Clone, Debug)]
pub enum Domain {
    Mod { size: u32 },        // 2^bits
    Enum { size: u32 },       // |values|
}

#[derive(Clone, Debug)]
pub struct DomainComponent {
    pub resource: ResourceId,
    pub dom: Domain,
    pub stride: u32,          // base stride for packing
}

#[derive(Clone, Debug)]
pub struct ProductDomain {
    pub comps: Vec<DomainComponent>,
    pub size: u32,            // N = |Â|
}

impl ProductDomain {
    pub fn from_json(j: &AbstractDomainJson) -> Result<Self> {
        if j.r#type != "product_finite" { bail!("unsupported domain type"); }
        let mut comps = Vec::new();
        for c in &j.components {
            let dom = match &c.domain {
                DomainJson::Mod{bits} => Domain::Mod { size: 1u32 << bits },
                DomainJson::Enum{values} => Domain::Enum { size: values.len() as u32 },
            };
            comps.push(DomainComponent { resource: c.resource.clone(), dom, stride: 0 });
        }
        // compute strides
        let mut stride = 1u32;
        for comp in comps.iter_mut() {
            comp.stride = stride;
            let base = match comp.dom { Domain::Mod{size} | Domain::Enum{size} => size };
            stride = stride.checked_mul(base).ok_or_else(|| anyhow::anyhow!("domain overflow"))?;
        }
        Ok(ProductDomain { comps, size: stride })
    }

    pub fn size(&self) -> u32 { self.size }

    // Optionnel: decode/encode si besoin pour debug
}
