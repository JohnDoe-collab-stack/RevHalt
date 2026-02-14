use crate::{types::*, domain::ProductDomain, rel::Rel, fiber::*};
use anyhow::{Result, bail};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Model {
    pub domain: ProductDomain,
    pub n: usize,
    pub events: Vec<Event>,
    pub event_index: HashMap<EventId, usize>,
    pub post: HashMap<EventId, Rel>,
    pub hb: Vec<(usize, usize)>, // indices
    pub sigma: Vec<SigmaStep>,
    pub observable: Observable,
}

impl Model {
    pub fn from_json(m: ModelJson) -> Result<Self> {
        let domain = ProductDomain::from_json(&m.abstract_domain)?;
        let n = domain.size() as usize;

        let mut event_index = HashMap::new();
        for (i,e) in m.events.iter().enumerate() { event_index.insert(e.id.clone(), i); }

        // hb edges as indices
        let mut hb = Vec::new();
        for [a,b] in m.hb_edges {
            let ia = *event_index.get(&a).ok_or_else(|| anyhow::anyhow!("hb missing event"))?;
            let ib = *event_index.get(&b).ok_or_else(|| anyhow::anyhow!("hb missing event"))?;
            hb.push((ia, ib));
        }

        // post relations
        let mut post = HashMap::new();
        for pj in m.post {
            if pj.relation.encoding != "sparse_pairs" { bail!("unsupported rel encoding"); }
            let mut r = Rel::empty(n);
            for [i,j] in pj.relation.pairs {
                r.set(i as usize, j as usize);
            }
            post.insert(pj.event, r);
        }

        let observable = observable_from_json(&m.observable)?;
        Ok(Self {
            domain, n, events: m.events, event_index, post, hb, sigma: m.sigma, observable
        })
    }

    pub fn post_of(&self, eid: &EventId) -> &Rel {
        self.post.get(eid).expect("missing post relation")
    }
}
