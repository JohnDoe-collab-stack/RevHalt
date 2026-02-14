use serde::{Deserialize, Serialize};

pub type ResourceId = String;
pub type EventId = String;
pub type PrefixId = String;
pub type SigmaId = String;
pub type StateId = u32; // index dans [0..N)

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Resource {
    pub id: ResourceId,
    pub kind: String, // "field" | "mutex" | ...
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Event {
    pub id: EventId,
    pub kind: String,      // "Read" | "Write" | "Lock" | ...
    pub resource: Option<ResourceId>,
    pub reads: Vec<ResourceId>,
    pub writes: Vec<ResourceId>,
    pub hb_after: Vec<EventId>, // optionnel: redondant avec hb_edges
    pub meta: Option<EventMeta>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EventMeta {
    pub span: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SigmaStep {
    pub id: SigmaId,
    pub kind: String,
    pub resource: Option<ResourceId>,
    // Optionnel: path explicit (sinon généré)
    pub step_path: Option<Vec<EventId>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HbEdge(pub EventId, pub EventId);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModelJson {
    pub version: String,
    pub resources: Vec<Resource>,
    pub events: Vec<Event>,
    pub hb_edges: Vec<[EventId; 2]>,
    pub sigma: Vec<SigmaStep>,
    pub abstract_domain: AbstractDomainJson,
    pub post: Vec<PostJson>,
    pub observable: ObservableJson,
    pub targets: Option<Vec<TargetJson>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TargetJson {
    pub prefix: PrefixId,
    pub obs_value: serde_json::Value,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ObservableJson {
    pub r#type: String, // "projection" | "unit"
    pub resources: Option<Vec<ResourceId>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AbstractDomainJson {
    pub r#type: String, // "product_finite"
    pub components: Vec<DomainComponentJson>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DomainComponentJson {
    pub resource: ResourceId,
    pub domain: DomainJson,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum DomainJson {
    #[serde(rename="mod")]
    Mod { bits: u32 }, // size = 2^bits
    #[serde(rename="enum")]
    Enum { values: Vec<String> },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PostJson {
    pub event: EventId,
    pub relation: RelEncodingJson,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RelEncodingJson {
    pub encoding: String, // "sparse_pairs" (MVP)
    pub pairs: Vec<[u32; 2]>,
}
