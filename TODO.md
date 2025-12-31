# TODO: P vs NP Formalization Roadmap

Goal: formalize the structural dichotomy criterion for SAT/UNSAT in a
polynomially constrained setting.

- Define SAT/UNSAT (syntax, semantics) and the ambient category of instances.
- Define polynomial reductions as morphisms and show functoriality.
- Propose a candidate operator O on instances in this category.
- Prove O has a universal property (adjoint/coreflector style).
- Prove ker_iff: O x = bot <-> UNSAT x (non-tautological theorem).
- Prove sig_invar: SAT (O x) <-> SAT x.
- Derive the structural dichotomy consequences in this setting.
- Analyze whether the criterion is satisfied or provably absent.
