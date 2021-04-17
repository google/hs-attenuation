# attenuation

Implements uni-directional coercions, or representational subtyping relations.

This lets you coerce containers from stronger types to weaker types with zero
runtime cost when it's safe to do so, e.g. `[Fin n] -> [Int]`.
