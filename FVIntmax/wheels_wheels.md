# Wheels/Wheels.lean
## Structure

1. section: HicSuntDracones
2. namespace: Finmap
   1. section: Lookup
      1. variable
      2. def: lookup_h
3. namespace: Intmax
   1. abbrev: ExtraDataT
   2. instance
   3. abbrev: KₛT
   4. abbrev: KₚT
   5. section: RubeGoldberg
      1. opaque: ComputationallyInfeasible
      2. axiom: computationallyInfeasible_axiom
   6. namespace: SimpleRandom
      1. def: Seed
      2. def: isRandom
      3. scoped notation
   7. section: ByteArray
      1. deriving instance
