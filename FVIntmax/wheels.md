# Wheels.lean & Wheels/Wheels.lean
## Structure

### Wheels.lean

#### namespace: Intmax

1. noncomputable opaque: H
2. namespace: CryptoAssumptions
   1. section: Hashing
      1. class: Injective
      2. theorem: Function.injective_of_CryptInjective
3. class abbrev: PreWithZero
4. section: UniquelyIndexed
   1. abbrev: UniqueTokenT
   2. prefix:max
   3. abbrev: UniquelyIndexed
   4. namespace: UniquelyIndexed
      1. noncomputable def: attach
      2. noncomputable instance
      3. noncomputable instance
      4. lemma: default_eq_attach
      5. theorem: injective
5. def: codomainPred
6. def: isCodomainNonneg
7. section: NonNeg
   1. def: NonNeg
   2. postfix:max
   3. section: Nonneg
      1. variable
      2. instance
      3. instance
      4. lemma: NonNeg.coe_nonneg
      5. lemma: NonNeg.nonneg
      6. instance
8. section: Order
   1. def: discretePreorder
   2. def: trivialPreorder
   3. section: VectorPreorder
      1. open: Mathlib
      2. variable
      3. namespace: Vec
         1. def: le
         2. instance
         3. lemma: le_refl
         4. lemma: le_trans
      4. instance
      5. namespace: Vec
         1. section: UnnecessarilySpecific
            1. variable
            2. private lemma: le_cons_aux
            3. lemma: le_cons
            4. lemma: le_of_ext_le
9.  section: Tactics
      1.  open Lean.Elab.Tactic in
10. lemma: sort_empty_iff

1. theorem: List.keys_zipWith_sigma

#### namespace & section: List

1. theorem: keys_map_eq
2. theorem: nodup_map_of_pres_keys_nodup
3. lemma: zip_nodup_of_nodup_right
4. lemma: zip_eq_iff
5. lemma: getElem_Ico_of_lt
6. section: ImSorry
   1. lemma: map_join_eq
   2. lemma: map_eq_project_triple
   3. lemma: map_join_unnecessarily_specific
7. lemma: finRange_eq_Ico

#### namespace & section: Multiset

1. variable
2. theorem: keys_map_eq
3. theorem: nodup_map_of_pres_keys_nodup
4. theorem: keys_dedup_map_pres_univ
5. theorem: nodup_filter_of_nodup

### Wheels/Wheels.lean

#### section: HicSuntDracones
1. declare_aesop_rule_sets

#### namespace: Finmap

1. section: Lookup
   1. variable
   2. def: lookup_h

#### namespace: Intmax

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

## Syntaxes

### Top Level
- [x] `import`
- [x] `namespace`
- [x] `section`
- [x] `abbrev`
- [ ] `variable`
- [ ] `def`
- [ ] `instance`
- [ ] `axiom`
- [ ] `lemma`
- [ ] `theorem`
- [ ] `class`
- [ ] `opaque`
- [ ] `open`
- [ ] `prefix:max`
- [ ] `scoped notation`
- [ ] `deriving instance`
- [ ] `noncomputable opaque`
- [ ] `noncomputable def`
- [ ] `noncomputable instance`
- [ ] `private lemma`

### Tactics
