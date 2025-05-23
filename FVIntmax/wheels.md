# Wheels.lean
## Structure

1. namespace: Intmax
   1. namespace: CryptoAssumptions
   2. class abbrev PreWithZero
   3. section: UniquelyIndexed
   4. def: codomainPred
   5. def: isCodomainNonneg
   6. section: NonNeg
   7. section: Order
   8. section: Tactics
   9. lemma: sort_empty_iff
2. theorem: List.keys_zipWith_sigma
3. namespace: List
   1. section: List
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
4. namespace: Multiset
   1. section: Multiset
      1. variable
      2. theorem: keys_map_eq
      3. theorem: nodup_map_of_pres_keys_nodup
      4. theorem: keys_dedup_map_pres_univ
      5. theorem: nodup_filter_of_nodup
