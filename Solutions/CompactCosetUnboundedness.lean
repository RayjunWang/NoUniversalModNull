import ModNullProof.CompactFamily

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality

theorem compact_coset_unboundedness :
    ∃ K : CompactMetrizableHaarGroup, IsAbelian K ∧
      ∃ H : WF → Subgroup K.Carrier, LowComplexityFamily K H ∧
        ∀ F : StandardBorelEquivalence, ∃ T : WF,
          ¬ BorelReducible (CosetRelation K (H T)) F.rel :=
  ⟨CompactTensor.compactGroup,CompactTensor.compactGroup_abelian,
    CompactTensor.compactFamily,CompactTensor.compactFamily_lowComplexity,
    CompactTensor.compactFamily_unbounded⟩

end ModNullUniversality
