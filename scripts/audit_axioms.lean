import ModNullUniversalityProof

set_option autoImplicit false

#print axioms ModNullUniversality.theorem1_1
#print axioms ModNullUniversality.compact_coset_unboundedness
#print axioms ModNullUniversality.haar_amplification
#print axioms ModNullUniversality.CompactTensor.image_coordinates_difference_ksigma
#print axioms ModNullUniversality.CompactTensor.compactFamily_lowComplexity
#print axioms ModNullUniversality.CompactTensor.compactFamily_unbounded
#print axioms ModNullUniversality.AEPower.exists_measurable_code

example :
    ∃ K : ModNullUniversality.CompactMetrizableHaarGroup,
      ModNullUniversality.IsAbelian K ∧
      ∃ H : ModNullUniversality.WF → Subgroup K.Carrier,
        ModNullUniversality.LowComplexityFamily K H ∧
        ∀ F : ModNullUniversality.StandardBorelEquivalence,
          ∃ T : ModNullUniversality.WF,
            ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
              ¬ ModNullUniversality.BorelReducible
                (fun x y : C => ModNullUniversality.CosetRelation K (H T) x.val y.val)
                F.rel := ModNullUniversality.theorem1_1
