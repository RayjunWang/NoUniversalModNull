import ModNullProof.HaarAmplification

set_option autoImplicit false

namespace ModNullUniversality

/-- Uniform Haar amplification: a fixed Borel target absorbs every conull reduction. -/
theorem haar_amplification
    (K : CompactMetrizableHaarGroup) (F : StandardBorelEquivalence)
    (hF : Nonempty F.Carrier) :
    ∃ Q : StandardBorelEquivalence,
      ∀ H : Subgroup K.Carrier, MeasurableSet (H : Set K.Carrier) →
        ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
          BorelReducible
            (fun x y : C => CosetRelation K H x.val y.val) F.rel →
          BorelReducible (CosetRelation K H) Q.rel :=
  haar_amplification_proved K F hF

end ModNullUniversality
