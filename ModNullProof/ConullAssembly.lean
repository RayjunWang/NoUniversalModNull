import Solutions.HaarAmplification

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace ModNullUniversality

/-- Uniform amplification preserves unboundedness on every conull restriction. -/
theorem conull_unbounded_of_unbounded
    (K : CompactMetrizableHaarGroup) (H : WF → Subgroup K.Carrier)
    (hH : ∀ T, MeasurableSet (H T : Set K.Carrier))
    (hunbounded : ∀ F : StandardBorelEquivalence,
      ∃ T : WF, ¬ BorelReducible (CosetRelation K (H T)) F.rel) :
    ∀ F : StandardBorelEquivalence,
      ∃ T : WF, ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
        ¬ BorelReducible (fun x y : C => CosetRelation K (H T) x.val y.val) F.rel := by
  classical
  intro F
  by_cases hF : Nonempty F.Carrier
  · obtain ⟨Q,hQ⟩ := haar_amplification K F hF
    obtain ⟨T,hT⟩ := hunbounded Q
    refine ⟨T,fun C hC hμ hred => ?_⟩
    exact hT (hQ (H T) (hH T) C hC hμ hred)
  · obtain ⟨T,_⟩ := hunbounded F
    refine ⟨T,fun C _ hμ hred => ?_⟩
    have hne : C.Nonempty := by
      by_contra hn
      have hzero : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simpa only [hzero,measure_empty,zero_ne_one] using hμ
    obtain ⟨x,hx⟩ := hne
    obtain ⟨f,_,_⟩ := hred
    exact hF ⟨f ⟨x,hx⟩⟩

end ModNullUniversality
