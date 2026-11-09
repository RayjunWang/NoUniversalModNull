import NoBorelUpperBound.CategoryProduct
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

section LocalCategory
variable {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] [BaireSpace X]

/-- The local category test for a Baire-measurable set can be witnessed on a
member of a fixed countable basis. -/
theorem nonmeagre_inter_iff_basic_meagre_compl {s U : Set X}
    (hs : BaireMeasurableSet s) (hU : IsOpen U) :
    ¬ IsMeagre (U ∩ s) ↔ ∃ V : countableBasis X,
      (V : Set X) ⊆ U ∧ IsMeagre ((V : Set X) ∩ sᶜ) := by
  classical
  constructor
  · intro hnon
    obtain ⟨O,hO,heq⟩ := hs.residualEq_isOpen
    have hdiff : IsMeagre {x | ¬ (x ∈ s ↔ x ∈ O)} := by
      change ∀ᶠ x in residual X, ¬¬(x ∈ s ↔ x ∈ O)
      exact (eventuallyEq_set.mp heq).mono (fun _ hx => not_not.mpr hx)
    have hUO : (U ∩ O).Nonempty := by
      by_contra hn
      apply hnon
      apply hdiff.mono
      intro x hx
      intro he
      exact hn ⟨x,hx.1,he.mp hx.2⟩
    obtain ⟨V,hV,hVne,hVsub⟩ :=
      (isBasis_countableBasis X).exists_nonempty_subset hUO (hU.inter hO)
    refine ⟨⟨V,hV⟩, (fun x hx => (hVsub hx).1), hdiff.mono ?_⟩
    intro x hx he
    exact hx.2 (he.mpr (hVsub hx.1).2)
  · rintro ⟨V,hVU,hVm⟩ hUm
    have hVmeagre : IsMeagre (V : Set X) := by
      have hVs : IsMeagre ((V : Set X) ∩ s) :=
        hUm.mono (inter_subset_inter_left _ hVU)
      have hu := hVs.union hVm
      exact hu.mono (by intro x hx; by_cases hxs : x ∈ s <;> simp_all)
    exact not_isMeagre_of_isOpen (isOpen_of_mem_countableBasis V.property)
      (nonempty_of_mem_countableBasis V.property) hVmeagre

end LocalCategory

section BorelQuantifier
variable {P : Type u} {X : Type v}
    [TopologicalSpace P] [PolishSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Nonmeagreness of a Borel section inside a fixed open set is a Borel
condition on the parameter. This is the Borel category quantifier. -/
theorem measurableSet_nonmeagre_sections {S : Set (P × X)} (hS : MeasurableSet S) :
    ∀ U : Set X, IsOpen U → MeasurableSet {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ S})} := by
  classical
  induction S,hS using MeasurableSet.induction_on_open with
  | isOpen S hS =>
    intro U hU
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ S})} = sectionHit S U := by
      ext p
      have hsec : IsOpen (U ∩ {x | (p,x) ∈ S}) :=
        hU.inter (hS.preimage (continuous_const.prodMk continuous_id))
      constructor
      · intro hn
        obtain ⟨x,hxU,hxS⟩ := nonempty_of_not_isMeagre hn
        exact ⟨(p,x),⟨hxS,mem_univ _,hxU⟩,rfl⟩
      · rintro ⟨⟨q,x⟩,⟨hxS,_,hxU⟩,hqp⟩
        dsimp at hqp
        subst q
        exact not_isMeagre_of_isOpen hsec ⟨x,hxU,hxS⟩
    rw [heq]
    exact (isOpen_sectionHit hS hU).measurableSet
  | compl S hS IH =>
    intro U hU
    have hsec (p : P) : BaireMeasurableSet {x | (p,x) ∈ Sᶜ} :=
      (hS.compl.preimage measurable_prodMk_left).baireMeasurableSet
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ Sᶜ})} =
        ⋃ V : countableBasis X, if (V : Set X) ⊆ U then
          {p | IsMeagre ((V : Set X) ∩ {x | (p,x) ∈ S})} else ∅ := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion]
      rw [nonmeagre_inter_iff_basic_meagre_compl (hsec p) hU]
      constructor
      · rintro ⟨V,hVU,hVm⟩
        exact ⟨V, by simpa only [if_pos hVU, mem_setOf_eq, mem_compl_iff,
          Set.compl_setOf, not_not] using hVm⟩
      · rintro ⟨V,hVp⟩
        by_cases hVU : (V : Set X) ⊆ U
        · exact ⟨V,hVU,by simpa only [if_pos hVU, mem_setOf_eq, mem_compl_iff,
            Set.compl_setOf, not_not] using hVp⟩
        · simp only [if_neg hVU, mem_empty_iff_false] at hVp
    rw [heq]
    apply MeasurableSet.iUnion
    intro V
    split_ifs
    · simpa only [Set.compl_setOf, not_not] using
        (IH V (isOpen_of_mem_countableBasis V.property)).compl
    · exact MeasurableSet.empty
  | iUnion f _ hf IH =>
    intro U hU
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ ⋃ n, f n})} =
        ⋃ n, {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ f n})} := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro hn
        by_contra he
        push Not at he
        apply hn
        have hi : IsMeagre (⋃ n, U ∩ {x | (p,x) ∈ f n}) := isMeagre_iUnion he
        convert hi using 1
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion]
        tauto
      · rintro ⟨n,hn⟩ hm
        apply hn
        exact hm.mono (by intro x hx; exact ⟨hx.1,⟨n,hx.2⟩⟩)
    rw [heq]
    exact MeasurableSet.iUnion (fun n => IH n U hU)

/-- Comeagreness of Borel sections is a Borel parameter condition. -/
theorem measurableSet_residual_sections {S : Set (P × X)} (hS : MeasurableSet S) :
    MeasurableSet {p | {x | (p,x) ∈ S} ∈ residual X} := by
  have h := (measurableSet_nonmeagre_sections hS.compl Set.univ isOpen_univ).compl
  convert h using 1
  ext p
  simp only [mem_setOf_eq, mem_compl_iff, not_not, Set.univ_inter, IsMeagre,
    Set.compl_setOf, not_not]

end BorelQuantifier
end NoBorelUpperBoundFSigma
