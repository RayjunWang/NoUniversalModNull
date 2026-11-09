import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic

noncomputable section
open Set Filter TopologicalSpace Topology

namespace NoBorelUpperBoundFSigma
universe u v

section Product
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def sectionHit (U : Set (X × Y)) (V : Set Y) : Set X :=
  Prod.fst '' (U ∩ (univ ×ˢ V))

theorem isOpen_sectionHit {U : Set (X × Y)} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) : IsOpen (sectionHit U V) :=
  isOpenMap_fst _ (hU.inter (isOpen_univ.prod hV))

theorem dense_sectionHit {U : Set (X × Y)} {V : Set Y}
    (hU : Dense U) (hV : IsOpen V) (hne : V.Nonempty) : Dense (sectionHit U V) := by
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨p, hpWV, hpU⟩ := hU.inter_open_nonempty (W ×ˢ V) (hW.prod hV) (hWne.prod hne)
  exact ⟨p.1, hpWV.1, ⟨p, ⟨hpU, ⟨mem_univ _, hpWV.2⟩⟩, rfl⟩⟩

/-- The residual-section half of the Kuratowski--Ulam theorem. -/
theorem residual_sections [SecondCountableTopology Y] {s : Set (X × Y)}
    (hs : s ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, {y | (x, y) ∈ s} ∈ residual Y := by
  classical
  obtain ⟨S, hSo, hSd, hSc, hSs⟩ := mem_residual_iff.mp hs
  letI : Countable S := hSc.to_subtype
  have hgood : ∀ᶠ x in residual X, ∀ U : S, ∀ V : countableBasis Y,
      x ∈ sectionHit U.val V.val := by
    apply eventually_countable_forall.mpr
    intro U
    apply eventually_countable_forall.mpr
    intro V
    exact residual_of_dense_open
      (isOpen_sectionHit (hSo U U.property) (isOpen_of_mem_countableBasis V.property))
      (dense_sectionHit (hSd U U.property) (isOpen_of_mem_countableBasis V.property)
        (nonempty_of_mem_countableBasis V.property))
  filter_upwards [hgood] with x hx
  have hsection (U : S) : {y | (x, y) ∈ U.val} ∈ residual Y := by
    apply residual_of_dense_open
    · exact (hSo U U.property).preimage (continuous_const.prodMk continuous_id)
    · apply (isBasis_countableBasis Y).dense_iff.mpr
      intro V hV _
      obtain ⟨⟨a,b⟩, ⟨hpU, hpV⟩, hpx⟩ := hx U ⟨V, hV⟩
      dsimp at hpx
      subst a
      exact ⟨b, hpV.2, hpU⟩
  have htotal : (⋂ U : S, {y | (x, y) ∈ U.val}) ∈ residual Y :=
    countable_iInter_mem.mpr hsection
  apply mem_of_superset htotal
  intro y hy
  apply hSs
  intro U hU
  exact mem_iInter.mp hy ⟨U, hU⟩

/-- A saturated residual set in a nonempty Baire product reflects to its
first factor. No regularity assumption on the saturated set is required. -/
theorem residual_of_preimage_fst [SecondCountableTopology Y] [BaireSpace Y] [Nonempty Y]
    {s : Set X} (hs : Prod.fst ⁻¹' s ∈ residual (X × Y)) : s ∈ residual X := by
  filter_upwards [residual_sections hs] with x hx
  obtain ⟨y, hy⟩ := (dense_of_mem_residual hx).nonempty
  exact hy

/-- The Kuratowski--Ulam equivalence for sets with the property of Baire. -/
theorem residual_product_iff [SecondCountableTopology Y] [BaireSpace X] [BaireSpace Y]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) :
    s ∈ residual (X × Y) ↔ ∀ᶠ x in residual X, {y | (x,y) ∈ s} ∈ residual Y := by
  refine ⟨residual_sections, ?_⟩
  intro hsec
  obtain ⟨U, hU, heq⟩ := hs.residualEq_isOpen
  have heqp : ∀ᶠ p in residual (X × Y), p ∈ s ↔ p ∈ U := eventuallyEq_set.mp heq
  have hUsec : ∀ᶠ x in residual X, {y | (x,y) ∈ U} ∈ residual Y := by
    filter_upwards [hsec, residual_sections heqp] with x hx hxEq
    filter_upwards [hx, hxEq] with y hy hEq
    exact hEq.mp hy
  have hUd : Dense U := by
    apply dense_iff_inter_open.mpr
    intro W hW hWne
    obtain ⟨⟨x,y⟩, hxy⟩ := hWne
    obtain ⟨A,B,hA,hB,hx,hy,hAB⟩ := isOpen_prod_iff.mp hW x y hxy
    obtain ⟨a,ha,haSec⟩ := (dense_of_mem_residual hUsec).inter_open_nonempty A hA ⟨x,hx⟩
    obtain ⟨b,hb,hab⟩ := (dense_of_mem_residual haSec).inter_open_nonempty B hB ⟨y,hy⟩
    exact ⟨(a,b), hAB ⟨ha,hb⟩, hab⟩
  filter_upwards [residual_of_dense_open hU hUd, heqp] with p hp hEq
  exact hEq.mpr hp

end Product
end NoBorelUpperBoundFSigma
