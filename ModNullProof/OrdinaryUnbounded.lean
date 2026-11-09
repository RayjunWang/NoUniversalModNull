import ModNullProof.LinearCosets
import ModNullProof.TensorFamily
import NoBorelUpperBound.Main

set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace

namespace ModNullUniversality.LinearCosets

open NoBorelUpperBoundFSigma
open NoBorelUpperBoundFSigma.Construction
open NoBorelUpperBoundFSigma.SymmetricTensor

def productSetoid (F : StandardBorelEquivalence) : Setoid ((A × A) × F.Carrier) where
  r x y := x.1 = y.1 ∧ F.rel x.2 y.2
  iseqv := ⟨fun x => ⟨rfl,F.equivalence.refl x.2⟩,
    fun h => ⟨h.1.symm,F.equivalence.symm h.2⟩,
    fun h k => ⟨h.1.trans k.1,F.equivalence.trans h.2 k.2⟩⟩

/-- The actual tree-tensor coset family has no Borel upper bound. -/
theorem tensor_family_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ ModNullUniversality.BorelReducible
      (TensorRelation (TreeOperators.operator T.val.val)) F.rel := by
  classical
  by_contra! hbound
  letI := upgradeStandardBorel F.Carrier
  letI : MeasurableSpace A := borel A
  letI : BorelSpace A := ⟨rfl⟩
  letI : MeasurableSpace Trees.TreeSpace := borel Trees.TreeSpace
  letI : BorelSpace Trees.TreeSpace := ⟨rfl⟩
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace Axis := borel Axis
  letI : BorelSpace Axis := ⟨rfl⟩
  let P := (A × A) × F.Carrier
  let R : Setoid P := productSetoid F
  have hR : IsBorelRelation R.r := by
    have heq : MeasurableSet {p : P × P | p.1.1 = p.2.1} :=
      (isClosed_eq (continuous_fst.fst : Continuous (fun p : P×P => p.1.1))
        continuous_snd.fst).measurableSet
    have hF : MeasurableSet {p : P × P | F.rel p.1.2 p.2.2} :=
      F.measurable_graph.preimage (measurable_fst.snd.prodMk measurable_snd.snd)
    change @MeasurableSet (P × P) (borel (P × P)) _
    have hB : (inferInstance : MeasurableSpace (P × P)) = borel (P × P) :=
      BorelSpace.measurable_eq
    rw [← hB]
    exact heq.inter hF
  have hnil : ∀ T : Trees.TreeSpace, T ∉ MembershipSet family (fun _ => designated) →
      NoBorelUpperBoundFSigma.BorelReducible
        (GroupCosetRelation (GeneratedSubgroup family T)) R.r := by
    intro T hT
    have hnb : ¬ Trees.HasBranch T := by
      simpa only [membershipSet_family,Trees.IF,mem_setOf_eq] using hT
    let W : WF := ⟨T,hnb⟩
    obtain ⟨f,hf,hred⟩ := hbound W
    let D := TreeOperators.operator T
    let g : G → P := fun x => ((theta D x).1,f (theta D x).2)
    have hg : Measurable g :=
      ((continuous_fst.comp (continuous_theta D)).measurable).prodMk
        (hf.comp (continuous_snd.comp (continuous_theta D)).measurable)
    refine ⟨g,?_,?_⟩
    · change @Measurable G P (borel G) (borel P) g
      have hB : (inferInstance : MeasurableSpace P) = borel P := BorelSpace.measurable_eq
      rw [← hB]
      exact hg
    · intro x y
      rw [generatedSubgroup_family]
      change GroupCosetRelation (subgroup D) x y ↔ _
      rw [coset_iff_theta]
      exact and_congr_right (fun _ => hred _ _)
  have hm := category_transfer family (fun n => (continuous_family n).measurable)
    continuous_family_fixed (fun _ => designated) measurable_const R hR hnil
  rw [membershipSet_family] at hm
  exact Trees.not_borel_IF hm

end ModNullUniversality.LinearCosets

namespace ModNullUniversality.CompactTensor

theorem source_family_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ BorelReducible (sourceRelation T) F.rel := by
  exact LinearCosets.tensor_family_unbounded F

end ModNullUniversality.CompactTensor
