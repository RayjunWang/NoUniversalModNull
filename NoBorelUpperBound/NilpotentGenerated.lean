import NoBorelUpperBound.NilpotentGroup

noncomputable section
open Set Topology

namespace NoBorelUpperBoundFSigma.CentralExtension
universe u v w
variable {A : Type u} {X : Type v} {C : Type w}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
variable (β : X →L[ℝ] X →L[ℝ] C)

def coordinateSubgroup (H : Submodule ℝ X) (K : Submodule ℝ C)
    (hβ : ∀ x ∈ H, ∀ y ∈ H, β x y ∈ K) : Subgroup (CentralExtension β) where
  carrier := {g | g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ K}
  one_mem' := ⟨H.zero_mem,H.zero_mem,K.zero_mem⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨H.add_mem ha.1 hb.1,H.add_mem ha.2.1 hb.2.1,
      K.add_mem (K.add_mem ha.2.2 hb.2.2) (hβ a.1 ha.1 b.2.1 hb.2.1)⟩
  inv_mem' := by
    intro a ha
    exact ⟨H.neg_mem ha.1,H.neg_mem ha.2.1,
      K.add_mem (K.neg_mem ha.2.2) (hβ a.1 ha.1 a.2.1 ha.2.1)⟩

@[simp] theorem mem_coordinateSubgroup (H : Submodule ℝ X) (K : Submodule ℝ C)
    (hβ : ∀ x ∈ H, ∀ y ∈ H, β x y ∈ K) (g : CentralExtension β) :
    g ∈ coordinateSubgroup β H K hβ ↔ g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ K := Iff.rfl

def centralSpan (j : A →L[ℝ] X) : Submodule ℝ C :=
  Submodule.span ℝ (range (fun p : A×A => β (j p.1) (j p.2)))

theorem beta_mem_centralSpan (j : A →L[ℝ] X) (a b : A) :
    β (j a) (j b) ∈ centralSpan β j := Submodule.subset_span (mem_range_self (a,b))

theorem beta_range_mem_centralSpan (j : A →L[ℝ] X) :
    ∀ x ∈ j.range, ∀ y ∈ j.range, β x y ∈ centralSpan β j := by
  rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩
  exact beta_mem_centralSpan β j a b

def generatedAxes (j : A →L[ℝ] X) : Subgroup (CentralExtension β) :=
  Subgroup.closure (range (fun a => left β (j a)) ∪ range (fun a => right β (j a)))

theorem left_mem_generatedAxes (j : A →L[ℝ] X) (a : A) :
    left β (j a) ∈ generatedAxes β j :=
  Subgroup.subset_closure (Or.inl (mem_range_self a))

theorem right_mem_generatedAxes (j : A →L[ℝ] X) (a : A) :
    right β (j a) ∈ generatedAxes β j :=
  Subgroup.subset_closure (Or.inr (mem_range_self a))

theorem center_generator_mem_generatedAxes (j : A →L[ℝ] X) (a b : A) :
    center β (β (j a) (j b)) ∈ generatedAxes β j := by
  rw [← mixed_commutator]
  exact (generatedAxes β j).mul_mem
    ((generatedAxes β j).mul_mem
      ((generatedAxes β j).mul_mem (left_mem_generatedAxes β j a) (right_mem_generatedAxes β j b))
      ((generatedAxes β j).inv_mem (left_mem_generatedAxes β j a)))
    ((generatedAxes β j).inv_mem (right_mem_generatedAxes β j b))

theorem center_mem_generatedAxes (j : A →L[ℝ] X) {c : C} (hc : c ∈ centralSpan β j) :
    center β c ∈ generatedAxes β j := by
  have hstrong : ∀ c ∈ centralSpan β j, ∀ r : ℝ, center β (r • c) ∈ generatedAxes β j := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨⟨a,b⟩,rfl⟩ := hc
      intro r
      have heq : r • β (j a) (j b) = β (j (r • a)) (j b) := by simp
      rw [heq]
      exact center_generator_mem_generatedAxes β j (r • a) b
    | zero =>
      intro r
      simpa [center] using (generatedAxes β j).one_mem
    | add c d hc hd IHc IHd =>
      intro r
      rw [smul_add,← center_mul]
      exact (generatedAxes β j).mul_mem (IHc r) (IHd r)
    | smul a c hc IH =>
      intro r
      rw [smul_smul]
      exact IH (r*a)
  simpa only [one_smul] using hstrong c hc 1

theorem generatedAxes_eq_coordinateSubgroup (j : A →L[ℝ] X) :
    generatedAxes β j = coordinateSubgroup β j.range (centralSpan β j) (beta_range_mem_centralSpan β j) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · exact ⟨⟨a,rfl⟩,j.range.zero_mem,(centralSpan β j).zero_mem⟩
    · exact ⟨j.range.zero_mem,⟨a,rfl⟩,(centralSpan β j).zero_mem⟩
  · intro g hg
    rcases hg with ⟨⟨a,ha⟩,⟨b,hb⟩,hc⟩
    rw [coordinate_factorization β g]
    apply (generatedAxes β j).mul_mem
    · apply (generatedAxes β j).mul_mem
      · rw [← ha]
        exact left_mem_generatedAxes β j a
      · rw [← hb]
        exact right_mem_generatedAxes β j b
    · apply center_mem_generatedAxes β j
      apply (centralSpan β j).sub_mem hc
      rw [← ha,← hb]
      exact beta_mem_centralSpan β j a b

theorem isFSigma_coordinateSubgroup (H : Submodule ℝ X) (K : Submodule ℝ C)
    (hβ : ∀ x ∈ H, ∀ y ∈ H, β x y ∈ K)
    (hH : IsClosed (H : Set X)) (hK : NoUniversalFSigma.IsFSigma (K : Set C)) :
    NoUniversalFSigma.IsFSigma (coordinateSubgroup β H K hβ : Set (CentralExtension β)) := by
  obtain ⟨S,hS,hcover⟩ := hK
  refine ⟨fun n => {g | g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ S n},?_,?_⟩
  · intro n
    exact (hH.preimage continuous_fst).inter
      ((hH.preimage continuous_snd.fst).inter ((hS n).preimage continuous_snd.snd))
  · ext g
    change (g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ K) ↔ _
    change (g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ (K : Set C)) ↔ _
    rw [hcover]
    simp only [mem_iUnion,mem_setOf_eq]
    aesop

theorem isFSigma_generatedAxes (j : A →L[ℝ] X)
    (hj : IsClosed (j.range : Set X))
    (hC : NoUniversalFSigma.IsFSigma (centralSpan β j : Set C)) :
    NoUniversalFSigma.IsFSigma (generatedAxes β j : Set (CentralExtension β)) := by
  rw [generatedAxes_eq_coordinateSubgroup]
  exact isFSigma_coordinateSubgroup β _ _ _ hj hC

end NoBorelUpperBoundFSigma.CentralExtension
