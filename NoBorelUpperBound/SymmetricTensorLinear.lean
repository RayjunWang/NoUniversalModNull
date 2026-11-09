import NoBorelUpperBound.L1Coordinates
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

noncomputable section

open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma
namespace TensorAlgebra

/-- Finitely many independent coordinate vectors admit a nonsingular coordinate
minor. The coordinate index type itself can be infinite. -/
theorem exists_coordinate_pivot {I : Type*} {r : ℕ} (f : Fin r → I → ℝ)
    (hf : LinearIndependent ℝ f) :
    ∃ rows : Fin r → I, Matrix.det (fun i j => f j (rows i)) ≠ 0 := by
  have htop : Submodule.span ℝ (range (Function.swap f)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hf
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (Function.swap f)
  let b : Module.Basis κ ℝ (Fin r → ℝ) := Module.Basis.mk hli (by rw [hspan, htop])
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = r := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : Fin r ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  refine ⟨a ∘ e, ?_⟩
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hli.comp e e.injective

end TensorAlgebra
end NoBorelUpperBoundFSigma


namespace NoBorelUpperBoundFSigma.TensorAlgebra

/-- The algebraic column space of an infinite real matrix. -/
def columnSpace {I J : Type*} (A : I → J → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (range (fun j i => A i j))

/-- Finite-dimensional column spaces have a basis consisting of actual columns. -/
theorem exists_column_basis {I J : Type*} (A : I → J → ℝ)
    [FiniteDimensional ℝ (columnSpace A)] :
    ∃ r : ℕ, ∃ cols : Fin r → J,
      LinearIndependent ℝ (fun t i => A i (cols t)) ∧
      Submodule.span ℝ (range (fun t i => A i (cols t))) = columnSpace A := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (fun j i => A i j)
  have hspan' : Submodule.span ℝ (range ((fun j i => A i j) ∘ a)) = columnSpace A := hspan
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun j i => A i j) ∘ a))) :=
    hspan'.symm ▸ inferInstance
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, a ∘ e, hli.comp e e.injective, ?_⟩
  have hrange : range (fun t i => A i ((a ∘ e) t)) =
      range ((fun j i => A i j) ∘ a) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨e t, rfl⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨t, rfl⟩ := e.surjective k
      exact ⟨t, rfl⟩
  rw [hrange]
  exact hspan'

/-- A nonsingular pivot reconstructs every column once the selected columns span
all the columns. The adjugate form makes reconstruction polynomial. -/
theorem pivot_reconstruction {I J : Type*} {r : ℕ}
    (A : I → J → ℝ) (cols : Fin r → J) (rows : Fin r → I)
    (hspan : ∀ j, (fun i => A i j) ∈
      Submodule.span ℝ (range (fun t i => A i (cols t)))) (i : I) (j : J) :
    Matrix.det (fun s t => A (rows s) (cols t)) * A i j =
      (fun t => A i (cols t)) ⬝ᵥ
        ((Matrix.adjugate (fun s t => A (rows s) (cols t))) *ᵥ (fun s => A (rows s) j)) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hspan j)
  have heq (a : I) : ∑ t, c t * A a (cols t) = A a j := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc a
  have hvec : (fun s => A (rows s) j) =
      (fun s t => A (rows s) (cols t)) *ᵥ c := by
    funext s
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using (heq (rows s)).symm
  rw [hvec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul]
  congr 1
  simpa only [dotProduct, mul_comm] using (heq i).symm

/-- Every finite-rank coordinate matrix has a nonsingular finite pivot and an
exact polynomial row-column reconstruction. -/
theorem exists_finite_pivot {I J : Type*} (A : I → J → ℝ)
    [FiniteDimensional ℝ (columnSpace A)] :
    ∃ r : ℕ, ∃ cols : Fin r → J, ∃ rows : Fin r → I,
      Matrix.det (fun s t => A (rows s) (cols t)) ≠ 0 ∧
      ∀ i j, Matrix.det (fun s t => A (rows s) (cols t)) * A i j =
        (fun t => A i (cols t)) ⬝ᵥ
          (Matrix.adjugate (fun s t => A (rows s) (cols t)) *ᵥ (fun s => A (rows s) j)) := by
  obtain ⟨r, cols, hli, hspan⟩ := exists_column_basis A
  obtain ⟨rows, hdet⟩ := exists_coordinate_pivot (fun t i => A i (cols t)) hli
  refine ⟨r, cols, rows, hdet, pivot_reconstruction A cols rows ?_⟩
  intro j
  rw [hspan]
  exact Submodule.subset_span (mem_range_self j)

end NoBorelUpperBoundFSigma.TensorAlgebra


namespace NoBorelUpperBoundFSigma.TensorAlgebra

@[simp] theorem columnSpace_zero {I J : Type*} :
    columnSpace (fun (_ : I) (_ : J) => (0 : ℝ)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Submodule.zero_mem _

theorem columnSpace_add_le {I J : Type*} (A B : I → J → ℝ) :
    columnSpace (fun i j => A i j + B i j) ≤ columnSpace A ⊔ columnSpace B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (columnSpace A ⊔ columnSpace B).add_mem
    (Submodule.mem_sup_left (Submodule.subset_span (mem_range_self j)))
    (Submodule.mem_sup_right (Submodule.subset_span (mem_range_self j)))

theorem columnSpace_smul_le {I J : Type*} (c : ℝ) (A : I → J → ℝ) :
    columnSpace (fun i j => c * A i j) ≤ columnSpace A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (columnSpace A).smul_mem c (Submodule.subset_span (mem_range_self j))

end NoBorelUpperBoundFSigma.TensorAlgebra






