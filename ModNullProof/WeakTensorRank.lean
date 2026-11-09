import ModNullProof.CoordinateBounds
import NoBorelUpperBound.SymmetricTensorRank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor
open NoBorelUpperBoundFSigma.TensorAlgebra

/-- Rank at most r, expressed solely by vanishing finite coordinate minors. -/
def RankLE (r : ℕ) (u : Ambient) : Prop :=
  ∀ rows cols : Fin (r+1) → S,
    Matrix.det (fun i j => u (.inr (rows i,cols j))) = 0

theorem isClosed_rankLE (r : ℕ) : IsClosed {u : Ambient | RankLE r u} := by
  simp only [RankLE,setOf_forall]
  apply isClosed_iInter
  intro rows
  apply isClosed_iInter
  intro cols
  apply isClosed_eq _ continuous_const
  have hc : Continuous (fun u : Ambient =>
      fun i j : Fin (r+1) => u (.inr (rows i,cols j))) :=
    continuous_pi (fun i => continuous_pi (fun j => continuous_apply _))
  exact hc.matrix_det

theorem rankLE_not_independent (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) (rows : Fin (r+1) → S) :
    ¬ LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) := by
  intro hli
  have hcoord := independent_coordinates (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) hli
  obtain ⟨cols,hdet⟩ := exists_coordinate_pivot (fun t j => R (rows t,j)) hcoord
  have hz := hR rows cols
  have heq : (fun i j => R (rows j,cols i)) =
      (fun i j => R (rows i,cols j))ᵀ := rfl
  change Matrix.det (fun i j : Fin (r+1) => R (rows j,cols i)) ≠ 0 at hdet
  rw [heq,Matrix.det_transpose] at hdet
  exact hdet hz

theorem finiteDimensional_rowSpace_rankLE (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) : FiniteDimensional ℝ (rowSpace R) := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)
  have hf : Finite κ := by
    by_contra hfinite
    letI : Infinite κ := not_finite_iff_infinite.mp hfinite
    let e : Fin (r+1) → κ := fun i => Infinite.natEmbedding κ i.val
    have he : Function.Injective e := fun i j h => Fin.ext ((Infinite.natEmbedding κ).injective h)
    exact rankLE_not_independent r R hR (fun t => a (e t)) (hli.comp e he)
  letI := hf
  have hi : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a))) :=
    (Module.Basis.span hli).finiteDimensional_of_finite
  change FiniteDimensional ℝ (Submodule.span ℝ (range (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)))
  exact hspan ▸ hi

theorem finrank_rowSpace_le_rankLE (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) : Module.finrank ℝ (rowSpace R) ≤ r := by
  classical
  letI := finiteDimensional_rowSpace_rankLE r R hR
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a))) :=
    hspan.symm ▸ finiteDimensional_rowSpace_rankLE r R hR
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  have hcard : Fintype.card κ ≤ r := by
    by_contra h
    have hemb : Fintype.card (Fin (r+1)) ≤ Fintype.card κ := by
      simpa using Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hemb
    exact rankLE_not_independent r R hR (fun t => a (e t)) (hli.comp e e.injective)
  have heq : Module.finrank ℝ (rowSpace R) = Fintype.card κ := by
    change Module.finrank ℝ (Submodule.span ℝ (range (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R))) = _
    rw [← hspan]
    exact Module.finrank_eq_card_basis (Module.Basis.span hli)
  rw [heq]
  exact hcard

theorem exists_row_basis_of_finiteDimensional (R : MatrixL1 S S)
    [FiniteDimensional ℝ (rowSpace R)] :
    ∃ r : ℕ, ∃ rows : Fin r → S,
      LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) ∧
      Submodule.span ℝ (range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R)) = rowSpace R := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a))) :=
    hspan.symm ▸ (inferInstance : FiniteDimensional ℝ (rowSpace R))
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ,a ∘ e,hli.comp e e.injective,?_⟩
  have hr : range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row ((a ∘ e) t) R) =
      range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨e t,rfl⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨t,rfl⟩ := e.surjective k
      exact ⟨t,rfl⟩
  rw [hr]
  exact hspan

/-- Finite coordinate rank in an l1 matrix is actual finite tensor rank. -/
theorem mem_algebraicSpan_of_finiteDimensional (R : MatrixL1 S S)
    [FiniteDimensional ℝ (rowSpace R)] : R ∈ algebraicSpan := by
  classical
  obtain ⟨r,rows,hli,hspan⟩ := exists_row_basis_of_finiteDimensional R
  obtain ⟨cols,hdet⟩ := exists_coordinate_pivot
    (fun t j => R (rows t,j)) (independent_coordinates _ hli)
  let P : Matrix (Fin r) (Fin r) ℝ := fun i j => R (rows j,cols i)
  have hraw (i : S) : (fun j => R (i,j)) ∈
      Submodule.span ℝ (range (fun t j => R (rows t,j))) := by
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      (hspan.symm ▸ row_mem_rowSpace R i)
    refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c,?_⟩
    ext j
    have hh := congrArg (lp.evalCLM ℝ (fun _ : S => ℝ) 1 j) hc
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    simpa only [map_sum,map_smul,smul_eq_mul] using hh
  let b : Fin r → L1 S := fun s => ∑ t, P.adjugate t s •
    NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R
  have heq : P.det • R = ∑ s, outer (col (cols s) R) (b s) := by
    ext ij
    change P.det * R ij =
      (lp.evalCLM ℝ (fun _ : S×S => ℝ) 1 ij) (∑ s, outer (col (cols s) R) (b s))
    rw [map_sum]
    change P.det * R ij = ∑ s, R (ij.1,cols s) * b s ij.2
    have hh := pivot_reconstruction (fun i j => R (j,i)) rows cols hraw ij.2 ij.1
    change P.det * R ij = _ at hh
    rw [hh]
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    change _ = R (ij.1,cols s) *
      (lp.evalCLM ℝ (fun _ : S => ℝ) 1 ij.2)
        (∑ t, P.adjugate t s • NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R)
    simp only [map_sum,map_smul,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    change R (rows t,ij.2) * (P.adjugate t s * R (ij.1,cols s)) =
      R (ij.1,cols s) * (P.adjugate t s * R (rows t,ij.2))
    ring
  have hs : P.det • R ∈ algebraicSpan := by
    rw [heq]
    exact Submodule.sum_mem _ (fun s _ => outer_mem _ _)
  exact (Submodule.smul_mem_iff _ hdet).mp hs

theorem mem_algebraicSpan_of_rankLE (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) : R ∈ algebraicSpan := by
  letI := finiteDimensional_rowSpace_rankLE r R hR
  exact mem_algebraicSpan_of_finiteDimensional R

theorem rankLE_of_finrank_rowSpace_le (r : ℕ) (R : MatrixL1 S S)
    [FiniteDimensional ℝ (rowSpace R)] (hdim : Module.finrank ℝ (rowSpace R) ≤ r) :
    RankLE r (coordinates (0,R)) := by
  classical
  intro rows cols
  by_contra hd
  let F : L1 S →ₗ[ℝ] (Fin (r+1) → ℝ) :=
    LinearMap.pi (fun j => (lp.evalCLM ℝ (fun _ : S => ℝ) 1 (cols j)).toLinearMap)
  have hli : LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) :=
    LinearIndependent.of_comp F (Matrix.linearIndependent_rows_of_det_ne_zero hd)
  let v : Fin (r+1) → rowSpace R := fun t =>
    ⟨NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R,row_mem_rowSpace R (rows t)⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (rowSpace R).subtype hli
  have hh := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hh
  omega

theorem exists_rankLE_of_mem_algebraicSpan {R : MatrixL1 S S}
    (hR : R ∈ algebraicSpan) : ∃ r : ℕ, RankLE r (coordinates (0,R)) := by
  letI := finiteDimensional_rowSpace hR
  exact ⟨Module.finrank ℝ (rowSpace R),rankLE_of_finrank_rowSpace_le _ R le_rfl⟩

end ModNullUniversality.CompactTensor
