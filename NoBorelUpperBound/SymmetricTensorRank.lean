import NoBorelUpperBound.SymmetricTensor

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

def coordinates : L1 I →ₗ[ℝ] (I → ℝ) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinates_injective : Function.Injective (coordinates (I := I)) := by
  intro x y h
  ext i
  exact congrFun h i

theorem independent_coordinates {r : ℕ} (a : Fin r → L1 I)
    (ha : LinearIndependent ℝ a) : LinearIndependent ℝ (fun t i => a t i) := by
  exact ha.map' coordinates (LinearMap.ker_eq_bot.mpr coordinates_injective)

def rowSpace (R : MatrixL1 I I) : Submodule ℝ (L1 I) :=
  Submodule.span ℝ (range (fun i => L1Coordinates.row i R))

theorem row_mem_rowSpace (R : MatrixL1 I I) (i : I) : L1Coordinates.row i R ∈ rowSpace R :=
  Submodule.subset_span (mem_range_self i)

theorem rowSpace_zero : rowSpace (0 : MatrixL1 I I) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i (0 : MatrixL1 I I) ∈ (⊥ : Submodule ℝ (L1 I))
  simp

theorem rowSpace_add_le (R Q : MatrixL1 I I) : rowSpace (R+Q) ≤ rowSpace R ⊔ rowSpace Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i (R+Q) ∈ rowSpace R ⊔ rowSpace Q
  rw [map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (row_mem_rowSpace R i)) (Submodule.mem_sup_right (row_mem_rowSpace Q i))

theorem rowSpace_smul_le (c : ℝ) (R : MatrixL1 I I) : rowSpace (c • R) ≤ rowSpace R := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i (c • R) ∈ rowSpace R
  rw [map_smul]
  exact Submodule.smul_mem _ _ (row_mem_rowSpace R i)

theorem finiteDimensional_rowSpace {R : MatrixL1 I I} (hR : R ∈ algebraicSpan) :
    FiniteDimensional ℝ (rowSpace R) := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hR
    let W := Submodule.span ℝ ({b} : Set (L1 I))
    have hW : rowSpace (outer a b) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change L1Coordinates.row i (outer a b) ∈ W
      rw [row_outer]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton b))
    letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (finite_singleton b)
    exact Submodule.finiteDimensional_of_le hW
  | zero => rw [rowSpace_zero]; infer_instance
  | add x y hx hy IHx IHy =>
    letI := IHx
    letI := IHy
    exact Submodule.finiteDimensional_of_le (rowSpace_add_le x y)
  | smul a x hx IH =>
    letI := IH
    exact Submodule.finiteDimensional_of_le (rowSpace_smul_le a x)

theorem finiteDimensional_coordinate_columnSpace {R : MatrixL1 I I} (hR : R ∈ algebraicSpan) :
    FiniteDimensional ℝ (columnSpace (fun i j => R (i,j))) := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hR
    let W := Submodule.span ℝ ({fun i => a i} : Set (I → ℝ))
    have hW : columnSpace (fun i j => outer a b (i,j)) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      have ha : (fun i => a i) ∈ W := Submodule.subset_span (by simp)
      convert W.smul_mem (b j) ha using 1
      funext i
      simp [mul_comm]
    letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (finite_singleton _)
    exact Submodule.finiteDimensional_of_le hW
  | zero =>
    change FiniteDimensional ℝ (columnSpace (fun (_ : I) (_ : I) => (0:ℝ)))
    rw [columnSpace_zero]
    infer_instance
  | add x y hx hy IHx IHy =>
    letI := IHx
    letI := IHy
    exact Submodule.finiteDimensional_of_le
      (columnSpace_add_le (fun i j => x (i,j)) (fun i j => y (i,j)))
  | smul a x hx IH =>
    letI := IH
    exact Submodule.finiteDimensional_of_le (columnSpace_smul_le a (fun i j => x (i,j)))

theorem exists_row_basis {R : MatrixL1 I I} (hR : R ∈ algebraicSpan) :
    ∃ r : ℕ, ∃ rows : Fin r → I,
      LinearIndependent ℝ (fun t => L1Coordinates.row (rows t) R) ∧
      Submodule.span ℝ (range (fun t => L1Coordinates.row (rows t) R)) = rowSpace R := by
  letI := finiteDimensional_rowSpace hR
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => L1Coordinates.row i R)
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => L1Coordinates.row i R) ∘ a))) :=
    hspan.symm ▸ finiteDimensional_rowSpace hR
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ,a ∘ e,hli.comp e e.injective,?_⟩
  have hr : range (fun t => L1Coordinates.row ((a ∘ e) t) R) = range ((fun i => L1Coordinates.row i R) ∘ a) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨e t,rfl⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨t,rfl⟩ := e.surjective k
      exact ⟨t,rfl⟩
  rw [hr]
  exact hspan

/-- Independent first tensor factors allow recovery of every second factor
from finitely many rows, using a nonsingular coordinate minor. -/
theorem factor_mem_rowSpace {r : ℕ} (x y : Fin r → L1 I)
    (hx : LinearIndependent ℝ (fun t i => x t i)) (t : Fin r) :
    y t ∈ rowSpace (∑ s, outer (x s) (y s)) := by
  classical
  obtain ⟨qs,hdet⟩ := exists_coordinate_pivot (fun t i => x t i) hx
  let N : Matrix (Fin r) (Fin r) ℝ := fun j i => x i (qs j)
  let R := ∑ s, outer (x s) (y s)
  have hrec : N.det • y t = ∑ j, N.adjugate t j • L1Coordinates.row (qs j) R := by
    ext k
    change (lp.evalCLM ℝ (fun _ : I => ℝ) 1 k) (N.det • y t) =
      (lp.evalCLM ℝ (fun _ : I => ℝ) 1 k) (∑ j, N.adjugate t j • L1Coordinates.row (qs j) R)
    simp only [map_smul,map_sum,smul_eq_mul]
    change N.det * y t k = ∑ j, N.adjugate t j * R (qs j,k)
    have hr (j : Fin r) : R (qs j,k) = (N *ᵥ (fun s => y s k)) j := by
      change (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (qs j,k)) R = _
      simp only [R,map_sum,outer_apply,Matrix.mulVec,dotProduct,N]
      rfl
    simp_rw [hr]
    change N.det * y t k = (N.adjugate *ᵥ (N *ᵥ (fun s => y s k))) t
    rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
    rfl
  have hh : N.det • y t ∈ rowSpace R := by
    rw [hrec]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (row_mem_rowSpace R (qs j)))
  exact (Submodule.smul_mem_iff _ hdet).mp hh

theorem exists_independent_decomposition {K : MatrixL1 I I} (hK : K ∈ algebraicSpan) :
    ∃ r : ℕ, ∃ x y : Fin r → L1 I,
      LinearIndependent ℝ (fun t i => x t i) ∧ K = ∑ t, outer (x t) (y t) := by
  classical
  letI := finiteDimensional_coordinate_columnSpace hK
  obtain ⟨r,cols,hli,hspan⟩ := exists_column_basis (fun i j => K (i,j))
  obtain ⟨rows,hdet⟩ := exists_coordinate_pivot (fun t i => K (i,cols t)) hli
  let P : Matrix (Fin r) (Fin r) ℝ := fun s t => K (rows s,cols t)
  let x : Fin r → L1 I := fun t => col (cols t) K
  let b : Fin r → L1 I := fun t => ∑ s, P.adjugate t s • L1Coordinates.row (rows s) K
  have hscaled : P.det • K = ∑ t, outer (x t) (b t) := by
    ext p
    change (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 p) (P.det • K) =
      (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 p) (∑ t, outer (x t) (b t))
    simp only [map_smul,map_sum,smul_eq_mul]
    change P.det * K p = ∑ t, x t p.1 * b t p.2
    have hrec := pivot_reconstruction (fun i j => K (i,j)) cols rows
      (fun j => by rw [hspan]; exact Submodule.subset_span (mem_range_self j)) p.1 p.2
    apply hrec.trans
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    change (∑ s, K (p.1,cols t) * (P.adjugate t s * K (rows s,p.2))) = _
    change _ = K (p.1,cols t) *
      (lp.evalCLM ℝ (fun _ : I => ℝ) 1 p.2) (∑ s, P.adjugate t s • L1Coordinates.row (rows s) K)
    simp only [map_sum,map_smul,smul_eq_mul]
    rw [Finset.mul_sum]
    rfl
  refine ⟨r,x,fun t => P.det⁻¹ • b t,hli,?_⟩
  calc
    K = P.det⁻¹ • (P.det • K) := by rw [smul_smul,inv_mul_cancel₀ hdet,one_smul]
    _ = ∑ t, outer (x t) (P.det⁻¹ • b t) := by
      rw [hscaled,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro t _
      exact (outer_smul_right P.det⁻¹ (x t) (b t)).symm

theorem mapLeft_mem_algebraicSpan (D : L1 I →L[ℝ] L1 I) {K : MatrixL1 I I}
    (hK : K ∈ algebraicSpan) : mapLeft D K ∈ algebraicSpan := by
  induction hK using Submodule.span_induction with
  | mem K hK => obtain ⟨⟨a,b⟩,rfl⟩ := hK; simpa using outer_mem (D a) b
  | zero => simpa using (algebraicSpan (I := I)).zero_mem
  | add x y hx hy IHx IHy => simpa only [map_add] using Submodule.add_mem _ IHx IHy
  | smul a x hx IH => simpa only [map_smul] using Submodule.smul_mem _ a IH

/-- An injective action on the first tensor factor preserves the entire
finite-dimensional row space. This direction is the recovery needed below. -/
theorem rowSpace_le_rowSpace_mapLeft (D : L1 I →L[ℝ] L1 I) (hD : Function.Injective D)
    {K : MatrixL1 I I} (hK : K ∈ algebraicSpan) : rowSpace K ≤ rowSpace (mapLeft D K) := by
  classical
  obtain ⟨r,x,y,hx,hxy⟩ := exists_independent_decomposition hK
  have hxnative : LinearIndependent ℝ x := by
    apply (coordinates.linearIndependent_iff (LinearMap.ker_eq_bot.mpr coordinates_injective)).mp
    exact hx
  have hxD := independent_coordinates (fun t => D (x t))
    (hxnative.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD))
  have hR : mapLeft D K = ∑ t, outer (D (x t)) (y t) := by
    rw [hxy,map_sum]
    simp only [mapLeft_outer]
  have hy (t : Fin r) : y t ∈ rowSpace (mapLeft D K) := by
    rw [hR]
    exact factor_mem_rowSpace (fun t => D (x t)) y hxD t
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i K ∈ rowSpace (mapLeft D K)
  have hrow : L1Coordinates.row i K = ∑ t, (x t i) • y t := by
    rw [hxy]
    simp only [map_sum,row_outer]
  rw [hrow]
  exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (hy t))

end NoBorelUpperBoundFSigma.SymmetricTensor
