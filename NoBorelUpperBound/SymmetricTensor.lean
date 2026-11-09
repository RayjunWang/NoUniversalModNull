import NoBorelUpperBound.SymmetricTensorLinear

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

def algebraicSpan : Submodule ℝ (MatrixL1 I I) :=
  Submodule.span ℝ (range (fun p : L1 I × L1 I => outer p.1 p.2))

def sym (a b : L1 I) : MatrixL1 I I := (1 / 2 : ℝ) • (outer a b + outer b a)

def symmetricSpan : Submodule ℝ (MatrixL1 I I) :=
  Submodule.span ℝ (range (fun p : L1 I × L1 I => sym p.1 p.2))

theorem sym_mem (a b : L1 I) : sym a b ∈ symmetricSpan :=
  Submodule.subset_span (mem_range_self (a,b))

theorem outer_mem (a b : L1 I) : outer a b ∈ algebraicSpan :=
  Submodule.subset_span (mem_range_self (a,b))

theorem symmetricSpan_le_algebraicSpan : symmetricSpan (I := I) ≤ algebraicSpan := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,b⟩,rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (outer_mem a b) (outer_mem b a))

theorem transpose_eq_of_mem_symmetricSpan {K : MatrixL1 I I} (hK : K ∈ symmetricSpan) :
    transpose K = K := by
  induction hK using Submodule.span_induction with
  | mem K hK =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hK
    simp only [sym,map_smul,map_add,transpose_outer,add_comm]
  | zero => exact map_zero _
  | add x y hx hy IHx IHy => simp only [map_add,IHx,IHy]
  | smul a x hx IH => simp only [map_smul,IH]

theorem symmetric_of_mem {K : MatrixL1 I I} (hK : K ∈ symmetricSpan) (i j : I) :
    K (i,j) = K (j,i) := by
  have h := congrArg (fun Q : MatrixL1 I I => Q (j,i)) (transpose_eq_of_mem_symmetricSpan hK)
  exact h

def symmetrize : MatrixL1 I I →L[ℝ] MatrixL1 I I :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ + transpose.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem symmetrize_outer (a b : L1 I) : symmetrize (outer a b) = sym a b := by
  change (1 / 2 : ℝ) • (outer a b + transpose (outer a b)) = _
  rw [transpose_outer]
  rfl

theorem symmetrize_mem {K : MatrixL1 I I} (hK : K ∈ algebraicSpan) :
    symmetrize K ∈ symmetricSpan := by
  induction hK using Submodule.span_induction with
  | mem K hK => obtain ⟨⟨a,b⟩,rfl⟩ := hK; simpa using sym_mem a b
  | zero => simpa using (symmetricSpan (I := I)).zero_mem
  | add x y hx hy IHx IHy => simpa only [map_add] using Submodule.add_mem _ IHx IHy
  | smul a x hx IH => simpa only [map_smul] using Submodule.smul_mem _ a IH

theorem mem_symmetricSpan_iff {K : MatrixL1 I I} :
    K ∈ symmetricSpan ↔ K ∈ algebraicSpan ∧ transpose K = K := by
  refine ⟨fun h => ⟨symmetricSpan_le_algebraicSpan h,transpose_eq_of_mem_symmetricSpan h⟩, ?_⟩
  rintro ⟨hK,hT⟩
  have h := symmetrize_mem hK
  have heq : symmetrize K = K := by
    change (1/2 : ℝ) • (K + transpose K) = K
    rw [hT]
    module
  rwa [heq] at h

def imageMap (D : L1 I →L[ℝ] L1 I) (o : I) : MatrixL1 I I →L[ℝ] ℝ × MatrixL1 I I :=
  (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (o,o)).prod (mapLeft D)

def imageSubmodule (D : L1 I →L[ℝ] L1 I) (o : I) : Submodule ℝ (ℝ × MatrixL1 I I) :=
  symmetricSpan.map (imageMap D o).toLinearMap

@[simp] theorem imageMap_apply (D : L1 I →L[ℝ] L1 I) (o : I) (K : MatrixL1 I I) :
    imageMap D o K = (K (o,o),mapLeft D K) := rfl

theorem mem_imageSubmodule (D : L1 I →L[ℝ] L1 I) (o : I) (K : MatrixL1 I I)
    (hK : K ∈ symmetricSpan) : (K (o,o),mapLeft D K) ∈ imageSubmodule D o :=
  ⟨K,hK,rfl⟩

@[simp] theorem mapLeft_sym (D : L1 I →L[ℝ] L1 I) (a b : L1 I) :
    mapLeft D (sym a b) = (1/2 : ℝ) • (outer (D a) b + outer (D b) a) := by
  simp only [sym,map_smul,map_add,mapLeft_outer]

def symBilinear : L1 I →L[ℝ] L1 I →L[ℝ] MatrixL1 I I :=
  (1/2 : ℝ) • ((outerBilinear (I := I) (J := I)) + outerBilinear.flip)

@[simp] theorem symBilinear_apply (a b : L1 I) : symBilinear a b = sym a b := rfl

end NoBorelUpperBoundFSigma.SymmetricTensor
