import NoBorelUpperBound.NilpotentGenerated
import NoBorelUpperBound.SymmetricTensor
import NoBorelUpperBound.SymmetricTensorImage
import NoBorelUpperBound.TreeKernels
import NoBorelUpperBound.L1Separable
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.Mul

noncomputable section
open Set Topology

namespace NoBorelUpperBoundFSigma.Construction
open L1Coordinates SymmetricTensor TreeOperators Trees

abbrev A := TreeOperators.Space
abbrev Z := MatrixL1 Trees.Node Trees.Node
abbrev X := A × A
abbrev C := ℝ × Z

def rootEval : X →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : Trees.Node => ℝ) 1 []).comp (ContinuousLinearMap.fst ℝ A A)

def scalarBeta : X →L[ℝ] X →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp rootEval rootEval

def tensorBeta : X →L[ℝ] X →L[ℝ] Z :=
  (1/2 : ℝ) • ((outerBilinear.bilinearComp
    (ContinuousLinearMap.snd ℝ A A) (ContinuousLinearMap.fst ℝ A A)) +
    (outerBilinear.flip.bilinearComp
      (ContinuousLinearMap.fst ℝ A A) (ContinuousLinearMap.snd ℝ A A)))

def beta : X →L[ℝ] X →L[ℝ] C :=
  (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := X) (F := ℝ) (G := Z) ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarBeta.prod tensorBeta)

@[simp] theorem beta_apply (x y : X) :
    beta x y = (x.1 [] * y.1 [],(1/2 : ℝ) • (outer x.2 y.1 + outer y.2 x.1)) := rfl

abbrev G := CentralExtension beta

instance : PolishSpace A := by infer_instance
instance : PolishSpace Z := by infer_instance
instance : PolishSpace G := by infer_instance

def graphMap (D : A →L[ℝ] A) : A →L[ℝ] X := (ContinuousLinearMap.id ℝ A).prod D

@[simp] theorem graphMap_apply (D : A →L[ℝ] A) (a : A) : graphMap D a = (a,D a) := rfl

theorem isClosed_range_graphMap (D : A →L[ℝ] A) : IsClosed ((graphMap D).range : Set X) := by
  have heq : ((graphMap D).range : Set X) = {x | x.2 = D x.1} := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      rfl
    · intro h
      exact ⟨x.1,Prod.ext rfl h.symm⟩
  rw [heq]
  exact isClosed_eq continuous_snd (D.continuous.comp continuous_fst)

@[simp] theorem beta_graph (D : A →L[ℝ] A) (a b : A) :
    beta (graphMap D a) (graphMap D b) = imageMap D [] (sym a b) := by
  apply Prod.ext
  · rw [beta_apply]
    change a [] * b [] = (sym a b) ([],[])
    change a [] * b [] = (1/2 : ℝ) * (a [] * b [] + b [] * a [])
    ring
  · rw [beta_apply]
    exact (mapLeft_sym D a b).symm

theorem centralSpan_eq_imageSubmodule (D : A →L[ℝ] A) :
    CentralExtension.centralSpan beta (graphMap D) = imageSubmodule D [] := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro c ⟨⟨a,b⟩,rfl⟩
    change beta (graphMap D a) (graphMap D b) ∈ imageSubmodule D []
    rw [beta_graph]
    exact ⟨sym a b,sym_mem a b,rfl⟩
  · rintro c ⟨K,hK,rfl⟩
    induction hK using Submodule.span_induction with
    | mem K hK =>
      obtain ⟨⟨a,b⟩,rfl⟩ := hK
      change imageMap D [] (sym a b) ∈ CentralExtension.centralSpan beta (graphMap D)
      rw [← beta_graph]
      exact CentralExtension.beta_mem_centralSpan beta (graphMap D) a b
    | zero =>
      change imageMap D [] 0 ∈ CentralExtension.centralSpan beta (graphMap D)
      rw [map_zero]
      exact (CentralExtension.centralSpan beta (graphMap D)).zero_mem
    | add K L hK hL IHK IHL =>
      simpa using (CentralExtension.centralSpan beta (graphMap D)).add_mem IHK IHL
    | smul r K hK IH =>
      simpa using (CentralExtension.centralSpan beta (graphMap D)).smul_mem r IH

def subgroup (D : A →L[ℝ] A) : Subgroup G := CentralExtension.generatedAxes beta (graphMap D)

def cosetSetoid (D : A →L[ℝ] A) : Setoid G where
  r := GroupCosetRelation (subgroup D)
  iseqv := ⟨by intro g; simpa only [GroupCosetRelation,inv_mul_cancel] using (subgroup D).one_mem,
    by
      intro g h hgh
      have hi := (subgroup D).inv_mem hgh
      simpa only [GroupCosetRelation,mul_inv_rev,inv_inv] using hi,
    by
      intro g h k hgh hhk
      have hm := (subgroup D).mul_mem hgh hhk
      simpa only [GroupCosetRelation,mul_assoc,mul_inv_cancel_left] using hm⟩

def designated : G := CentralExtension.center beta (1,0)

theorem designated_mem_iff (D : A →L[ℝ] A) :
    designated ∈ subgroup D ↔ ∃ a : A, D a = 0 ∧ a [] = 1 := by
  rw [subgroup,CentralExtension.generatedAxes_eq_coordinateSubgroup]
  change (0 ∈ (graphMap D).range ∧ 0 ∈ (graphMap D).range ∧
    (1,0) ∈ CentralExtension.centralSpan beta (graphMap D)) ↔ _
  rw [centralSpan_eq_imageSubmodule]
  simp only [Submodule.zero_mem,true_and]
  constructor
  · rintro ⟨K,hK,himage⟩
    have hr : K ([],[]) = 1 := congrArg Prod.fst himage
    have hD : mapLeft D K = 0 := congrArg Prod.snd himage
    refine ⟨col [] K,?_,hr⟩
    ext i
    have h := congrArg (fun R : Z => R (i,[])) hD
    exact h
  · rintro ⟨a,hDa,ha⟩
    refine ⟨sym a a,sym_mem a a,?_⟩
    apply Prod.ext
    · change (sym a a) ([],[]) = 1
      change (1/2 : ℝ) * (a [] * a [] + a [] * a []) = 1
      rw [ha]
      norm_num
    · simp [hDa]

theorem designated_mem_tree_iff (T : TreeSpace) :
    designated ∈ subgroup (operator T) ↔ HasBranch T := by
  rw [designated_mem_iff,hasBranch_iff_exists_kernel_root]

theorem isFSigma_subgroup (D : A →L[ℝ] A) (hD : Function.Injective D) :
    NoUniversalFSigma.IsFSigma (subgroup D : Set G) := by
  apply CentralExtension.isFSigma_generatedAxes beta (graphMap D) (isClosed_range_graphMap D)
  rw [centralSpan_eq_imageSubmodule]
  exact isFSigma_imageSubmodule D hD []

theorem isFSigma_tree_subgroup (T : TreeSpace) (hT : ¬ HasBranch T) :
    NoUniversalFSigma.IsFSigma (subgroup (operator T) : Set G) :=
  isFSigma_subgroup _ (operator_injective_of_not_hasBranch T hT)

theorem isFSigma_cosetGraph (D : A →L[ℝ] A) (hD : Function.Injective D) :
    NoUniversalFSigma.IsFSigma {p : G × G | GroupCosetRelation (subgroup D) p.1 p.2} := by
  obtain ⟨F,hF,hcover⟩ := isFSigma_subgroup D hD
  refine ⟨fun n => (fun p : G×G => p.1⁻¹*p.2) ⁻¹' F n,?_,?_⟩
  · intro n
    exact (hF n).preimage (continuous_fst.inv.mul continuous_snd)
  · change (fun p : G×G => p.1⁻¹*p.2) ⁻¹' (subgroup D : Set G) = _
    rw [hcover,preimage_iUnion]

end NoBorelUpperBoundFSigma.Construction
