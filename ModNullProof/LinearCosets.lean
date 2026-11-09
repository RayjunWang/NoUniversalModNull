import ModNullProof.Coordinates
import NoBorelUpperBound.Construction

set_option autoImplicit false
noncomputable section
open Set Topology

namespace ModNullUniversality.LinearCosets

open NoBorelUpperBoundFSigma
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor
open NoBorelUpperBoundFSigma.Construction

def residual (D : A →L[ℝ] A) (x : X) : A := x.2 - D x.1

def correction (D : A →L[ℝ] A) (g : G) : C :=
  (0, (1 / 2 : ℝ) • outer (residual D g.1) g.2.1.1)

def theta (D : A →L[ℝ] A) (g : G) : (A × A) × C :=
  ((residual D g.1, residual D g.2.1), g.2.2 - correction D g)

def TensorRelation (D : A →L[ℝ] A) (c d : C) : Prop :=
  d - c ∈ imageSubmodule D []

theorem continuous_residual (D : A →L[ℝ] A) : Continuous (residual D) :=
  continuous_snd.sub (D.continuous.comp continuous_fst)

theorem continuous_correction (D : A →L[ℝ] A) : Continuous (correction D) := by
  exact continuous_const.prodMk
    ((continuous_outer.comp (((continuous_residual D).comp continuous_fst).prodMk
      continuous_snd.fst.fst)).const_smul (1 / 2 : ℝ))

theorem continuous_theta (D : A →L[ℝ] A) : Continuous (theta D) :=
  (((continuous_residual D).comp continuous_fst).prodMk
    ((continuous_residual D).comp continuous_snd.fst)).prodMk
      (continuous_snd.snd.sub (continuous_correction D))

theorem mem_graph_iff (D : A →L[ℝ] A) (x : X) :
    x ∈ (graphMap D).range ↔ residual D x = 0 := by
  constructor
  · rintro ⟨a,rfl⟩
    simp [residual,graphMap_apply]
  · intro h
    exact ⟨x.1,Prod.ext rfl (sub_eq_zero.mp h).symm⟩

theorem residual_sub (D : A →L[ℝ] A) (x y : X) :
    residual D (y-x) = residual D y - residual D x := by
  change (y.2-x.2)-D (y.1-x.1) = (y.2-D y.1)-(x.2-D x.1)
  rw [map_sub]
  abel

theorem beta_residual (D : A →L[ℝ] A) (x : X) (e : A) :
    beta x (graphMap D e) =
      imageMap D [] (sym x.1 e) + (0, (1/2 : ℝ) • outer (residual D x) e) := by
  apply Prod.ext
  · change x.1 [] * e [] = (1/2 : ℝ) * (x.1 [] * e [] + e [] * x.1 []) + 0
    ring
  · change (1/2 : ℝ) • (outer x.2 e + outer (D e) x.1) =
      mapLeft D (sym x.1 e) + (1/2 : ℝ) • outer (residual D x) e
    rw [mapLeft_sym]
    ext ij
    change (1/2 : ℝ) * (x.2 ij.1 * e ij.2 + (D e) ij.1 * x.1 ij.2) =
      (1/2 : ℝ) * ((D x.1) ij.1 * e ij.2 + (D e) ij.1 * x.1 ij.2) +
        (1/2 : ℝ) * ((x.2 ij.1 - (D x.1) ij.1) * e ij.2)
    ring

theorem inv_mul_coordinates (g h : G) :
    g⁻¹ * h = (h.1-g.1,h.2.1-g.2.1,h.2.2-g.2.2-beta g.1 (h.2.1-g.2.1)) := by
  rw [CentralExtension.inv_def,CentralExtension.mul_def]
  apply Prod.ext
  · change -g.1+h.1 = h.1-g.1
    abel
  · apply Prod.ext
    · change -g.2.1+h.2.1 = h.2.1-g.2.1
      abel
    · simp only [map_neg,map_sub,ContinuousLinearMap.neg_apply]
      abel

theorem subgroup_mem_iff (D : A →L[ℝ] A) (g : G) :
    g ∈ subgroup D ↔
      residual D g.1 = 0 ∧ residual D g.2.1 = 0 ∧ g.2.2 ∈ imageSubmodule D [] := by
  rw [subgroup,CentralExtension.generatedAxes_eq_coordinateSubgroup]
  change g.1 ∈ (graphMap D).range ∧ g.2.1 ∈ (graphMap D).range ∧
      g.2.2 ∈ CentralExtension.centralSpan beta (graphMap D) ↔ _
  rw [centralSpan_eq_imageSubmodule,mem_graph_iff,mem_graph_iff]

theorem correction_sub (D : A →L[ℝ] A) (g h : G)
    (hr : residual D g.1 = residual D h.1) :
    correction D h - correction D g =
      (0, (1/2 : ℝ) • outer (residual D g.1) (h.2.1.1-g.2.1.1)) := by
  apply Prod.ext
  · simp [correction]
  · change (1/2 : ℝ) • outer (residual D h.1) h.2.1.1 -
      (1/2 : ℝ) • outer (residual D g.1) g.2.1.1 = _
    rw [← hr]
    ext ij
    change (1/2 : ℝ) * (residual D g.1 ij.1 * h.2.1.1 ij.2) -
      (1/2 : ℝ) * (residual D g.1 ij.1 * g.2.1.1 ij.2) =
        (1/2 : ℝ) * (residual D g.1 ij.1 * (h.2.1.1 ij.2-g.2.1.1 ij.2))
    ring

theorem graph_difference (D : A →L[ℝ] A) (x y : X)
    (h : residual D x = residual D y) :
    y-x = graphMap D (y.1-x.1) := by
  apply Prod.ext
  · rfl
  · change y.2-x.2 = D (y.1-x.1)
    rw [map_sub]
    have hh : x.2-D x.1 = y.2-D y.1 := h
    calc
      y.2-x.2 = (y.2-D y.1)-(x.2-D x.1)+(D y.1-D x.1) := by abel
      _ = D y.1-D x.1 := by rw [hh]; abel

theorem coset_iff_theta (D : A →L[ℝ] A) (g h : G) :
    GroupCosetRelation (subgroup D) g h ↔
      (theta D g).1 = (theta D h).1 ∧
        TensorRelation D (theta D g).2 (theta D h).2 := by
  rw [GroupCosetRelation,inv_mul_coordinates,subgroup_mem_iff]
  simp only [residual_sub,sub_eq_zero]
  change (residual D h.1 = residual D g.1 ∧
    residual D h.2.1 = residual D g.2.1 ∧
      h.2.2-g.2.2-beta g.1 (h.2.1-g.2.1) ∈ imageSubmodule D []) ↔ _
  by_cases hr : residual D g.1 = residual D h.1
  · by_cases hs : residual D g.2.1 = residual D h.2.1
    · have heq : (theta D g).1 = (theta D h).1 := Prod.ext hr hs
      simp only [hr.symm,hs.symm,true_and,heq]
      rw [graph_difference D g.2.1 h.2.1 hs,beta_residual]
      have hmem : imageMap D [] (sym g.1.1 (h.2.1.1-g.2.1.1)) ∈ imageSubmodule D [] :=
        ⟨_,sym_mem _ _,rfl⟩
      have hid :
          h.2.2-g.2.2-
              (imageMap D [] (sym g.1.1 (h.2.1.1-g.2.1.1)) +
                (0,(1/2 : ℝ) • outer (residual D g.1) (h.2.1.1-g.2.1.1))) =
            ((theta D h).2-(theta D g).2) -
              imageMap D [] (sym g.1.1 (h.2.1.1-g.2.1.1)) := by
        dsimp only [theta]
        rw [show h.2.2-correction D h-(g.2.2-correction D g) =
            h.2.2-g.2.2-(correction D h-correction D g) by abel]
        rw [correction_sub D g h hr]
        abel
      rw [hid]
      exact (imageSubmodule D []).sub_mem_iff_left hmem
    · constructor
      · rintro ⟨_,h,_⟩
        exact (hs h.symm).elim
      · rintro ⟨h,_⟩
        exact (hs (congrArg Prod.snd h)).elim
  · constructor
    · rintro ⟨h,_⟩
      exact (hr h.symm).elim
    · rintro ⟨h,_⟩
      exact (hr (congrArg Prod.fst h)).elim

end ModNullUniversality.LinearCosets
