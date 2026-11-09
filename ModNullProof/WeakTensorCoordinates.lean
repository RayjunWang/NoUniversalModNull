import ModNullProof.CoordinateBounds
import ModNullProof.BaireOneComplexity
import NoBorelUpperBound.SymmetricTensorImage
import Mathlib.Logic.Equiv.List
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor

/-- The finite-coordinate approximations to a bounded operator's row evaluation. -/
def rowApprox (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S) (n : ℕ)
    (u : coordinateBall M) : ℝ :=
  ∑ k ∈ Finset.range n, D (lp.single 1 (Equiv.listNatEquivNat.symm k)
    (u.val (.inr (a,Equiv.listNatEquivNat.symm k)))) q

theorem continuous_rowApprox (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S) (n : ℕ) :
    Continuous (rowApprox D M a q n) := by
  apply continuous_finsetSum
  intro k hk
  exact (lp.evalCLM ℝ (fun _ : S => ℝ) 1 q).continuous.comp
    (D.continuous.comp ((lp.singleContinuousLinearMap ℝ (fun _ : S => ℝ) 1
      (Equiv.listNatEquivNat.symm k)).continuous.comp
        ((continuous_apply _).comp continuous_subtype_val)))

theorem tendsto_rowApprox (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S)
    (u : coordinateBall M) :
    Tendsto (fun n => rowApprox D M a q n u) atTop
      (𝓝 (D (NoBorelUpperBoundFSigma.L1Coordinates.row a (ballMatrix M u)) q)) := by
  have h := (lp.hasSum_single (by simp : (1 : ENNReal) ≠ ⊤)
    (NoBorelUpperBoundFSigma.L1Coordinates.row a (ballMatrix M u))).mapL D
  have h' := h.mapL (lp.evalCLM ℝ (fun _ : S => ℝ) 1 q)
  have h'' := Equiv.listNatEquivNat.symm.hasSum_iff.mpr h'
  exact h''.tendsto_sum_nat

theorem baireOne_row (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S) :
    BaireOne (fun u : coordinateBall M =>
      D (NoBorelUpperBoundFSigma.L1Coordinates.row a (ballMatrix M u)) q) :=
  ⟨rowApprox D M a q,continuous_rowApprox D M a q,tendsto_rowApprox D M a q⟩

theorem baireOne_matrix (M : ℝ) (ij : S × S) :
    BaireOne (fun u : coordinateBall M => ballMatrix M u ij) := by
  change BaireOne (fun u : coordinateBall M => u.val (Sum.inr ij))
  exact BaireOne.of_continuous ((continuous_apply (Sum.inr ij : Index)).comp continuous_subtype_val)

theorem baireOne_scalar (M : ℝ) :
    BaireOne (fun u : coordinateBall M => (ballSource M u).1) :=
  BaireOne.of_continuous ((continuous_apply _).comp continuous_subtype_val)

theorem baireOne_pivotDet (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) :
    BaireOne (fun u : coordinateBall M => (pivotD D rows qs (ballMatrix M u)).det) :=
  BaireOne.matrix_det (fun i j => baireOne_row D M (rows j) (qs i))

theorem baireOne_pivotAdjugate (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) (i j : Fin r) :
    BaireOne (fun u : coordinateBall M => (pivotD D rows qs (ballMatrix M u)).adjugate i j) :=
  BaireOne.matrix_adjugate (fun i j => baireOne_row D M (rows j) (qs i)) i j

theorem baireOne_lift (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) (i j : S) :
    BaireOne (fun u : coordinateBall M => liftNumerator D rows qs (ballMatrix M u) (i,j)) := by
  simp_rw [liftNumerator_apply]
  exact BaireOne.sum Finset.univ (fun t ht => BaireOne.sum Finset.univ
    (fun s hs => (baireOne_pivotAdjugate D M rows qs t s).mul
      ((baireOne_matrix M (rows t,i)).mul (baireOne_matrix M (qs s,j)))))

theorem mapLeft_liftNumerator_apply (D : L1 S →L[ℝ] L1 S) {r : ℕ}
    (rows qs : Fin r → S) (R : MatrixL1 S S) (i j : S) :
    mapLeft D (liftNumerator D rows qs R) (i,j) =
      ∑ t, ∑ s, (pivotD D rows qs R).adjugate t s *
        (D (NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) i * R (qs s,j)) := by
  change (lp.evalCLM ℝ (fun _ : S×S => ℝ) 1 (i,j))
    (mapLeft D (liftNumerator D rows qs R)) = _
  simp only [liftNumerator,map_sum,map_smul,smul_eq_mul,mapLeft_outer]
  rfl

theorem baireOne_mapLeft_lift (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) (i j : S) :
    BaireOne (fun u : coordinateBall M =>
      mapLeft D (liftNumerator D rows qs (ballMatrix M u)) (i,j)) := by
  simp_rw [mapLeft_liftNumerator_apply]
  exact BaireOne.sum Finset.univ (fun t ht => BaireOne.sum Finset.univ
    (fun s hs => (baireOne_pivotAdjugate D M rows qs t s).mul
      ((baireOne_row D M (rows t) i).mul (baireOne_matrix M (qs s,j)))))

end ModNullUniversality.CompactTensor
