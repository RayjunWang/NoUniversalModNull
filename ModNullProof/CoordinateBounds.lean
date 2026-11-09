import ModNullProof.Coordinates
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates

/-- The closed coordinate-topology ball of the scalar plus matrix l1 norm. -/
def coordinateBall (M : ℝ) : Set Ambient :=
  {u | ∀ t : Finset Index, ∑ i ∈ t, |u i| ≤ M}

theorem isClosed_coordinateBall (M : ℝ) : IsClosed (coordinateBall M) := by
  change IsClosed {u : Ambient | ∀ t : Finset Index, ∑ i ∈ t, |u i| ≤ M}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro t
  exact isClosed_le (continuous_finsetSum _ (fun i _ => (continuous_apply i).abs)) continuous_const

theorem coordinateBall_coordinate_le (M : ℝ) {u : Ambient}
    (hu : u ∈ coordinateBall M) (i : Index) : |u i| ≤ M := by
  have h := hu ({i} : Finset Index)
  simpa only [Finset.sum_singleton] using h

theorem isCompact_coordinateBall (M : ℝ) : IsCompact (coordinateBall M) := by
  have hc : IsCompact {u : Ambient | ∀ i, u i ∈ Icc (-M) M} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hc.of_isClosed_subset (isClosed_coordinateBall M)
  intro u hu i
  exact abs_le.mp (coordinateBall_coordinate_le M hu i)

theorem summable_coordinates (p : Space) : Summable (fun i : Index => |coordinates p i|) := by
  apply Summable.sum
  · exact (hasSum_fintype _).summable
  · simpa only [Function.comp_def,coordinates_right,Real.norm_eq_abs] using summable_norm p.2

theorem exists_coordinateBall (p : Space) : ∃ M : ℕ, coordinates p ∈ coordinateBall M := by
  obtain ⟨M,hM⟩ := exists_nat_ge (∑' i : Index, |coordinates p i|)
  refine ⟨M,fun t => ?_⟩
  exact ((summable_coordinates p).sum_le_tsum t (fun _ _ => abs_nonneg _)).trans hM

def ballMatrix (M : ℝ) (u : coordinateBall M) : MatrixL1 S S :=
  ⟨fun ij => u.val (.inr ij), memℓp_gen' (C := M) (by
    intro t
    have h := u.property (t.image Sum.inr)
    rw [Finset.sum_image] at h
    · simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using h
    · intro a ha b hb hab
      exact Sum.inr.inj hab)⟩

def ballSource (M : ℝ) (u : coordinateBall M) : Space :=
  (u.val (.inl ()),ballMatrix M u)

@[simp] theorem ballMatrix_apply (M : ℝ) (u : coordinateBall M) (ij : S × S) :
    ballMatrix M u ij = u.val (.inr ij) := rfl

theorem coordinates_ballSource (M : ℝ) (u : coordinateBall M) :
    coordinates (ballSource M u) = u.val := by
  funext i
  cases i with
  | inl j => cases j; rfl
  | inr ij => rfl

@[simp] theorem ballSource_coordinates (M : ℝ) (p : Space)
    (hp : coordinates p ∈ coordinateBall M) :
    ballSource M ⟨coordinates p,hp⟩ = p :=
  coordinates_injective (coordinates_ballSource M _)

theorem coordinateBall_subset_range (M : ℝ) : coordinateBall M ⊆ range coordinates := by
  intro u hu
  exact ⟨ballSource M ⟨u,hu⟩,coordinates_ballSource M _⟩

end ModNullUniversality.CompactTensor
