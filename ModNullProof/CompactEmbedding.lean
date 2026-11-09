import ModNullProof.Coordinates
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace

namespace ModNullUniversality.CompactTensor

abbrev AddTarget := Index → ℕ → AddCircle (1 : ℝ)
abbrev Target := Multiplicative AddTarget

instance : MeasurableSpace Target := borel Target
instance : BorelSpace Target := ⟨rfl⟩
instance : MetrizableSpace Target := inferInstanceAs (MetrizableSpace AddTarget)

/-- Dividing by every positive integer separates real numbers modulo integers. -/
theorem real_eq_zero_of_div_mod_zero (x : ℝ)
    (hx : ∀ n : ℕ, ((x / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) = 0) : x = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt |x|
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsmall : |x / ((N : ℝ) + 1)| < 1 := by
    rw [abs_div,abs_of_pos hpos,div_lt_one hpos]
    linarith
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hx N)
  have hk' : (k : ℝ) = x / ((N : ℝ) + 1) := by simpa using hk
  rw [← hk'] at hsmall
  have hlo : (-1 : ℤ) < k := by exact_mod_cast (abs_lt.mp hsmall).1
  have hhi : k < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hsmall).2
  have hk0 : k = 0 := by omega
  have hz : x / ((N : ℝ) + 1) = 0 := by rw [← hk',hk0]; simp
  exact (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt hpos)

def embedding : Ambient →+ AddTarget where
  toFun u i n := ((u i / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ))
  map_zero' := by ext i n; simp
  map_add' u v := by
    ext i n
    change (((u i + v i) / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [add_div,AddCircle.coe_add]
    rfl

theorem continuous_embedding : Continuous embedding := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro n
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp ((continuous_apply i).div_const _)

theorem embedding_injective : Function.Injective embedding := by
  intro u v huv
  funext i
  apply sub_eq_zero.mp
  apply real_eq_zero_of_div_mod_zero
  intro n
  have h := congrFun (congrFun huv i) n
  change ((u i / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) =
    ((v i / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) at h
  rw [sub_div,AddCircle.coe_sub]
  exact sub_eq_zero.mpr h

def sourceEmbedding : Space →+ AddTarget := embedding.comp coordinates.toAddMonoidHom

theorem continuous_sourceEmbedding : Continuous sourceEmbedding :=
  continuous_embedding.comp continuous_coordinates

theorem sourceEmbedding_injective : Function.Injective sourceEmbedding :=
  embedding_injective.comp coordinates_injective

def fullCompact : PositiveCompacts Target :=
  ⟨⟨univ,isCompact_univ⟩,by simp⟩

def haar : Measure Target := Measure.haarMeasure fullCompact

instance : IsProbabilityMeasure haar := ⟨by exact Measure.haarMeasure_self⟩
instance : Measure.IsHaarMeasure haar := inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure fullCompact))

def compactGroup : CompactMetrizableHaarGroup where
  Carrier := Target
  group := inferInstance
  topology := inferInstance
  compact := inferInstance
  metrizable := inferInstance
  topologicalGroup := inferInstance
  measurable := inferInstance
  borelSpace := inferInstance
  haar := haar
  probability := inferInstance
  haarMeasure := inferInstance

theorem compactGroup_abelian : IsAbelian compactGroup := by
  change ∀ x y : Target, x * y = y * x
  intro x y
  exact mul_comm x y

end ModNullUniversality.CompactTensor
