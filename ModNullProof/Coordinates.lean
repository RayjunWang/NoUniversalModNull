import Definitions.Def_ModNullCompact20261109
import NoBorelUpperBound.L1Coordinates

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

abbrev S := List ℕ
abbrev Space := ℝ × NoBorelUpperBoundFSigma.L1Coordinates.MatrixL1 S S
abbrev Index := Unit ⊕ (S × S)
abbrev Ambient := Index → ℝ

instance : MeasurableSpace Space := borel Space
instance : BorelSpace Space := ⟨rfl⟩

def coordinates : Space →ₗ[ℝ] Ambient where
  toFun p := Sum.elim (fun _ => p.1) (fun ij => p.2 ij)
  map_add' p q := by funext i; cases i <;> rfl
  map_smul' a p := by funext i; cases i <;> rfl

@[simp] theorem coordinates_left (p : Space) (u : Unit) :
    coordinates p (.inl u) = p.1 := rfl

@[simp] theorem coordinates_right (p : Space) (ij : S × S) :
    coordinates p (.inr ij) = p.2 ij := rfl

theorem coordinates_injective : Function.Injective coordinates := by
  intro p q h
  apply Prod.ext
  · exact congrFun h (.inl ())
  · ext ij
    exact congrFun h (.inr ij)

theorem continuous_coordinates : Continuous coordinates := by
  apply continuous_pi
  intro i
  cases i with
  | inl u => exact continuous_fst
  | inr ij =>
    exact (lp.evalCLM ℝ (fun _ : S × S => ℝ) 1 ij).continuous.comp continuous_snd

end ModNullUniversality.CompactTensor
