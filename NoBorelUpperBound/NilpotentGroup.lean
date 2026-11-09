import Definitions.Def_NoBorelUpperBoundTransfer20261101
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

noncomputable section
open Set Topology

namespace NoBorelUpperBoundFSigma

universe u v
variable {X : Type u} {C : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- A central extension associated with a real continuous bilinear map. -/
def CentralExtension (β : X →L[ℝ] X →L[ℝ] C) := X × X × C

namespace CentralExtension
variable (β : X →L[ℝ] X →L[ℝ] C)

instance : TopologicalSpace (CentralExtension β) :=
  inferInstanceAs (TopologicalSpace (X × X × C))

instance [PolishSpace X] [PolishSpace C] : PolishSpace (CentralExtension β) :=
  inferInstanceAs (PolishSpace (X × X × C))

instance : Group (CentralExtension β) where
  mul a b := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2 + β a.1 b.2.1)
  one := (0, 0, 0)
  inv a := (-a.1, -a.2.1, -a.2.2 + β a.1 a.2.1)
  mul_assoc a b c := by
    apply Prod.ext
    · exact add_assoc _ _ _
    · apply Prod.ext
      · exact add_assoc _ _ _
      · change (a.2.2 + b.2.2 + β a.1 b.2.1) + c.2.2 + β (a.1 + b.1) c.2.1 =
          a.2.2 + (b.2.2 + c.2.2 + β b.1 c.2.1) + β a.1 (b.2.1 + c.2.1)
        simp only [map_add, ContinuousLinearMap.add_apply]
        abel
  one_mul a := by
    apply Prod.ext
    · exact zero_add _
    · apply Prod.ext
      · exact zero_add _
      · change (0 : C) + a.2.2 + β 0 a.2.1 = a.2.2
        simp
  mul_one a := by
    apply Prod.ext
    · exact add_zero _
    · apply Prod.ext
      · exact add_zero _
      · change a.2.2 + (0 : C) + β a.1 0 = a.2.2
        simp
  inv_mul_cancel a := by
    apply Prod.ext
    · exact neg_add_cancel _
    · apply Prod.ext
      · exact neg_add_cancel _
      · change (-a.2.2 + β a.1 a.2.1) + a.2.2 + β (-a.1) a.2.1 = 0
        simp only [map_neg, ContinuousLinearMap.neg_apply]
        abel

@[simp] theorem one_def : (1 : CentralExtension β) = (0, 0, 0) := rfl
theorem mul_def (a b : CentralExtension β) :
    a * b = (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2 + β a.1 b.2.1) := rfl
theorem inv_def (a : CentralExtension β) :
    a⁻¹ = (-a.1, -a.2.1, -a.2.2 + β a.1 a.2.1) := rfl

instance : IsTopologicalGroup (CentralExtension β) where
  continuous_mul := by
    change Continuous (fun p : (X × X × C) × (X × X × C) =>
      (p.1.1 + p.2.1, p.1.2.1 + p.2.2.1, p.1.2.2 + p.2.2.2 + β p.1.1 p.2.2.1))
    exact (continuous_fst.fst.add continuous_snd.fst).prodMk
      ((continuous_fst.snd.fst.add continuous_snd.snd.fst).prodMk
        ((continuous_fst.snd.snd.add continuous_snd.snd.snd).add
          (β.continuous₂.comp (continuous_fst.fst.prodMk continuous_snd.snd.fst))))
  continuous_inv := by
    change Continuous (fun a : X × X × C => (-a.1, -a.2.1, -a.2.2 + β a.1 a.2.1))
    exact continuous_fst.neg.prodMk
      (continuous_snd.fst.neg.prodMk (continuous_snd.snd.neg.add
        (β.continuous₂.comp (continuous_fst.prodMk continuous_snd.fst))))

def left (x : X) : CentralExtension β := (x, 0, 0)
def right (y : X) : CentralExtension β := (0, y, 0)
def center (c : C) : CentralExtension β := (0, 0, c)

@[simp] theorem left_mul (x x' : X) : left β x * left β x' = left β (x + x') := by
  simp [left, mul_def]
@[simp] theorem right_mul (y y' : X) : right β y * right β y' = right β (y + y') := by
  simp [right, mul_def]
@[simp] theorem center_mul (c c' : C) : center β c * center β c' = center β (c + c') := by
  simp [center, mul_def]
@[simp] theorem center_inv (c : C) : (center β c)⁻¹ = center β (-c) := by
  simp [center, inv_def]

def leftHom : Multiplicative X →* CentralExtension β where
  toFun x := left β x.toAdd
  map_one' := rfl
  map_mul' x y := (left_mul β x.toAdd y.toAdd).symm

def rightHom : Multiplicative X →* CentralExtension β where
  toFun y := right β y.toAdd
  map_one' := rfl
  map_mul' x y := (right_mul β x.toAdd y.toAdd).symm

def centerHom : Multiplicative C →* CentralExtension β where
  toFun c := center β c.toAdd
  map_one' := rfl
  map_mul' c d := (center_mul β c.toAdd d.toAdd).symm

theorem mixed_commutator (x y : X) :
    left β x * right β y * (left β x)⁻¹ * (right β y)⁻¹ = center β (β x y) := by
  simp [left, right, center, mul_def, inv_def]

theorem coordinate_factorization (a : CentralExtension β) :
    a = left β a.1 * right β a.2.1 * center β (a.2.2 - β a.1 a.2.1) := by
  simp [left, right, center, mul_def]

theorem center_commutes (c : C) (a : CentralExtension β) :
    center β c * a = a * center β c := by
  simp [center, mul_def, add_comm]

end CentralExtension
end NoBorelUpperBoundFSigma
