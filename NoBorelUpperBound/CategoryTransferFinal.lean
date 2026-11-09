import NoBorelUpperBound.CategoryAnalytic
import NoBorelUpperBound.GenericRepresentation

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z

/-- Generic homomorphism category transfer, for a standard Borel parameter
space and countably many continuously parametrized Polish-group generators.
The Borel evaluator and the finite-word analytic membership witnesses are
constructed in the proof rather than assumed. -/
theorem category_transfer
    {P : Type u} [MeasurableSpace P] [StandardBorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, BorelSpace (A n)]
    {Y : Type z} [TopologicalSpace Y] [PolishSpace Y]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) := by
  classical
  letI := upgradeStandardBorel P
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  by_cases hfull : ∀ p, p ∈ MembershipSet h z₀
  · have heq : MembershipSet h z₀ = univ := by ext p; simp [hfull p]
    rw [heq]
    exact MeasurableSet.univ
  · obtain ⟨p,hp⟩ := not_forall.mp hfull
    obtain ⟨f,_,_⟩ := hbound p hp
    letI : Nonempty Y := ⟨f 1⟩
    exact category_transfer_of_generic_codes h hh hc z₀ hz
      (BorelCodes.eval (Y := Y)) BorelCodes.measurable_eval
      BorelCodes.exists_code_of_isBorelMeasurable F hF hbound

end NoBorelUpperBoundFSigma
