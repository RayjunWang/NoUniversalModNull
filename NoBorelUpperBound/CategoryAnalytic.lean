import NoBorelUpperBound.CategoryTransfer
import NoBorelUpperBound.CategoryQuantifier
import NoBorelUpperBound.CategoryMembership
import Mathlib.MeasureTheory.Group.Arithmetic

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z t

section Witness
variable {P : Type u} {C : Type v} {G : Type w} {A : ℕ → Type z} {Y : Type t}
    [Group G] [TopologicalSpace G]
    [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]

/-- Generic generator invariance and generic designated-element separation. -/
def GenericWitness (h : ∀ n, P → (A n →* G)) (z₀ : P → G)
    (eval : C → G → Y) (F : Setoid Y) (pc : P × C) : Prop :=
  (∀ n, ∀ᶠ ga : G × A n in residual (G × A n),
    F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))) ∧
  (∀ᶠ g in residual G, ¬ F.r (eval pc.2 g) (eval pc.2 (g*z₀ pc.1)))

end Witness

section BorelWitness
variable {P : Type u} [TopologicalSpace P] [PolishSpace P]
    [MeasurableSpace P] [BorelSpace P]
    {C : Type v} [TopologicalSpace C] [PolishSpace C]
    [MeasurableSpace C] [BorelSpace C]
    {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type z} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, BorelSpace (A n)]
    {Y : Type t} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]

/-- The set of generic tests is genuinely Borel, including its category
quantifiers. -/
theorem measurableSet_genericWitness
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (F : Setoid Y) (hF : IsBorelRelation F.r) :
    MeasurableSet {pc | GenericWitness h z₀ eval F pc} := by
  have hFb : MeasurableSet {yy : Y × Y | F.r yy.1 yy.2} := by
    unfold IsBorelRelation at hF
    rwa [← BorelSpace.measurable_eq] at hF
  have hgen (n : ℕ) : MeasurableSet {pc : P × C |
      ∀ᶠ ga : G × A n in residual (G × A n),
        F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))} := by
    apply measurableSet_residual_sections (S := {p : (P × C) × (G × A n) |
      F.r (eval p.1.2 p.2.1) (eval p.1.2 (p.2.1 * h n p.1.1 p.2.2))})
    apply hFb.preimage (f := fun p : (P × C) × (G × A n) =>
      (eval p.1.2 p.2.1, eval p.1.2 (p.2.1 * h n p.1.1 p.2.2)))
    apply Measurable.prodMk
    · exact heval.comp (measurable_fst.snd.prodMk measurable_snd.fst)
    · exact heval.comp (measurable_fst.snd.prodMk
        (measurable_snd.fst.mul ((hh n).comp
          (measurable_fst.fst.prodMk measurable_snd.snd))))
  have hsep : MeasurableSet {pc : P × C | ∀ᶠ g in residual G,
      ¬ F.r (eval pc.2 g) (eval pc.2 (g*z₀ pc.1))} := by
    apply measurableSet_residual_sections (S := {p : (P × C) × G |
      ¬ F.r (eval p.1.2 p.2) (eval p.1.2 (p.2 * z₀ p.1.1))})
    apply hFb.compl.preimage (f := fun p : (P × C) × G =>
      (eval p.1.2 p.2, eval p.1.2 (p.2 * z₀ p.1.1)))
    apply Measurable.prodMk
    · exact heval.comp (measurable_fst.snd.prodMk measurable_snd)
    · exact heval.comp (measurable_fst.snd.prodMk
        (measurable_snd.mul (hz.comp measurable_fst.fst)))
  have hforall : MeasurableSet {pc : P × C | ∀ n,
      ∀ᶠ ga : G × A n in residual (G × A n),
        F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))} := by
    simpa only [setOf_forall] using MeasurableSet.iInter hgen
  exact hforall.inter hsep

/-- Analytic generic witness projection equals the complement of membership
when actual reductions are available there. -/
theorem genericWitness_projection_eq_compl
    (h : ∀ n, P → (A n →* G)) (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (eval : C → G → Y) (F : Setoid Y)
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    Prod.fst '' {pc : P × C | GenericWitness h z₀ eval F pc} = (MembershipSet h z₀)ᶜ := by
  ext p
  constructor
  · rintro ⟨⟨q,c⟩,⟨hgen,hsep⟩,hqp⟩
    dsimp at hqp
    subst q
    exact generic_tests_exclude_membership (eval c) F h p (z₀ p) hgen hsep
  · intro hp
    obtain ⟨f,hf,hred⟩ := hbound p hp
    obtain ⟨c,hag⟩ := hrep f hf
    refine ⟨(p,c),⟨?_,?_⟩,rfl⟩
    · intro n
      exact generic_test_of_reduction_agreement f (eval c) F (GeneratedSubgroup h p)
        hred hag (h n p) (hc n p) (fun a => Subgroup.subset_closure (mem_iUnion.mpr ⟨n,mem_range_self a⟩))
    · exact generic_separation_of_reduction_agreement f (eval c) F (GeneratedSubgroup h p)
        hred hag (z₀ p) hp

/-- Category transfer once a universal Borel evaluation modulo meager
agreement and analyticity of the designated membership family are supplied.
Both premises are explicit infrastructure obligations. -/
theorem membership_measurable_of_generic_codes
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hM : AnalyticSet (MembershipSet h z₀))
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) := by
  have hW := measurableSet_genericWitness h hh z₀ hz eval heval F hF
  have hproj : AnalyticSet (Prod.fst '' {pc : P × C | GenericWitness h z₀ eval F pc}) :=
    hW.analyticSet.image_of_continuous continuous_fst
  rw [genericWitness_projection_eq_compl h hc z₀ eval F hrep hbound] at hproj
  exact hM.measurableSet_of_compl hproj

/-- The generic homomorphism category-transfer principle. The sole coding
input is a jointly Borel family representing all Borel maps modulo meager
agreement. -/
theorem category_transfer_of_generic_codes
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) :=
  membership_measurable_of_generic_codes h hh hc z₀ hz eval heval hrep F hF
    (analyticSet_membershipSet h hh z₀ hz) hbound

end BorelWitness
end NoBorelUpperBoundFSigma
