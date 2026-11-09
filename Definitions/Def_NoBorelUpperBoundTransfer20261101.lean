import Definitions.Def_NoBorelUpperBound20261101
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

namespace NoBorelUpperBoundFSigma
universe u v w

def GroupCosetRelation {G : Type u} [Group G] (H : Subgroup G) (g g' : G) : Prop :=
  g⁻¹ * g' ∈ H

def GeneratedSubgroup {P : Type u} {G : Type v} [Group G]
    {A : ℕ → Type w} [∀ n, Group (A n)]
    (h : ∀ n, P → (A n →* G)) (p : P) : Subgroup G :=
  Subgroup.closure (⋃ n, Set.range (h n p))

def MembershipSet {P : Type u} {G : Type v} [Group G]
    {A : ℕ → Type w} [∀ n, Group (A n)]
    (h : ∀ n, P → (A n →* G)) (z : P → G) : Set P :=
  {p | z p ∈ GeneratedSubgroup h p}

end NoBorelUpperBoundFSigma
