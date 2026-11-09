import ModNullProof.BorelComplexity

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace

namespace ModNullUniversality

variable {X : Type*} [TopologicalSpace X]

theorem isKSigma_of_isCompact {s : Set X} (hs : IsCompact s) : IsKSigma s :=
  ⟨fun _ => s,fun _ => hs,by ext x; simp⟩

theorem isKSigma_iUnion_nat {s : ℕ → Set X} (hs : ∀ n, IsKSigma (s n)) :
    IsKSigma (⋃ n, s n) := by
  classical
  choose C hC hseq using hs
  refine ⟨fun k => C k.unpair.1 k.unpair.2,fun k => hC _ _,?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n,hn⟩
    rw [hseq n] at hn
    obtain ⟨m,hm⟩ := mem_iUnion.mp hn
    exact ⟨Nat.pair n m,by simpa using hm⟩
  · rintro ⟨k,hk⟩
    refine ⟨k.unpair.1,?_⟩
    rw [hseq]
    exact mem_iUnion.mpr ⟨k.unpair.2,hk⟩

theorem isKSigma_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, IsKSigma (s i)) : IsKSigma (⋃ i, s i) := by
  classical
  by_cases h : Nonempty ι
  · letI := h
    obtain ⟨e,he⟩ := exists_surjective_nat ι
    have hseq : (⋃ i, s i) = ⋃ n : ℕ, s (e n) := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        obtain ⟨n,rfl⟩ := he i
        exact ⟨n,hi⟩
      · rintro ⟨n,hn⟩
        exact ⟨e n,hn⟩
    rw [hseq]
    exact isKSigma_iUnion_nat (fun n => hs (e n))
  · letI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
    exact ⟨fun _ => ∅,fun _ => isCompact_empty,by ext x; simp⟩

theorem isKSigma_inter_isClosed {s t : Set X} (hs : IsKSigma s) (ht : IsClosed t) :
    IsKSigma (s ∩ t) := by
  obtain ⟨C,hC,rfl⟩ := hs
  refine ⟨fun n => C n ∩ t,fun n => (hC n).inter_right ht,?_⟩
  ext x
  simp only [mem_inter_iff,mem_iUnion]
  exact ⟨fun ⟨⟨i,hi⟩,ht⟩ => ⟨i,hi,ht⟩,
    fun ⟨i,hi,ht⟩ => ⟨⟨i,hi⟩,ht⟩⟩

end ModNullUniversality
