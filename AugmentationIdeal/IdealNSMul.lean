import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Basic

/-!
Some lemmas about nsmul of Ideals which is used nowhere in this project

-/

variable {R : Type*} [CommRing R]

open BigOperators
lemma sup_union_finset_single_eq_sup_finset_sup_single (n : ℕ) (f : ℕ → Ideal R) :
    ⨆ x ∈ (Finset.range n : Set ℕ) ∪ ({n} : Set ℕ), f x = (⨆ x ∈ (Finset.range n : Set ℕ), f x) ⊔ f n := by
  rw [iSup_union, iSup_singleton]

@[simp]
lemma sup_succ (n : ℕ) (f : ℕ → Ideal R) : ⨆ x ∈ (Finset.range (Nat.succ n) : Set ℕ), f x = (⨆ i ∈ (Finset.range n : Set ℕ), f i) ⊔ f n:= by
  rw [←sup_union_finset_single_eq_sup_finset_sup_single]
  rw [show (Finset.range n : Set ℕ) ∪ ({n} : Set ℕ) = (Finset.range (Nat.succ n) : Set ℕ) by ext m ; simp ; exact Nat.lt_succ.symm]

lemma mem_fsup_iff_sum (n : ℕ) (f : ℕ → Ideal R) : ∀ x, x ∈ ⨆ i ∈ (Finset.range n : Set ℕ), f i ↔ ∃ g : ℕ → R, (∀ i ∈ Finset.range n, g i ∈ f i) ∧ x = ∑ i in Finset.range n, g i := by
  induction n with
  | zero =>
    simp [Submodule.iSup_eq_span, Set.iUnion_of_empty,
          Submodule.span_empty, Ideal.mem_bot]
  | succ n ih =>
    intro x
    constructor
    · intro hx
      rw [sup_succ] at hx
      rw [@Submodule.mem_sup] at hx
      obtain ⟨y,⟨hy,⟨z,⟨hz,hyz⟩⟩⟩⟩ := hx
      rw [ih y] at hy
      obtain ⟨g, ⟨hg₁, hg₂⟩⟩ := hy
      let g' : ℕ → R := fun m =>
        if m = n then z else g m
      use g'
      constructor
      · intro i hi
        rw [@Finset.mem_range_succ_iff, @Nat.le_iff_lt_or_eq] at hi
        cases hi with
        | inl h =>
          specialize hg₁ i
          dsimp
          have hi' : i ≠ n := Nat.ne_of_lt h
          rw [if_neg hi']
          apply hg₁
          exact Finset.mem_range.mpr h
        | inr h =>
          dsimp ; rwa [if_pos h, h]
      · rw [← hyz] ;
        rw [Finset.sum_range_succ]
        dsimp
        rw [if_pos, add_left_inj]
        rw [←Finset.sum_coe_sort]
        have hi' (i : Finset.range n) : ↑i ≠ n := by
          obtain ⟨_, hi''⟩ := i
          rw [@Finset.mem_range] at hi''
          exact Nat.ne_of_lt hi''
        conv =>
          enter [2, 2, i]
          rw [if_neg (hi' i)]
        rwa [Finset.sum_coe_sort]
        rfl
    · rintro ⟨g, ⟨hg₁, hg₂⟩⟩
      rw [sup_succ]
      rw [Submodule.mem_sup]
      rw [Finset.sum_range_succ] at hg₂
      use ∑ x in Finset.range n, g x
      constructor
      · rw [ih]
        use g
        constructor
        · intro i hi
          specialize hg₁ i
          apply hg₁
          simp at hi ⊢
          exact Nat.lt.step hi
        · rfl
      · use (g n)
        constructor
        · apply hg₁
          exact Finset.self_mem_range_succ n
        · exact hg₂.symm

theorem smul_eq_sup (n : ℕ) (I : Ideal R) : n • I = ⨆ i ∈ (Finset.range n : Set ℕ), I := by
  ext i
  induction n with
  | zero => simp
  | succ n =>
    rw [succ_nsmul, sup_succ]
    simp only [nsmul_eq_mul, Submodule.add_eq_sup, ge_iff_le, Ideal.sup_mul_left_self,
      Finset.coe_range, Set.mem_Iio, not_lt, iSup_le_iff, le_refl, implies_true, forall_const,
      sup_of_le_right]

theorem sup_eq_sum (n : ℕ) (I : Ideal R) : ⨆ i ∈ (Finset.range n : Set ℕ), I = ∑ _i : Finset.range n, I := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sup_succ, ih, ← Submodule.add_eq_sup]
    simp

theorem smul_eq_sum (n : ℕ) (I : Ideal R) : n • I = ∑ _i : Finset.range n, I := by
  ext x
  rw[smul_eq_sup, sup_eq_sum]

lemma mem_smul_eq_sum (n : ℕ) (I : Ideal R) : ∀ x, x ∈ n • I ↔ ∃ g : Finset.range n → I, x = ∑ i : Finset.range n, g i := by
  rw [smul_eq_sup]
  intro x
  rw [mem_fsup_iff_sum]
  constructor
  · rintro ⟨g, ⟨hg₁, hg₂⟩⟩
    use fun i => {
      val := g i
      property := by
        obtain ⟨i', hi'⟩ := i
        simp
        exact hg₁ i' hi'
    }
    simp
    rwa [@Finset.sum_attach]
  · rintro ⟨g, hg⟩
    use fun i =>
      if h : i ∈ Finset.range n then ↑(g ⟨i, h⟩) else 0
    constructor
    · intro i hi
      rw [dif_pos hi]
      exact Submodule.coe_mem (g { val := i, property := hi })
    · rw [←Finset.sum_coe_sort]
      conv =>
        enter [2, 2, i]
        rw [dif_pos i.property]
        simp
      simp at hg ⊢
      assumption
