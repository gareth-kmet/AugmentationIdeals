/-
Authors : Gareth Kmet
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic

/-!
# Helper

This file defines helpful lemmas surrounding `Finset` and `Finsupp`. These lemmas mainly foccus on the finite sums of
different unions, sdiffs, and intersections and on the manipulation of supports.
-/

open Classical BigOperators

variable {A A' R G R' R'': Type*}


instance Ideal.mul [Ring R] (I : Ideal R) : Mul I where
  mul f g := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', hg⟩ := g
    exact ⟨f' * g', Ideal.mul_mem_left I f' hg⟩


namespace Set.iUnion

section Mul

lemma union_of_union_of_prod_toSet (α β : Set R) [Mul R] : ⋃ s ∈ α, ⋃ t ∈ β, {s * t} = {s * t | (s ∈ α) (t ∈ β)} := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Set.mem_setOf_eq]
  conv => enter [2, 1, s, 2, 1, t, 2] ; rw [eq_comm]

end Mul

end Set.iUnion

namespace Finset

section SetTheory

lemma set_is_union_of_set_and_sdiff (I J : Finset A) : I = (I ∩ J) ∪ (I \ J) := by
  ext a
  constructor
  · intro ha
    rw [Finset.mem_union, Finset.mem_inter]
    by_cases a ∈ J
    · exact Or.inl { left := ha, right := h }
    · exact Or.inr <| by rw [Finset.mem_sdiff] ; exact { left := ha, right := h }
  · intro ha
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, ←and_or_left] at ha
    obtain ⟨l,_⟩ := ha ; exact l


lemma image_sdiff_is_sdiff_image (I J : Finset A) (γ : A → A) (hγ : ∀ g₁ g₂ : A, γ g₁ = γ g₂ → g₁ = g₂) : γ '' (I \ J) = (γ '' I) \ (γ '' J) := by
  ext x
  constructor
  · rintro ⟨w, ⟨⟨hw₁, hw₁'⟩, hw₂⟩⟩
    simp only [Set.mem_diff, Set.mem_image, Finset.mem_coe, not_exists, not_and]
    constructor
    · use w ; exact ⟨hw₁, hw₂⟩
    · intro z hz h
      rw [←hw₂] at h ; specialize hγ z w
      have hzw : z = w := hγ h ; rw[hzw] at hz
      exact hw₁' hz
  · simp only [Set.mem_diff, Set.mem_image, Finset.mem_coe, not_exists, not_and, and_imp,
    forall_exists_index]
    intro z₁ hz₁ hz₁' h
    use z₁ ; constructor ; constructor
    · assumption
    · intro hz₁'' ; specialize h z₁
      apply h ; assumption'
    · assumption


lemma union_decomp (I J : Finset A) : I ∩ J ∪ I \ J ∪ J \ I = I ∪ J := by
  ext x ; simp only [mem_sdiff, mem_union, mem_inter]
  constructor
  · intro hx ; rw[or_assoc] at hx
    rcases hx with ⟨hI, _⟩ | ⟨hI, _⟩ | ⟨hJ, _⟩
    exact Or.inl hI ; exact Or.inl hI ; exact Or.inr hJ
  · intro hx
    by_cases x ∈ I ∧ x ∈ J
    · exact Or.inl (Or.inl h)
    · have h₁ : x ∉ I ∨ x ∉ J := by exact not_and_or.mp h
      by_cases x ∈ I
      · exact Or.inl <| Or.inr <| by
          constructor ; exact h
          intro h₂
          cases h₁ with
          | inl hl => exact hl h
          | inr hr => exact hr h₂
      · exact Or.inr <| by
          constructor
          · cases hx with
            | inl hl => exfalso ; exact h hl
            | inr hr => exact hr
          · exact h

lemma empty_decomp (I J : Finset A) : (I ∩ J ∪ I \ J) ∩ (J \ I) = ∅ := by
  ext x ; simp only [mem_sdiff, mem_union, mem_inter]
  constructor
  · rintro ⟨⟨hI, _⟩ | ⟨_, hnJ⟩, ⟨hJ, hnI⟩⟩
    · exact (hnI hI).elim
    · exact (hnJ hJ).elim
  · intro hx ; exfalso
    exact (List.mem_nil_iff x).mp hx


end SetTheory

section Sum

variable {f g : A → R} {f' g' : A → R'}
  [AddCommMonoid R] [DecidableEq A] [AddCommGroup R']

lemma sum_union_disjoint_is_disjoint_sum (I J : Finset A) (hij : I ∩ J = ∅) : (∑ x in (I ∪ J), f x) = (∑ x in I, f x) + (∑ x in J, f x) := by
  rw [← @Finset.sum_union_inter, hij]
  simp only [sum_empty, add_zero]

lemma sum_union_is_left_and_sdiff (I J : Finset A) : (∑ x in (I ∪ J), f x) = (∑ x in I, f x) + (∑ x in J \ I, f x) := by
  rw [← Finset.sum_union]
  · suffices I ∪ J = I ∪ J \ I by rw[this]
    rw [union_sdiff_self_eq_union]
  · exact disjoint_sdiff

lemma sum_union_is_right_and_sdiff (I J : Finset A) : (∑ x in (I ∪ J), f x) = (∑ x in I \ J, f x) + (∑ x in J, f x) := by
  rw [← Finset.sum_union]
  · suffices I ∪ J = I \ J ∪ J by rw[this]
    rw [sdiff_union_self_eq_union]
  · exact sdiff_disjoint

lemma sum_union_sdiff_is_sum_sdiff (I J K : Finset A) : ∑ x in (I ∪ J) \ K, f' x = (∑ x in I \ K, f' x) + (∑ x in J \ K, f' x) - (∑ x in (I ∩ J) \ K, f' x) := by
  rw [← @sum_union_inter]
  rw [show I \ K ∪ J \ K = (I ∪ J) \ K by
    ext a ; simp only [mem_union, mem_sdiff]
    constructor
    · rintro (⟨ha₁, ha₂⟩ | ⟨ha₃, ha₄⟩)
      · exact ⟨Or.inl ha₁, ha₂⟩
      · exact ⟨Or.inr ha₃, ha₄⟩
    · rintro (⟨ha₁ | ha₂, ha₃⟩)
      · exact Or.inl ⟨ha₁, ha₃⟩
      · exact Or.inr ⟨ha₂, ha₃⟩
  ]
  rw [show (I \ K) ∩ (J \ K) = (I ∩ J) \ K by
    ext a ; simp only [mem_inter, mem_sdiff]
    constructor
    · rintro ⟨⟨ha₁, ha₂⟩, ⟨ha₃, _⟩⟩
      exact ⟨⟨ha₁, ha₃⟩, ha₂⟩
    · rintro ⟨⟨ha₁, ha₂⟩, ha₃⟩
      exact ⟨⟨ha₁, ha₃⟩, ⟨ha₂, ha₃⟩⟩
  ]
  rw [add_sub_cancel]

lemma union_sum_decomp (I J : Finset G) (f : G → R) : (∑ x in (I ∪ J), f x) = (∑ x in (I ∩ J), f x) + (∑ x in (I \ J), f x) + (∑ x in (J \ I), f x) := by
  rw[←Finset.sum_union_inter]
  have h₁ : I ∩ J ∩ (I \ J) = ∅ := by simp only [inter_assoc, inter_sdiff_self, inter_empty]
  rw [h₁] ; simp only [sum_empty, add_zero]
  rw [←Finset.sum_union_inter, union_decomp, empty_decomp]
  simp only [sum_empty, add_zero]

variable {φ ψ : A → A} {α β : Finset A} (γ : A → R)
instance : Finite (φ '' ↑β) := Finite.Set.finite_image (↑β) φ

lemma sum_of_funct_is_sum_over_image (h : ∀ x₁ ∈ β, ∀ x₂ ∈ β, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a in β, γ (φ a) = ∑ b in (φ '' β).toFinset, γ b := by
  simp only [Set.toFinset_image, Finset.toFinset_coe] ; rwa [Finset.sum_image]

lemma sum_of_funct_is_sum_over_image' (h : ∀ x₁ ∈ β, ∀ x₂ ∈ β, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a in β, γ (ψ (φ a)) = ∑ b in (φ '' β).toFinset, γ (ψ b) := by
  simp only [Set.toFinset_image, Finset.toFinset_coe] ; rwa [Finset.sum_image]

variable (β) in
lemma sum_of_funct_is_sum_over_image'₂ (h : ∀ x₁ x₂ : A, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a in β, γ (ψ (φ a)) = ∑ b in (φ '' β).toFinset, γ (ψ b) := by
  simp only [Set.toFinset_image, Finset.toFinset_coe] ; rw [Finset.sum_image]
  intro x _ y _ hxy
  apply h ; assumption

lemma sum_of_funct_is_sum_over_image''  (h : ∀ x₁ ∈ β, ∀ x₂ ∈ β, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a : β, γ (φ a) = ∑ b : (φ '' β).toFinset, γ b := by
  simp only [univ_eq_attach,@sum_attach, Set.toFinset_image, toFinset_coe]
  rw [sum_image, ← @sum_coe_sort_eq_attach]
  refine (sum_subtype β ?_ fun a => γ (φ a)).symm
  simp only [implies_true]
  assumption

lemma sum_of_funct_is_sum_over_equiv (ϕ : A ≃ A') :
    ∑ a in β, γ a = ∑ b in (ϕ '' β).toFinset, γ (ϕ.symm b) := by
  simp only [Set.toFinset_image, toFinset_coe, EmbeddingLike.apply_eq_iff_eq, imp_self,
    implies_true, sum_image, Equiv.symm_apply_apply]

variable (α f) in
lemma sum_in_eq_sum_type : ∑ a in α, f a = ∑ a : α, f ↑a := by
  rw [← Finset.sum_attach]
  simp only [univ_eq_attach]

lemma sum_of_funct_is_sum_over_image_equiv_nat (β : Finset G) (γ : G → R) (φ : ℕ → G) (ψ : G → ℕ)
    (h : ∀ x ∈ β, φ (ψ x) = x) (inj : ∀ x ∈ β, ∀ y ∈ β, ψ x = ψ y → x = y) :
    ∑ a in β, γ a = ∑ i in (ψ '' β).toFinset, γ (φ i) := by
  simp only [Set.toFinset_image, toFinset_coe] ; rw [sum_image]
  conv => rhs ; rw [sum_in_eq_sum_type]
  conv => enter [2, 2, x] ; rw [h ↑x x.property]
  rwa [← sum_in_eq_sum_type]

lemma sum_of_funct_is_sum_over_image_equiv_nat' (φ : ℕ → A) (ψ : A → ℕ)
    (h : ∀ x ∈ β, φ (ψ x) = x) (inj : ∀ x ∈ β, ∀ y ∈ β, ψ x = ψ y → x = y) :
    ∑ a : β, γ a = ∑ i : (ψ '' β).toFinset, γ (φ i) := by
  rw [← sum_in_eq_sum_type]
  conv => rhs ; rw [← sum_in_eq_sum_type (fun a => γ (φ a)) (ψ '' β).toFinset]
  rw [sum_of_funct_is_sum_over_image_equiv_nat]
  assumption'

variable (β) in
lemma sum_equiv_sum_indexed_by_card :
    ∑ a : β, γ a = ∑ i : Fin β.card, γ (β.equivFin.invFun i) := by
  by_cases hcard : β.card = 0
  · rw [@card_eq_zero] at hcard ; rw [hcard]
    simp only [univ_eq_empty, sum_empty, card_empty, Equiv.invFun_as_coe]
  · let φ : ℕ → A := fun i => by
      by_cases i < β.card
      · exact ↑(β.equivFin.invFun ⟨i,h⟩)
      · exact ↑(β.equivFin.invFun ⟨0, Nat.pos_of_ne_zero hcard⟩)
    let ψ : A → ℕ := fun g => by
      by_cases g ∈ β
      · exact ↑(β.equivFin.toFun ⟨g,h⟩)
      · exact 0
    have hψ : ∀ b : β, ↑(β.equivFin.toFun b) = ψ ↑b := by simp only [Equiv.toFun_as_coe,
      coe_mem, Subtype.coe_eta, dite_eq_ite, ite_true, Subtype.forall, implies_true]
    have hh : ∀ x ∈ β, φ (ψ x) = x := by
      intro _ h' ; simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, dif_pos h', Fin.is_lt,
        Fin.eta, Equiv.symm_apply_apply, dite_eq_ite, ite_true]
    have inj : ∀ x ∈ β, ∀ y ∈ β, ψ x = ψ y → x = y := by
      intro x hx y hy
      rw [← hψ ⟨x,hx⟩, ← hψ ⟨y,hy⟩]
      have h : Function.Injective β.equivFin.toFun := by
        rw [@Equiv.toFun_as_coe]
        exact Equiv.injective (equivFin β)
      intro heq
      unfold Function.Injective at h
      have h' : (⟨x,hx⟩ : β) = ⟨y,hy⟩ → x = y := by simp only [Subtype.mk.injEq,
        imp_self]
      apply h' ; apply h
      exact Fin.ext heq
    rw [@sum_of_funct_is_sum_over_image_equiv_nat' A R _ β γ φ ψ hh inj]
    rw [← sum_in_eq_sum_type (fun x => γ (φ x)) (Set.toFinset (ψ '' β))]
    rw [sum_fin_eq_sum_range]
    have hf : Set.toFinset (ψ '' ↑β) = range (card β) := by
      ext i
      constructor
      · intro hi
        rw [@Set.mem_toFinset] at hi
        obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := hi
        dsimp only [Equiv.toFun_as_coe] at hx₂
        rw [@mem_coe] at hx₁
        rw [dif_pos hx₁] at hx₂
        simp only [mem_range]
        have hi' : ∃ j : Fin β.card, ↑j = i := by
          use (β.equivFin ⟨x,hx₁⟩)
        obtain ⟨⟨j,hj₁⟩, hj₂⟩ := hi'
        simp only at hj₂
        rwa [← hj₂]
      · intro hi
        rw [Set.mem_toFinset]
        rw [@Set.mem_image]
        dsimp only [Equiv.toFun_as_coe]
        simp only [mem_range] at hi
        use β.equivFin.invFun ⟨i, hi⟩
        simp only [Equiv.invFun_as_coe, mem_coe, coe_mem, Subtype.coe_eta, Equiv.apply_symm_apply,
          dite_eq_ite, ite_true, and_self]
    rw [hf, sum_in_eq_sum_type]
    conv => rhs ; rw [sum_in_eq_sum_type]
    congr ; ext j
    obtain ⟨i, hi⟩ := j
    simp only [mem_range] at hi
    simp only [Equiv.invFun_as_coe, dif_pos hi]

variable (β) in
lemma sum_equiv_sum_indexed_by_card' :
    ∑ a in β, γ a = ∑ i : Fin β.card, γ (β.equivFin.invFun i) := by
  rw [sum_in_eq_sum_type]
  exact sum_equiv_sum_indexed_by_card β γ

variable (α β) [CommRing R''] in
lemma sum_mul_sum_is_sum_sum_mul (φ ψ : A → R'') : (∑ a in α, ψ a) * (∑ b in β, φ b) = ∑ a in α, ∑ b in β, ψ a * φ b := by
  conv => enter [2, 2, a] ; rw[Finset.mul_sum.symm , mul_comm]
  conv => rhs ; rw[←Finset.mul_sum]
  rw[mul_comm]

end Sum

section Subsets

noncomputable def subset_to_finset {t : Set A} {s : Finset A} (ht : t ⊆ s) : Finset A := Set.Finite.toFinset <| Set.Finite.subset (s.finite_toSet) ht

end Subsets

end Finset

namespace Finsupp

variable [CommRing R]
variable (f g : G →₀ R)

lemma sum_of_sum_support_eq_sum_of_union_support : (∑ a in (f+g).support, (f+g) a) = (∑ a in ((f.support ∪ g.support)), (f + g) a) := by
  have hsup : (f+g).support = (f.support ∪ g.support) ∩ (f+g).support := by
    rw[Finset.inter_eq_right.mpr] ; exact Finsupp.support_add
  conv => enter [1, 1] ; rw[hsup]
  apply Eq.symm
  conv => enter [1,1] ; rw [Finset.set_is_union_of_set_and_sdiff (f.support ∪ g.support) (f + g).support]
  simp only [Finset.sum_union_disjoint_is_disjoint_sum, Finset.inter_assoc, Finset.inter_sdiff_self, Finset.inter_empty]
  suffices (∑ a in ((f.support ∪ g.support) \ (f+g).support), (f + g) a) = 0 from add_right_eq_self.mpr this
  rw[Finset.sum_eq_zero] ; intro x ; rw[Finset.mem_sdiff]
  rintro ⟨_, hx⟩ ; exact Finsupp.not_mem_support_iff.mp hx

lemma sum_of_sum_support_eq_sum_of_parts : (∑ a in (f+g).support, (f+g) a) = (∑ a in f.support, (f + g) a) + (∑ a in g.support, (f + g) a) - (∑ a in ((f.support ∩ g.support)), (f + g) a) := by
  rw [sum_of_sum_support_eq_sum_of_union_support, ←Finset.sum_union_inter] ; simp only [add_sub_cancel]

lemma sum_comp_support_eq_zero : (∑ a in (f.support \ g.support), g a) = 0 := by
  rw[Finset.sum_eq_zero] ; intro x ; rw[Finset.mem_sdiff]
  rintro ⟨_, hx⟩ ; exact Finsupp.not_mem_support_iff.mp hx

lemma sum_inter_support_is_op_support : (∑ a in (f.support ∩ g.support), g a) = (∑ a in f.support, g a) := by
  rw[←add_zero (∑ a in (f.support ∩ g.support), g a), ←sum_comp_support_eq_zero f g]
  suffices 0 = (∑ a in (f.support ∩ g.support) ∩ (f.support \ g.support), g a) by rw [Finset.sum_inter_add_sum_diff]
  suffices ∀ a ∈ (f.support ∩ g.support) ∩ (f.support \ g.support), g a = 0 by rw [Finset.sum_eq_zero this]
  intro a ; rw [Finset.mem_inter]
  rintro ⟨_, ha⟩ ; rw [Finset.mem_sdiff] at ha
  obtain ⟨_, hg⟩ := ha ; exact Finsupp.not_mem_support_iff.mp hg

lemma sum_inter_support_eq_sum_parts : (∑ a in ((f.support ∩ g.support)), (f + g) a) = (∑ a in f.support, g a) + (∑ a in g.support, f a) := by
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  rw [sum_inter_support_is_op_support, Finset.inter_comm, sum_inter_support_is_op_support g f, add_comm]

theorem sum_coefficents_is_add_hom : (∑ a in (f+g).support, (f+g) a) = (∑ a in f.support, f a) + (∑ a in g.support, g a) := by
  rw [sum_of_sum_support_eq_sum_of_parts, sum_inter_support_eq_sum_parts]
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  ring

lemma mul_outside_supp_is_zero : ∑ u in (f.support \ g.support), f u * g u = 0 := by
  suffices ∀ u ∈ (f.support \ g.support), f u * g u = 0 from Finset.sum_eq_zero this
  intro u hu
  rw [Finset.mem_sdiff] at hu ; obtain ⟨_, hu'⟩ := hu
  replace hu' : g u = 0 := Finsupp.not_mem_support_iff.mp hu'
  exact mul_eq_zero_of_right (f u) hu'

lemma outside_supp_mul_is_zero : ∑ u in (g.support \ f.support), f u * g u = 0 := by
  conv => enter [1, 2, u] ; rw [mul_comm]
  exact mul_outside_supp_is_zero g f

lemma inter_supp_mul_is_union_supp_mul : ∑ u in (f.support ∩ g.support), f u * g u = (∑ u in (f.support ∪ g.support), f u * g u) := by
  simp only [Finset.union_sum_decomp, mul_outside_supp_is_zero, add_zero, outside_supp_mul_is_zero]

/-
Lemmas about finite support functions and their sums
-/
lemma sum_support_diff_singleton_is_sum_plus_singleton' (f : G →₀ R) (k : G) :
    ∑ a in f.support, (Finsupp.single a (f a) k) = (∑ a in (f.support \ {k}), (Finsupp.single a (f a) k)) + (Finsupp.single k (f k) k) := by
  by_cases k ∈ f.support
  · exact Finset.sum_eq_sum_diff_singleton_add h fun x => Finsupp.single x (f x) k
  · rw [Finsupp.not_mem_support_iff.mp h, Finsupp.single_apply_eq_zero.mpr (congrFun rfl)]
    rw [add_zero, Finset.sum_subset]
    · apply Finset.subset_of_eq
      exact (Finset.sdiff_singleton_eq_self h).symm
    · intro x' _ hx'
      rw[Finsupp.not_mem_support_iff.mp hx', Finsupp.single_apply_eq_zero.mpr (congrFun rfl)]

lemma sum_support_diff_singleton_is_sum_plus_singleton (f : G →₀ R) (k : G) :
    ∑ a in f.support, f a = (∑ a in (f.support \ {k}), f a) + f k := by
  by_cases k ∈ f.support
  · exact Finset.sum_eq_sum_diff_singleton_add h f
  · rw [Finsupp.not_mem_support_iff.mp h, add_zero, Finset.sum_subset]
    · apply Finset.subset_of_eq
      exact (Finset.sdiff_singleton_eq_self h).symm
    · intro x' _ hx'
      exact Finsupp.not_mem_support_iff.mp hx'

lemma sum_of_single_at_diff_is_zero (f : G →₀ R) (x : G) : ∑ a in f.support \ {x}, Finsupp.single a (f a) x = 0 := by
  suffices ∀ a ∈ f.support \ {x}, Finsupp.single a (f a) x = 0 by
    exact Finset.sum_eq_zero this
  intro a ; rw [Finset.mem_sdiff]
  rintro ⟨_, ha⟩
  apply List.ne_of_not_mem_cons at ha
  exact Finsupp.single_eq_of_ne ha

theorem finsupp_is_sum_of_singles (f : G →₀ R) : f = ∑ a in f.support, Finsupp.single a (f a) := by
  ext x ; rw [Finset.sum_apply']
  rw [sum_support_diff_singleton_is_sum_plus_singleton']
  rw [Finsupp.single_eq_same, self_eq_add_left, sum_of_single_at_diff_is_zero]

theorem finsupp_is_linear_combo_of_singles (f : G →₀ R) : f = ∑ a in f.support, (f a) • (Finsupp.single a (1 : R)) := by
  conv => enter [2, 2, a] ; rw[Finsupp.smul_single' (f a) a 1, mul_one]
  exact Finsupp.finsupp_is_sum_of_singles f

lemma sum_single_is_single_sum (f : G →₀ R) (g : G) : (∑ a in f.support, (f a) • (Finsupp.single g (1 : R))) = Finsupp.single g (∑ a in f.support, (f a)) := by
  conv => enter [1, 2, a] ; rw[Finsupp.smul_single', mul_one]
  rw [@Finsupp.single_finset_sum]

end Finsupp
