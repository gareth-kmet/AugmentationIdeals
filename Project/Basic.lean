/-
Authors : Gareth Kmet
-/
import Project.AugmentationMap
import Mathlib.GroupTheory.Torsion

/-!
# Augmentation Ideal

This file defines the Augmentation Ideal of the MonoidAlgebra of a communative group and communative ring.
It then defines the quotients of an Augmentation Ideal and its powers

This copies from the thesis "Calculation of Augmentation Termains" by John Kmet and encompases the prerequisites
and the first section of Chapter 1.

## Main definitions

* `AugmentationIdeal` is the kernal of a the homomorphism `AugmentationIdeal.AugmentationMap` which sends
  an element of the `MonoidAlgebra` to the sum of its ring coefficients. This is notated by `Δ R,G` where
  `R` is the communative ring and `G` is the communative group
* `AugmentationIdeal.Basis.basis` defines the basis of the Augmentation Ideal to be the set of
  `{MonoidAlgebra.of g - 1 | g ≠ 1}`
* `AugmentationIdeal.aug_pow_is_pow_of_mul_of_univ` states that, when `G` is cyclic,
  `(Δ R,G) ^ n = (MonoidAlgebra.of g - 1) ^ n * R[G]`
* `AugmentationIdeal.quotOfNPow` defines the quotient of `(Δ R,G) ^ n ⧸ (Δ R,G) ^ (n+r)` for some
  natural numbers `n` and `r`
* `AugmentationIdeal.quotNatOverSucc` defines the quotient of `(Δ R,G) ^ n ⧸ (Δ R,G) ^ (n + 1)`
* `AugmentationIdeal.Quotients.quot_torsion` defines a `AddMonoid.IsTorsion` on `(Δ R,G) ^ n ⧸ (Δ R,G) ^ (n + 1)`
  for any `n > 0`
* `AugmentationIdeal.npow_mem.linearcomb_prod_basis` states that any element of `(Δ R,G) ^ n` is a linear combination
  of `∏ i : Fin n, Monoid.of gᵢ - 1` with `R` coefficients for `n > 0`

## Implementation

Although the thesis use ℤ for all its proofs, this file uses a generic communative ring. To get around some cases, an
assumption is made that the ring has no zero divisors (isn't trivial), this should be removed in the future.

This file also does not cover the analagous proofs for `quotPolynomial` the quotient of `(Δ R,G) ⧸ (Δ R,G) ^ n`

## Future work

* generalize non communative groups
* remove the `NoZeroDivisors R` variable
* complete the other sections
* complete the analogous results for `(Δ R,G) ⧸ (Δ R,G) ^ n`

-/

open BigOperators Classical

variable (R G : Type*) [CommGroup G] [CommRing R] [NoZeroDivisors R]

noncomputable def AugmentationIdeal : Ideal (MonoidAlgebra R G) := RingHom.ker (AugmentationIdeal.AugmentationMap (R:=R) (G:=G))

-- A computable version of AugmentationIdeal
def AugmentationIdeal' : Ideal (MonoidAlgebra R G) := RingHom.ker (AugmentationIdeal'.AugmentationMap (R:=R) (G:=G))

lemma AugmentationIdeal'.eq : AugmentationIdeal' R G = AugmentationIdeal R G := by
  unfold AugmentationIdeal' AugmentationIdeal
  simp only [AugmentationMap.eq]


namespace AugmentationIdeal

scoped notation "Δ" R "," G => AugmentationIdeal R G

variable {R G} in
lemma mem (f : MonoidAlgebra R G) : f ∈ (Δ R,G) ↔ ∑ a in f.support, f a = 0 := by
  unfold AugmentationIdeal
  rw [@RingHom.mem_ker]
  rw [AugmentationMap.fun_def']


noncomputable section Quotients

variable (n r : ℕ)

variable {R G} in
lemma nrpow_subset_npow (x : ((Δ R,G) ^ (n + r) : Ideal (MonoidAlgebra R G))) :
    ↑x ∈ ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)) := by
  obtain ⟨_, hx⟩ := x
  induction r with
  | zero => simp only [Nat.zero_eq, add_zero] at hx  ; assumption
  | succ r ih =>
    rw [Nat.succ_eq_add_one, ← add_assoc, pow_succ'] at hx
    apply Ideal.mul_le_right at hx
    exact ih hx

def nrpow_addsubgroup_of_npow : AddSubgroup ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)) where
  carrier := {⟨↑x, nrpow_subset_npow n r x⟩ | x : ((Δ R,G) ^ (n + r) : Ideal (MonoidAlgebra R G))}
  add_mem' := by
    rintro ⟨_, _⟩ ⟨_, _⟩
    simp only [Subtype.exists, Set.mem_setOf_eq, Subtype.mk.injEq, exists_prop, exists_eq_right,
      AddSubmonoid.mk_add_mk]
    intro ha' hb'
    exact Ideal.add_mem ((Δ R,G) ^ (n + r)) ha' hb'
  zero_mem' := by simp only [Subtype.exists, Set.mem_setOf_eq, Submodule.mk_eq_zero, exists_prop,
    exists_eq_right, Submodule.zero_mem]
  neg_mem' := by
    rintro ⟨x, _⟩
    simp only [Subtype.exists, Set.mem_setOf_eq, Subtype.mk.injEq, exists_prop, exists_eq_right]
    intro hx'
    use -x
    suffices -x ∈ ((Δ R,G) ^ (n + r) : Ideal (MonoidAlgebra R G)) by {
      use this ; rfl
    }
    exact (Ideal.neg_mem_iff ((Δ R,G) ^ (n + r))).mpr hx'

lemma coe_nrpow_addsubgroup : ↑(nrpow_addsubgroup_of_npow R G n r).carrier = (((Δ R,G) ^ (n + r) : Ideal (MonoidAlgebra R G)) : Set (MonoidAlgebra R G)) := by
  unfold nrpow_addsubgroup_of_npow
  ext x
  simp only [SetLike.coe_sort_coe, Subtype.exists, Set.mem_image, Set.mem_setOf_eq,
    Subtype.mk.injEq, exists_prop, exists_eq_right, exists_and_left, exists_eq_right_right,
    SetLike.mem_coe, and_iff_left_iff_imp]
  simp only [and_iff_right_iff_imp]
  intro hx
  rw [show x = ↑(⟨x, hx⟩ : ((Δ R,G) ^ (n + r) : Ideal (MonoidAlgebra R G))) from rfl]
  exact nrpow_subset_npow n r ⟨x,hx⟩

def quotOfNPow :=
  ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)) ⧸ (nrpow_addsubgroup_of_npow R G n r)

instance quotOfNPow.addCommGroup : AddCommGroup (quotOfNPow R G n r) :=
  QuotientAddGroup.Quotient.addCommGroup (nrpow_addsubgroup_of_npow R G n r)

--Notated as `Qₙ` in the thesis
def quotNatOverSucc := quotOfNPow R G n 1

instance quotNatOverSucc.addCommGroup : AddCommGroup (quotNatOverSucc R G n) :=
  quotOfNPow.addCommGroup R G n 1

--Notated as `Pₙ` in the thesis
def quotIdOverNat := quotOfNPow R G 1 n

instance quotIdOverNat.addCommGroup : AddCommGroup (quotIdOverNat R G n) :=
  quotOfNPow.addCommGroup R G 1 n

end Quotients

end AugmentationIdeal

namespace AugmentationIdeal.Basis

lemma basis_elements_are_in_set (g : G) : (MonoidAlgebra.single g (1 : R)) - (1 : MonoidAlgebra R G) ∈ Δ R,G := by
  unfold AugmentationIdeal
  rw [RingHom.mem_ker, map_sub]
  by_cases (1:R) = 0
  · simp only [h, Finsupp.single_zero, map_zero, map_one, sub_self]
  · rw [map_one, AugmentationMap.fun_def'', Finsupp.support_single_ne_zero]
    simp only [Finset.univ_unique, ne_eq, Finset.sum_singleton, Finset.default_singleton,
      Finsupp.single_eq_same, sub_self]
    assumption'

noncomputable def basis_def' : {g : G | g ≠ 1} → MonoidAlgebra R G := fun g =>
  (MonoidAlgebra.single (g : G) (1 : R)) - (1 : MonoidAlgebra R G)

noncomputable def basis_def : {g : G | g ≠ 1} → Δ R,G := fun g => {
  val := basis_def' R G g
  property := basis_elements_are_in_set R G g
}

lemma basis_elements_are_in_set' (g : {g : G | g ≠ 1}) : basis_def' R G g ∈ Δ R,G := by
  simp only [basis_def', ne_eq, Set.mem_setOf_eq, basis_elements_are_in_set]

variable {R G}

theorem funct_is_linearcomb_of_basis_with_offset (f : G →₀ R) : f =
    (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) + MonoidAlgebra.single 1 (AugmentationMap f) := by
  calc f
    _ = ∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G) + (1 : MonoidAlgebra R G)) := by
      conv => enter [2, 2, a, 2] ; rw [sub_add_cancel]
      exact Finsupp.finsupp_is_linear_combo_of_singles f
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        (∑ a in f.support, (f a) • (1 : MonoidAlgebra R G)) := by
      conv => enter [1, 2, a] ; rw [smul_add]
      rw [← @Finset.sum_add_distrib]
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        MonoidAlgebra.single 1 (∑ a in f.support, (f a)) := by
      rw [MonoidAlgebra.one_def, Finsupp.sum_single_is_single_sum f 1]
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        MonoidAlgebra.single 1 (AugmentationMap f) := by rw [AugmentationMap.fun_def']

lemma mem_is_linearcomb_of_basis_singles' (f : MonoidAlgebra R G) (h : f ∈ Δ R,G) :
    (f : G →₀ R) = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) := by
  unfold AugmentationIdeal at h
  rw [RingHom.mem_ker] at h
  conv => lhs ; rw [funct_is_linearcomb_of_basis_with_offset (f : G →₀ R)]
  rw[h, MonoidAlgebra.single_zero, add_zero]

lemma mem_is_linearcomb_of_basis_singles (f : MonoidAlgebra R G) (h : f ∈ Δ R,G) :
    (f : G →₀ R) = (∑ a in f.support \ {1}, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) := by
  suffices (∑ a in f.support \ {1}, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) by {
    rw[this] ; exact mem_is_linearcomb_of_basis_singles' f h
  }
  suffices (∑ a in {1}, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) = 0 by {
    by_cases f 1 = 0
    · rw [show f.support \ {1} = f.support by {
      simp only [Finsupp.mem_support_iff, h, ne_eq, not_true_eq_false, not_false_eq_true,
        Finset.sdiff_singleton_eq_self]
    }]
    · conv => rhs ; rw [show f.support = (f.support \ {1}) ∪ {1} by {
        simpa only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.sdiff_union_self_eq_union,
          Finset.left_eq_union, Finset.singleton_subset_iff, Finset.sum_singleton]
        }]
      rw[Finset.sum_union_is_left_and_sdiff]
      rw [show {1} \ (f.support \ {1}) = {1} by {
        simp only [Finsupp.mem_support_iff, ne_eq, not_not, sdiff_eq_left,
          Finset.disjoint_singleton_left, Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false,
          and_false, not_false_eq_true]
      }, this, add_zero]
  }
  rw [Finset.sum_singleton, MonoidAlgebra.one_def, sub_self, smul_zero]

def support_to_basis_index (f : G →₀ R) (a : ↑(f.support \ {1})) : {g : G | g ≠ 1} where
  val := ↑a
  property := by
    obtain ⟨_, ha'⟩ := a
    simp only [ne_eq, Set.mem_setOf_eq]
    exact Finset.not_mem_singleton.mp (Finset.mem_sdiff.mp ha').2

theorem mem_is_linearcomb_of_basis' (f : MonoidAlgebra R G) (h : f ∈ Δ R,G) :
    (f : G →₀ R) = (∑ a : ↑(f.support \ {1}), (f a) • (basis_def' R G (support_to_basis_index f a))) := by
  conv => lhs ; rw [mem_is_linearcomb_of_basis_singles f h]
  simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.singleton_subset_iff,
    Finset.univ_eq_attach, basis_def', Set.mem_setOf_eq, support_to_basis_index]
  rw [← Finset.sum_attach]

theorem mem_is_linearcomb_of_basis (f : MonoidAlgebra R G) (h : f ∈ Δ R,G) :
    (f : G →₀ R) = (∑ a : ↑(f.support \ {1}), (f a) • (basis_def R G (support_to_basis_index f a))) := by
  unfold basis_def ; simp only [Finset.univ_eq_attach, AddSubmonoid.coe_finset_sum,
    Submodule.coe_toAddSubmonoid, Submodule.coe_smul_of_tower]
  conv => lhs ; rw [mem_is_linearcomb_of_basis' f h]

@[deprecated]
lemma subset (f : MonoidAlgebra R G) : (f ∈ Δ R,G) → f ∈ Submodule.span R (Set.range (basis_def' R G)) := by
  intro hf
  rw [mem_span_set']
  use (f.support\{1}).card
  let h' := (f.support\{1}).equivFin.invFun
  use fun n => f (h' n)
  use fun n => {
    val := basis_def' R G (support_to_basis_index f (h' n))
    property := by simp only [Equiv.invFun_as_coe, ne_eq, Set.coe_setOf, Set.mem_range,
      exists_apply_eq_apply]
  }
  dsimp only [ne_eq, Set.coe_setOf, Equiv.invFun_as_coe]
  let x := fun i => f ((Finset.equivFin (f.support \ {1})).symm i) •
      basis_def' R G (support_to_basis_index f ((Finset.equivFin (f.support \ {1})).symm i))
  let g := fun (a : ↑(f.support \ {1})) => f a • basis_def' R G (support_to_basis_index f a)
  rw[Equiv.sum_comp' (Finset.equivFin (f.support \ {1})).symm x g]
  · dsimp only [g]
    rw [←mem_is_linearcomb_of_basis' f hf]
  · intros ; rfl

lemma coe_iff (a : Δ R,G) (b : MonoidAlgebra R G) (h : b ∈ Δ R,G) : a = ⟨b, h⟩ ↔ ↑a = b := by
  constructor
  · obtain ⟨a', ha'⟩ := a
    simp only [Subtype.mk.injEq, imp_self]
  · exact fun a_1 => SetCoe.ext a_1

theorem spans_top_set : ⊤ ≤ Submodule.span R (Set.range (basis_def R G)) := by
  rw [@SetLike.le_def]
  rintro ⟨x, hx⟩ _
  rw [mem_span_set']
  use (x.support\{1}).card
  let h' := (x.support\{1}).equivFin.invFun
  use fun n => x (h' n)
  use fun n => {
    val := basis_def R G (support_to_basis_index x (h' n))
    property := by
      simp only [Equiv.invFun_as_coe, ne_eq, Set.coe_setOf, Set.mem_range, exists_apply_eq_apply]
  }
  dsimp only [ne_eq, Set.coe_setOf, Equiv.invFun_as_coe]
  let f := fun i => x ↑((Finset.equivFin (x.support \ {1})).symm i) •
      basis_def R G (support_to_basis_index x ((Finset.equivFin (x.support \ {1})).symm i))
  let g := fun (a : ↑(x.support \ {1})) => x ↑a • basis_def R G (support_to_basis_index x a)
  rw[Equiv.sum_comp' (Finset.equivFin (x.support \ {1})).symm f g]
  · dsimp only [g]
    rw [coe_iff, ←mem_is_linearcomb_of_basis x hx]
  · intros ; rfl

theorem linear_independent : LinearIndependent R (basis_def R G) := by
  rw [@linearIndependent_iff']
  intro s f h
  rw [@Subtype.ext_iff, @Submodule.coe_sum] at h
  unfold basis_def at h
  dsimp only [ne_eq, Set.coe_setOf, Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero] at h
  have h' := Finsupp.support_eq_empty.mpr h
  rw [@Finset.eq_empty_iff_forall_not_mem] at h'
  rintro ⟨i, hi⟩ hi'
  specialize h' i
  rw [@Finsupp.not_mem_support_iff] at h'
  rw[Finset.sum_apply'] at h'
  unfold basis_def' at h'
  simp only [smul_sub] at h'
  have h'' (x : { x // ¬x = 1 }) : (↑(f x • MonoidAlgebra.single (G:=G) (↑x) (1:R) - f x • 1) : G →₀ R) i =
      ↑(f x • MonoidAlgebra.single (G:=G) (↑x) (1:R) i - f x • MonoidAlgebra.single (G:=G) 1 (1:R) i) := by
    rfl
  simp only [h'',Finset.sum_sub_distrib] at h'
  have h''' (x : { x // ¬x = 1 }) : f x • (MonoidAlgebra.single (1:G) (1:R)) i = 0 := by
    simp only [ne_eq, smul_eq_mul, mul_eq_zero]
    exact Or.inr <| by
      rw [@Finsupp.single_apply_eq_zero]
      intro hi''' ; exfalso
      rw [@Set.mem_setOf] at hi ; exact hi hi'''
  simp only [h'''] at h'
  simp only [ne_eq, smul_eq_mul, Finset.sum_const_zero, sub_zero] at h'
  have hs : s = s \ {⟨i,hi⟩} ∪ {⟨i,hi⟩} := by
    simpa only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Finset.sdiff_union_self_eq_union,
      Finset.left_eq_union, Finset.singleton_subset_iff]
  rw [hs] at h'
  rw [Finset.sum_union_is_left_and_sdiff] at h'
  replace hs : {{ val := i, property := hi }} \ (s \ {{ val := i, property := hi }}) = {{ val := i, property := hi }} := by
    simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, sdiff_eq_left,
      Finset.disjoint_singleton_left, Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false,
      and_false, not_false_eq_true]
  rw [hs] at h'
  simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Finset.singleton_subset_iff,
    Finset.sum_singleton, Finsupp.single_eq_same, mul_one] at h'
  rw [← h']
  simp only [ne_eq, Set.mem_setOf_eq, Set.coe_setOf, Finset.singleton_subset_iff, self_eq_add_left]
  apply Finset.sum_eq_zero
  intro j hj
  rw [@Finset.mem_sdiff] at hj
  obtain ⟨_, hj₂⟩ := hj
  rw [@Finset.not_mem_singleton] at hj₂
  unfold MonoidAlgebra.single
  rw [@mul_eq_zero]
  exact Or.inr <| by
    rw [@Finsupp.single_apply_eq_zero]
    intro hj'
    exfalso
    apply hj₂
    rw [@Subtype.ext_iff]
    exact id hj'.symm

end Basis

noncomputable instance basis : Basis {g : G | g ≠ 1} R (Δ R,G) := Basis.mk Basis.linear_independent Basis.spans_top_set

@[simp]
lemma mul_distrib (f₁ f₂ g₁ g₂ : G) (r₁ r₂ r₃ r₄ : R) : (MonoidAlgebra.single f₁ r₁ + MonoidAlgebra.single f₂ r₂) * (MonoidAlgebra.single g₁ r₃ + MonoidAlgebra.single g₂ r₄) =
    (MonoidAlgebra.single (f₁*g₁) (r₁*r₃)) + (MonoidAlgebra.single (f₁*g₂) (r₁*r₄)) + (MonoidAlgebra.single (f₂*g₁) (r₂*r₃)) + (MonoidAlgebra.single (f₂*g₂) (r₂*r₄)) := by
  group ; simp only [MonoidAlgebra.single_mul_single, mul_comm]

@[simp]
lemma sub_distrib (g : G) (f : MonoidAlgebra R G) (r : R) : f - MonoidAlgebra.single g r = f + MonoidAlgebra.single g (-r) := by
  simp only [Finsupp.single_neg, sub_eq_iff_eq_add', add_neg_cancel_comm_assoc]

@[simp]
lemma mul_distrib_of_basis (f g : G) : (MonoidAlgebra.single f (1:R) - 1) * (MonoidAlgebra.single g (1:R) - 1) =
    (MonoidAlgebra.single (f*g) (1:R)) - (MonoidAlgebra.single f (1:R)) - (MonoidAlgebra.single g (1:R)) + 1 := by
  dsimp only [MonoidAlgebra.one_def]
  simp only [sub_distrib, mul_distrib]
  group

namespace Cyclic

variable [hG : IsCyclic G] {R G}

noncomputable def gen : G := hG.exists_generator.choose

lemma gen_def : ∀ x : G, x ∈ Subgroup.zpowers gen := by
  exact hG.exists_generator.choose_spec

lemma gen_is_top : (Subgroup.zpowers (G:=G) gen) = ⊤ := by
  rw [←top_le_iff]
  rw [@SetLike.le_def]
  exact fun ⦃x⦄ _ => gen_def x

def gen_pow_exists (g : G) : ∃ z : ℤ, g = gen ^ z := by
  apply Subgroup.exists_mem_zpowers.mp
  simp only [exists_eq_right']
  exact gen_def g

noncomputable def gen_pow : G → ℤ :=
  fun g => Classical.choose <| gen_pow_exists g

lemma gen_pow_def (g : G) : gen ^ (gen_pow g) = g := by
  dsimp only [gen_pow]
  rw[←Classical.choose_spec <| gen_pow_exists g]

lemma expand_basis_of_power_nat (g : G) (n : ℕ) : (MonoidAlgebra.single (g ^ n) (1:R) - 1) =
    (∑ i : Fin n, MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) * (MonoidAlgebra.single g (1:R) - 1):= by
  induction n with
  | zero => simp only [Nat.zero_eq, pow_zero, MonoidAlgebra.one_def, sub_self, Finset.univ_eq_empty,
    Finset.sum_empty, sub_distrib, Finsupp.single_neg, zero_mul]
  | succ n ih =>
    rw [MonoidAlgebra.one_def]
    apply symm
    calc (∑ i : Fin (Nat.succ n), MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) * (MonoidAlgebra.single g (1:R) - 1)
      _ = (MonoidAlgebra.single (g ^ n) (1:R) + ∑ i : Fin n, MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) *  (MonoidAlgebra.single g (1:R) - 1) := by
        rw [show Nat.succ n = n + 1 from rfl, Fin.sum_univ_add]
        simp only [Fin.coe_castAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.coe_natAdd,
          Fin.coe_fin_one, add_zero, Finset.sum_const, Finset.card_singleton, one_smul]
        ring
      _ = (MonoidAlgebra.single (g ^ n) (1:R) * (MonoidAlgebra.single g (1:R) - 1)) +
          (∑ i : Fin n, MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) *  (MonoidAlgebra.single g (1:R) - 1) := by ring
      _ = (MonoidAlgebra.single (g ^ n) (1:R) * (MonoidAlgebra.single g (1:R) - 1)) + (MonoidAlgebra.single (g ^ n) (1:R) - 1) := by rw[ih]
      _ = ((MonoidAlgebra.single (g ^ n) (1:R) + MonoidAlgebra.single 1 0) * (MonoidAlgebra.single g (1:R) - MonoidAlgebra.single 1 1)) + (MonoidAlgebra.single (g ^ n) (1:R) - 1) := by
        simp only [Finsupp.single_zero, add_zero, MonoidAlgebra.one_def]
      _ = ((MonoidAlgebra.single (g ^ n) (1:R) + MonoidAlgebra.single 1 0) * (MonoidAlgebra.single g (1:R) + MonoidAlgebra.single 1 (-1))) + (MonoidAlgebra.single (g ^ n) (1:R) - 1) := by
        simp only [sub_distrib, Finsupp.single_neg]
      _ = (MonoidAlgebra.single (g ^ n * g) (1:R) + (MonoidAlgebra.single (g ^ n) (-1:R))) + (MonoidAlgebra.single (g ^ n) (1:R) + MonoidAlgebra.single 1 (-1)) := by
        congr ; rw [mul_distrib] ; group
        simp only [zpow_coe_nat, Finsupp.single_neg,Finsupp.single_zero, add_zero]
        rw [← sub_distrib, MonoidAlgebra.one_def]
      _ = MonoidAlgebra.single (g ^ n * g) (1:R) - 1 := by
        simp only [Finsupp.single_neg, MonoidAlgebra.one_def, sub_distrib] ; group
    congr ; exact (pow_succ' g n).symm

lemma expand_basis_of_power_neg_nat (g : G) (n : ℕ) : (MonoidAlgebra.single (g ^ n)⁻¹ (1:R) - 1) =
    -MonoidAlgebra.single (g ^ n)⁻¹ (1:R) * (MonoidAlgebra.single (g ^ n) (1:R) - 1) := by
  group
  rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def]
  group

lemma basis_of_power_is_mul_of_basis (g : G) (z : ℤ) :
    (MonoidAlgebra.single (g ^ z) (1:R) - 1) ∈ {f * (MonoidAlgebra.single g (1:R) - 1) | f : MonoidAlgebra R G} := by
  induction z with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_coe_nat, Set.mem_setOf_eq,expand_basis_of_power_nat]
    use (∑ i : Fin n, MonoidAlgebra.single (g ^ (i : ℕ)) 1)
  | negSucc n =>
    simp only [zpow_negSucc, Set.mem_setOf_eq,
      expand_basis_of_power_neg_nat, expand_basis_of_power_nat]
    use -MonoidAlgebra.single (g ^ (-((n + 1):ℤ))) 1 * ((∑ i : Fin (n + 1), MonoidAlgebra.single (g ^ (i:ℕ)) 1))
    group

lemma basis_of_power_is_mul_of_basis' (g : G) (z : ℤ) :
    ∃ f : MonoidAlgebra R G, f * (MonoidAlgebra.single g (1:R) - 1) = (MonoidAlgebra.single (g ^ z) (1:R) - 1) := by
  exact basis_of_power_is_mul_of_basis g z

variable (R G) in
theorem univ_mul_basis_of_gen_eq_aug : {f * (MonoidAlgebra.single gen (1:R) - 1) | f : MonoidAlgebra R G} = Δ R,G := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    unfold AugmentationIdeal
    rw [SetLike.mem_coe, @RingHom.mem_ker, ←hy, @RingHom.map_mul]
    suffices (AugmentationMap (R:=R) (G:=G)) (MonoidAlgebra.single gen 1 - 1) = 0 by {
      rw[this] ; ring
    }
    suffices (MonoidAlgebra.single gen 1 - 1) ∈ Δ R,G by {
      unfold AugmentationIdeal at this
      rw[RingHom.mem_ker] at this
      exact this
    }
    exact Basis.basis_elements_are_in_set R G gen
  · intro hx
    rw [Basis.mem_is_linearcomb_of_basis_singles x hx]
    conv =>
      enter [1, 2, a]
      rw [← gen_pow_def a]
      rw [← Classical.choose_spec <| basis_of_power_is_mul_of_basis' gen <| gen_pow a]
      rw [← Algebra.smul_mul_assoc]
    rw [Finset.sum_mul.symm]
    simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.singleton_subset_iff,
      Set.mem_setOf_eq, exists_apply_eq_apply]

variable (R) in
lemma univ_mul_basis_of_gen_eq_aug' : g ∈ (Δ R,G) ↔ g ∈ {f * (MonoidAlgebra.single (G:=G) gen (1:R) - 1) | f : MonoidAlgebra R G} := by
  rw [univ_mul_basis_of_gen_eq_aug] ; rfl

variable (R G) in
theorem aug_is_span_singleton : (Δ R,G) = Ideal.span {MonoidAlgebra.single gen (1:R) - 1} := by
  ext f
  rw [@Ideal.mem_span_singleton']
  constructor
  · intro hf
    rwa [univ_mul_basis_of_gen_eq_aug'] at hf
  · intro hf
    rwa [univ_mul_basis_of_gen_eq_aug']

variable (R G) in
theorem aug_pow_is_span_singleton (n : ℕ) : (Δ R,G) ^ n = Ideal.span {(MonoidAlgebra.single gen (1:R) - 1) ^ n} := by
  rw [aug_is_span_singleton, Ideal.span_singleton_pow]

variable (R G) in
theorem aug_pow_is_pow_of_mul_of_univ (n : ℕ) : {f * (MonoidAlgebra.single (G:=G) gen (1:R) - 1) ^ n | f : MonoidAlgebra R G} = ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)) := by
  ext f
  constructor
  · rintro ⟨y, hy⟩
    rw [@SetLike.mem_coe, ←hy]
    apply Ideal.mul_mem_left
    apply Ideal.pow_mem_pow
    exact Basis.basis_elements_are_in_set R G gen
  · rintro hf
    rw [aug_pow_is_span_singleton, @SetLike.mem_coe] at hf
    rw [@Ideal.mem_span_singleton'] at hf
    rwa [@Set.mem_setOf]



end Cyclic

namespace Quotients

variable [Fintype G] {G}

lemma pow_card_sub_one_eq_zero (x : G) : MonoidAlgebra.single (x ^ Fintype.card G) (1:R) - 1 = 0 := by
  simp only [pow_card_eq_one, MonoidAlgebra.one_def, sub_self]

lemma pow_card_eq_binomial_exp (x : G) :
    (MonoidAlgebra.single x (1:R)) ^ Fintype.card G =
    ∑ i in Finset.range (Fintype.card G + 1), (Nat.choose (Fintype.card G) i) • ((MonoidAlgebra.single x (1:R) - 1) ^ (i:ℕ)) := by
  conv =>
    enter [1, 1]
    rw [←add_zero (MonoidAlgebra.single x 1), ←sub_self 1, sub_eq_add_neg, add_comm 1, ←add_assoc, ←sub_eq_add_neg]
  rw[add_pow]
  congr ; ext ; group

lemma pow_card_sub_one_eq_binomial_exp (x : G) :
    (MonoidAlgebra.single x (1:R)) ^ Fintype.card G - 1 =
    ∑ i in Finset.range (Fintype.card G), (Nat.choose (Fintype.card G) (i+1)) • ((MonoidAlgebra.single x (1:R) - 1) ^ (i+1)) := by
  rw [pow_card_eq_binomial_exp]
  rw [Finset.sum_range_succ']
  suffices Nat.choose (Fintype.card G) 0 • (MonoidAlgebra.single x (1:R) - 1) ^ 0 = 1 by {
    rw [this] ; simp only [nsmul_eq_mul, add_sub_cancel]
  }
  rw [@nsmul_eq_mul, pow_zero, Nat.choose_zero_right]
  group


lemma card_smul_basis_eq_neg_binomial_exp (x : G) :
    (Fintype.card G) • (MonoidAlgebra.single x (1:R) - 1) =
    - ∑ i in Finset.range (Fintype.card G - 1), Nat.choose (Fintype.card G) (i+1+1) • ((MonoidAlgebra.single x (1:R) - 1) ^ (i+1+1)) := by
  conv =>
    enter [2, 1]
    rw [← add_zero (∑ i in Finset.range (Fintype.card G - 1),
        (Nat.choose (Fintype.card G) (i + 1 + 1)) • (MonoidAlgebra.single x 1 - 1) ^ (i + 1 + 1))]
    rw [← sub_self (Nat.choose (Fintype.card G) (0 + 1) • (MonoidAlgebra.single x 1 - 1) ^ (0 + 1))]
    rw [sub_eq_add_neg (Nat.choose (Fintype.card G) (0 + 1) • (MonoidAlgebra.single x 1 - 1) ^ (0 + 1))]
    rw [← add_assoc]
  conv =>
    enter [2, 1, 1]
    rw[←Finset.sum_range_succ' (fun k => Nat.choose (Fintype.card G) (k + 1) • (MonoidAlgebra.single x 1 - 1) ^ (k + 1))]
  rw [Nat.sub_add_cancel] ; simp only [zero_add, Nat.choose_one_right, pow_one,
    neg_add_rev, neg_neg, self_eq_add_right, neg_eq_zero]
  rw[← pow_card_sub_one_eq_binomial_exp]
  simp only [MonoidAlgebra.single_pow, pow_card_eq_one, one_pow, MonoidAlgebra.one_def, sub_self]
  by_cases Fintype.card G ≠ 0
  · exact Nat.one_le_iff_ne_zero.mpr h
  · exfalso
    rw [@not_ne_iff] at h
    replace h := Fintype.card_eq_zero_iff.mp h
    rw [@isEmpty_iff] at h ; apply h
    exact 1

lemma card_smul_basis_mem_aug_squared (x : G) :
    (Fintype.card G) • (MonoidAlgebra.single x (1:R) - 1) ∈ (Δ R,G) ^ 2 := by
  rw [card_smul_basis_eq_neg_binomial_exp]
  conv =>
    enter [1, 1, 2, i, 2]
    rw [show i + 1 + 1 = i + 2 by ring,pow_add]
  conv =>
    enter [1, 1, 2, i]
    rw [nsmul_eq_mul, ← mul_assoc]
  rw [← Finset.sum_mul]
  rw [@Ideal.neg_mem_iff]
  apply Ideal.mul_mem_left
  apply Ideal.pow_mem_pow
  exact Basis.basis_elements_are_in_set R G x

lemma card_mul_basis_mem_aug_squared (x : G) :
    (Fintype.card G : MonoidAlgebra R G) * (MonoidAlgebra.single x (1:R) - 1) ∈ (Δ R,G) ^ 2 := by
  have h := card_smul_basis_mem_aug_squared R x
  simp only [nsmul_eq_mul] at h
  assumption


section Pointwise
open Pointwise

variable (G)
lemma card_pwsmul_aug_subset_aug_squared :
    {Fintype.card G • f | f ∈ Δ R,G} ⊆ ((Δ R,G) ^ 2 : Ideal (MonoidAlgebra R G)) := by
  rw [@Set.subset_def]
  rintro x ⟨d, ⟨hd, hx⟩⟩
  rw [Basis.mem_is_linearcomb_of_basis_singles' _ hd] at hx
  rw [@Finset.smul_sum] at hx
  conv at hx =>
    enter [1, 2, x]
    rw[smul_comm]
  suffices ∀ x, Fintype.card G • (MonoidAlgebra.single x 1 - 1) ∈ (Δ R,G)^2 by {
    rw [@SetLike.mem_coe]
    rw [←hx]
    let f : G → ((Δ R,G)^2 : Ideal (MonoidAlgebra R G)) := fun y => {
      val := d y • Fintype.card G • (MonoidAlgebra.single y 1 - 1)
      property := Submodule.smul_of_tower_mem ((Δ R,G) ^ 2) (d y) (this y)
    }
    have hf (y : G) : f y = d y • Fintype.card G • (MonoidAlgebra.single y (1:R) - 1) := rfl
    conv =>
      enter [1, 2, y]
      rw [← hf]
    rw [← @Submodule.coe_sum]
    exact Submodule.coe_mem (∑ i in d.support, f i)
  }
  exact fun y => card_smul_basis_mem_aug_squared R y

lemma card_pwsmul_aug_subset_aug_squared' (f : MonoidAlgebra R G) (hf : f ∈ Δ R,G):
    (Fintype.card G : MonoidAlgebra R G) * f ∈ ((Δ R,G) ^ 2 : Ideal (MonoidAlgebra R G)) := by
  rw [Basis.mem_is_linearcomb_of_basis_singles' _ hf]
  rw [Finset.mul_sum]
  conv =>
    enter [1, 2, x]
    rw[mul_comm]
  suffices ∀ x, (Fintype.card G : MonoidAlgebra R G) * (MonoidAlgebra.single x 1 - 1) ∈ (Δ R,G)^2 by {
    let d : G → ((Δ R,G)^2 : Ideal (MonoidAlgebra R G)) := fun y => {
      val := f y • (Fintype.card G : MonoidAlgebra R G) * (MonoidAlgebra.single y 1 - 1)
      property := by
        rw [smul_mul_assoc]
        exact Submodule.smul_of_tower_mem ((Δ R,G) ^ 2) (f y) (this y)
    }
    have hd (y : G) : d y = f y • (Fintype.card G : MonoidAlgebra R G) * (MonoidAlgebra.single y (1:R) - 1) := rfl
    conv =>
      enter [1, 2, y]
      rw [smul_mul_assoc, mul_comm, ← smul_mul_assoc, ← hd]
    rw [← @Submodule.coe_sum]
    exact Submodule.coe_mem (∑ i in f.support, d i)
  }
  exact fun y => card_mul_basis_mem_aug_squared R y

lemma card_pwsmul_aug_npow_subset_def (n : ℕ) :
    {Fintype.card G • f | f ∈ (Δ R,G) ^ (n+1)} ⊆
    {x | ∃ m : ℕ, ∃ f : Fin m → (Δ R,G), ∃ g : Fin m → ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)), ∃ c : Fin m → MonoidAlgebra R G, ∑ i : Fin m, Fintype.card G • (c i * ↑(f i) * ↑(g i)) = x} := by
  rw [pow_succ]
  rw [@Submodule.mul_eq_span_mul_set]
  rintro x ⟨f, ⟨hf₁, hf₂⟩⟩
  rw [mem_span_set] at hf₁
  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := hf₁
  rw [@Set.subset_def] at hc₁
  have hc₁' : ∀ x ∈ c.support, x ∈ {f * g | (f ∈ Δ R,G) (g ∈ (Δ R,G)^n)} := by
    intro x hx
    apply hc₁ at hx
    simp only [Set.mem_setOf_eq]
    rw [@Set.mem_mul] at hx
    obtain ⟨f, ⟨g, ⟨hf, ⟨hg, hfg⟩⟩⟩⟩ := hx
    exact ⟨f, ⟨hf, ⟨g, ⟨hg, hfg⟩⟩⟩⟩
  rw [← hf₂, ← hc₂, Finsupp.smul_sum]
  unfold Finsupp.sum
  dsimp only [smul_eq_mul, Set.mem_setOf_eq]
  use c.support.card
  let f : Fin c.support.card → (Δ R,G) := by
    intro i
    obtain ⟨y, hy⟩ := c.support.equivFin.invFun i
    apply hc₁' at hy
    exact ⟨hy.choose, hy.choose_spec.1⟩
  let g : Fin c.support.card → ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)) := by
    intro i
    obtain ⟨y, hy⟩ := c.support.equivFin.invFun i
    apply hc₁' at hy
    exact ⟨hy.choose_spec.2.choose, hy.choose_spec.2.choose_spec.1⟩
  let c' := fun i => c ((f i : MonoidAlgebra R G) * ↑(g i))
  use f ; use g ; use c'
  conv => rhs ; rw [Finset.sum_equiv_sum_indexed_by_card']
  suffices ∀ i : Fin (c.support.card), ↑(Equiv.invFun (Finset.equivFin c.support) i) = ((f i) : MonoidAlgebra R G) * (g i : MonoidAlgebra R G) by {
    conv => enter [2, 2, i] ; rw [this, ← mul_assoc]
  }
  intro i
  have hy := (c.support.equivFin.invFun i).property
  apply hc₁' at hy
  rw [← hy.choose_spec.2.choose_spec.2]

lemma card_pwsmul_aug_mul_npow_aug_subset (n : ℕ) :
    {x | ∃ m : ℕ, ∃ f : Fin m → (Δ R,G),
                  ∃ g : Fin m → ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)),
                  ∃ c : Fin m → MonoidAlgebra R G,
        ∑ i : Fin m, Fintype.card G • (c i * ↑(f i) * ↑(g i)) = x} ⊆
    {x | ∃ m : ℕ, ∃ f : Fin m → ((Δ R,G) ^ 2 : Ideal (MonoidAlgebra R G)),
                  ∃ g : Fin m → ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)),
                  ∃ c : Fin m → MonoidAlgebra R G,
        ∑ i : Fin m, (c i * ↑(f i) * ↑(g i)) = x} := by
  rintro x ⟨m, ⟨f, ⟨g, ⟨c, h⟩⟩⟩⟩
  simp only [Set.mem_setOf_eq]
  let f' : Fin m → ((Δ R,G) ^ 2 : Ideal (MonoidAlgebra R G)) := fun i => {
    val := Fintype.card G • f i
    property := by
      apply card_pwsmul_aug_subset_aug_squared
      rw [@Set.mem_setOf]
      use f i
      exact ⟨Submodule.coe_mem (f i),rfl⟩
  }
  use m ; use f' ; use g ; use c
  dsimp only [Set.mem_setOf_eq, id_eq, eq_mpr_eq_cast, cast_eq] ; rw [← h]
  congr ; ext _ ; group

lemma aug_sq_mul_aug_npow_def_subset (n : ℕ) :
    {x | ∃ m : ℕ, ∃ f : Fin m → ((Δ R,G) ^ 2 : Ideal (MonoidAlgebra R G)),
                  ∃ g : Fin m → ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)),
                  ∃ c : Fin m → MonoidAlgebra R G,
        ∑ i : Fin m, (c i * ↑(f i) * ↑(g i)) = x} ⊆ ((Δ R,G) ^ (n + 2) : Ideal (MonoidAlgebra R G)) := by
  rintro x ⟨m, ⟨f, ⟨g, ⟨c, hc⟩⟩⟩⟩
  rw [show (Δ R,G) ^ (n+2) = (Δ R,G) ^ 2 * (Δ R,G) ^ n by group]
  rw [← hc] ; simp only [SetLike.mem_coe]
  apply Ideal.sum_mem
  intro i _ ; rw [mul_assoc]
  apply Ideal.mul_mem_left
  apply Ideal.mul_mem_mul <;> simp only [SetLike.coe_mem]

theorem card_pwsmul_npow_aug_subset_succ_pow_aug' (n : ℕ):
    {Fintype.card G • f | f ∈ (Δ R,G) ^ (n+1) } ⊆ ((Δ R,G) ^ (n + 2) : Ideal (MonoidAlgebra R G)) :=
  card_pwsmul_aug_npow_subset_def R G n |>.trans
    <| card_pwsmul_aug_mul_npow_aug_subset R G n |>.trans
    <| aug_sq_mul_aug_npow_def_subset R G n

lemma pw_smul_def (x : MonoidAlgebra R G) (α : Set (MonoidAlgebra R G)) : x • α = {x * a | a ∈ α} := by
  ext y
  rw [Set.mem_smul_set]
  simp only [smul_eq_mul, Set.mem_setOf_eq]

lemma card_pwsmul_npow_aug_subset_succ_pow_aug'_apply (n : ℕ) (x : MonoidAlgebra R G) (hx : x ∈ (Δ R,G) ^ (n+1)) :
    Fintype.card G • x ∈ ((Δ R,G) ^ (n + 2) : Ideal (MonoidAlgebra R G)) := by
  have h := card_pwsmul_npow_aug_subset_succ_pow_aug' R G n
  rw [@Set.subset_def] at h
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h
  exact h x hx


lemma card_pwsmul_npow_aug_def (n : ℕ) :
    (Fintype.card G : MonoidAlgebra R G) • (((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) : Set (MonoidAlgebra R G)) =
    {Fintype.card G • f | f ∈ (Δ R,G) ^ (n+1) } := by
  rw [pw_smul_def]
  simp only [SetLike.mem_coe, nsmul_eq_mul]

theorem card_pwsmul_npow_aug_subset_succ_pow_aug (n : ℕ):
    (Fintype.card G : MonoidAlgebra R G) • (((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) : Set (MonoidAlgebra R G)) ⊆
    ((Δ R,G) ^ (n + 2) : Ideal (MonoidAlgebra R G)) := by
  rw [card_pwsmul_npow_aug_def]
  exact card_pwsmul_npow_aug_subset_succ_pow_aug' R G n

variable {R G}
lemma card_pwsmul_npow_aug_subset_succ_pow_aug_apply (n : ℕ) (y : MonoidAlgebra R G) :
    y ∈ (Fintype.card G : MonoidAlgebra R G) • (((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) : Set (MonoidAlgebra R G)) →
    y ∈ ((Δ R,G) ^ (n + 2) : Ideal (MonoidAlgebra R G)) := fun a => (card_pwsmul_npow_aug_subset_succ_pow_aug R G n) a

theorem quot_aug_finite_ord' (n : ℕ) (x : quotNatOverSucc R G (n+1)) : addOrderOf x > 0 := by
  apply addOrderOf_pos_iff.mpr
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  use Fintype.card G
  constructor ; exact Fintype.card_pos
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [← QuotientAddGroup.mk_nsmul (nrpow_addsubgroup_of_npow R G (n+1) 1) x (Fintype.card G)]
  obtain ⟨x, hx⟩ := x
  replace hx := card_pwsmul_npow_aug_subset_succ_pow_aug'_apply R G n x hx
  rw [show (0 : quotNatOverSucc R G (n + 1)) = QuotientAddGroup.mk 0 from rfl]
  rw [QuotientAddGroup.eq]
  unfold nrpow_addsubgroup_of_npow
  simp only [nsmul_eq_mul, AddSubmonoidClass.mk_nsmul, add_zero, Subtype.exists, neg_mem_iff,
    AddSubgroup.mem_mk, Set.mem_setOf_eq, Subtype.mk.injEq, exists_prop, exists_eq_right] at hx ⊢
  rwa [show n + 1 + 1 = n + 2 from rfl]

theorem quot_aug_finite_ord (n : ℕ) (x : quotNatOverSucc R G (n+1)) : IsOfFinAddOrder x := by
  rw [← @addOrderOf_pos_iff]
  exact quot_aug_finite_ord' n x

instance quot_torsion (n : ℕ) : AddMonoid.IsTorsion (quotNatOverSucc R G (n+1)) :=
  fun x => quot_aug_finite_ord n x

end Pointwise

end Quotients

section NPow
open Pointwise

variable [Fintype G]

lemma npow_mem.proof_1 (n : ℕ) : ((Δ R,G) ^ n : Ideal (MonoidAlgebra R G)) = Ideal.span (∏ _i in Finset.range n, ((Δ R,G) : Set (MonoidAlgebra R G))) := by
  induction n with
  | zero => simp only [Nat.zero_eq, pow_zero, Ideal.one_eq_top, Finset.range_zero,
      Finset.prod_const, Finset.card_empty, Ideal.span_one]
  | succ n ih =>
    rw [pow_succ, Nat.succ_eq_add_one, ih, Finset.prod_range_add, ← Ideal.span_mul_span', mul_comm]
    simp only [Finset.prod_const, Finset.card_range, Finset.range_one, Finset.card_singleton,
      pow_one, Ideal.span_eq]

lemma npow_mem.proof_2 (n : ℕ) : ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) = Ideal.span {∏ i in Finset.range (n+1), ↑(f i) | f : ℕ → (Δ R,G)} := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, zero_add, pow_one, Finset.range_one, Finset.prod_singleton]
    conv => lhs ; rw [← Ideal.span_eq (Δ R,G)]
    congr ; ext y ; simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · intro h ; use fun _ => ⟨y,h⟩
    · rintro ⟨f, hf⟩ ; rw [← hf] ; exact Submodule.coe_mem (f 0)
  | succ n ih =>
    rw [pow_succ, Nat.succ_eq_add_one, ih]
    conv => enter [1, 1] ; rw [← Ideal.span_eq (Δ R,G)]
    rw [Ideal.span_mul_span, Set.iUnion.union_of_union_of_prod_toSet]
    congr ; ext x ; simp only [SetLike.mem_coe, Set.mem_setOf_eq, exists_exists_eq_and]
    constructor
    · rintro ⟨s, ⟨hs, ⟨f, ⟨hf, hsf⟩⟩⟩⟩
      let f' : ℕ → (Δ R,G) := fun i => by
        by_cases i < n + 1
        · exact f i
        · by_cases i = n + 1
          · exact ⟨s, hs⟩
          · exact 0
      use f'
      rw [@Finset.prod_range_add, mul_comm, Finset.range_one, Finset.prod_singleton,
        Finset.prod_range, Finset.prod_range]
      simp only [dite_eq_ite, add_zero, lt_self_iff_false, ite_true, ite_false, Fin.is_lt]
    · rintro ⟨f, hf⟩
      use f (n + 1)
      constructor ; exact Submodule.coe_mem (f (n + 1))
      use f ; rw [mul_comm]
      rw [Finset.prod_range] at hf ⊢
      rw [Fin.prod_univ_castSucc] at hf
      rw [← hf] ; simp only [Fin.coe_castSucc, Fin.val_last]

variable {R G} in
lemma npow_mem.proof_3' (n : ℕ) (x : MonoidAlgebra R G) :
    (∃ f : ℕ → (Δ R,G), ∏ i in Finset.range (n+1), (f i : MonoidAlgebra R G) = x) ↔
    (∃ f : ℕ → (Δ R,G), ∏ i in Finset.range (n+1), (∑ a in (f i : MonoidAlgebra R G).support \ {1},
      ((f i : MonoidAlgebra R G) a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) = x) := by
  constructor
  <;> rintro ⟨f, hf⟩
  <;> use f <;> rw [← hf]
  <;> congr <;> ext i
  · conv => rhs ; rw [Basis.mem_is_linearcomb_of_basis_singles (f ↑i : MonoidAlgebra R G) (Submodule.coe_mem (f ↑i))]
  · conv => lhs ; rw [Basis.mem_is_linearcomb_of_basis_singles (f ↑i : MonoidAlgebra R G) (Submodule.coe_mem (f ↑i))]

lemma npow_mem.proof_3 (n : ℕ) : {∏ i in Finset.range (n+1), (f i : MonoidAlgebra R G) | f : ℕ → (Δ R,G)} =
    {∏ i in Finset.range (n+1), (∑ a in (f i : MonoidAlgebra R G).support \ {1},
      ((f i : MonoidAlgebra R G) a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) | f : ℕ → (Δ R,G)} := by
  ext y
  simp only [Set.mem_setOf_eq, Finset.univ_eq_attach]
  exact proof_3' n y

variable {R G} in
lemma npow_mem.proof_4 (n : ℕ) (x : MonoidAlgebra R G) (hx : ∃ f : ℕ → (Δ R,G), ∏ i in Finset.range (n+1), (f ↑i : MonoidAlgebra R G) = x) :
    ∃ f : ℕ → (Δ R,G), ∑ p in Finset.pi (Finset.range (n + 1)) fun i => (f i : MonoidAlgebra R G).support \ {1},
    (∏ i in Finset.attach (Finset.range (n + 1)),
      ((f ↑i : MonoidAlgebra R G) (p ↑i i.property))) •
    ∏ i in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (p ↑i i.property) (1:R) - 1) = x := by
  have h' := (proof_3' n x).mp hx
  simp only [←Finset.sum_in_eq_sum_type] at h'
  have hf := h'.choose_spec
  have h := @Finset.prod_sum ℕ (MonoidAlgebra R G) _ (fun _ => G) _ _ (Finset.range (n+1)) (fun i => (h'.choose i : MonoidAlgebra R G).support \ {1})
    (fun i a => ((h'.choose i : MonoidAlgebra R G) a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G)))
  rw [h] at hf
  use h'.choose
  conv => rhs ; rw [← hf]
  congr ; ext p
  rw [@Algebra.smul_def]
  simp only [map_prod, MonoidAlgebra.coe_algebraMap, Algebra.id.map_eq_id, Function.comp_apply,
    RingHom.id_apply]
  rw [← @Finset.prod_mul_distrib]
  congr ; ext i
  rw [@Algebra.smul_def]
  simp only [MonoidAlgebra.coe_algebraMap, Algebra.id.map_eq_id, Function.comp_apply,
    RingHom.id_apply]


lemma npow_mem.product_of_basis (n : ℕ) (f : (Finset.range (n+1)) → G) : ∏ i in Finset.attach (Finset.range (n + 1)),
    (MonoidAlgebra.single (f i) (1:R) - 1) ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) := by
  rw [proof_2]
  rw [← Ideal.submodule_span_eq]
  rw [Submodule.mem_span]
  intro S hS
  suffices ∏ i in Finset.attach (Finset.range (n + 1)),
      (MonoidAlgebra.single (f i) (1:R) - 1) ∈ {x | ∃ f : ℕ → (Δ R,G), ∏ i in Finset.range (n + 1), (f i : MonoidAlgebra R G) = x}
    from hS this
  simp only [Set.mem_setOf_eq]
  let f' : ℕ → (Δ R,G) := fun i => by
    by_cases i < n + 1
    · exact ⟨(MonoidAlgebra.single (f ⟨i, (Finset.mem_range.mpr h)⟩)) (1:R) - 1,
        Basis.basis_elements_are_in_set R G (f ⟨i, (Finset.mem_range.mpr h)⟩)⟩
    · exact 0
  use f'
  rw [← Finset.prod_attach (s := Finset.range (n+1)) ]
  congr ; ext ⟨i, hi⟩
  rw [Finset.mem_range] at hi
  simp only [hi, dite_true]

lemma npow_mem.smul_product_of_basis (n : ℕ) (r : R) (f : (Finset.range (n+1)) → G) : r • ∏ i in Finset.attach (Finset.range (n + 1)),
    (MonoidAlgebra.single (f i) (1:R) - 1) ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) := by
  rw [@Algebra.smul_def]
  simp only [MonoidAlgebra.coe_algebraMap, Algebra.id.map_eq_id, Function.comp_apply,
    RingHom.id_apply]
  apply Ideal.mul_mem_left
  exact product_of_basis R G n fun i => f i

lemma npow_mem.linearcomb_of_product_of_basis (n : ℕ) (f : ℕ → (Δ R,G)) (r : R) :
    ∑ p in Finset.pi (Finset.range (n + 1)) fun i => (f i : MonoidAlgebra R G).support \ {1},
    r • ∏ i in Finset.attach (Finset.range (n + 1)),
    (MonoidAlgebra.single (p ↑i i.property) (1:R) - 1) ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) := by
  suffices ∀ p ∈ Finset.pi (Finset.range (n + 1)) fun i => (f i : MonoidAlgebra R G).support \ {1},
      ∏ i in Finset.attach (Finset.range (n + 1)),
      (MonoidAlgebra.single (p ↑i i.property) (1:R) - 1) ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) by {
    have h : ∀ p ∈ Finset.pi (Finset.range (n + 1)) fun i => (f i : MonoidAlgebra R G).support \ {1},
        r • ∏ i in Finset.attach (Finset.range (n + 1)),
        (MonoidAlgebra.single (p ↑i i.property) (1:R) - 1) ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G)) := by
      intro p hp
      rw [@Algebra.smul_def]
      simp only [MonoidAlgebra.coe_algebraMap, Algebra.id.map_eq_id, Function.comp_apply,
        RingHom.id_apply]
      apply Ideal.mul_mem_left
      exact this p hp
    apply Ideal.sum_mem
    exact fun c a => h c a
  }
  intro p _
  exact product_of_basis R G n (fun i => p ↑i i.property)


lemma npow_mem.linearcomb_prod_basis.proof_1 (n : ℕ) (x : MonoidAlgebra R G) (hx : x ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G))) :
    ∃ m, ∃ f : Fin m → ℕ → (Δ R,G), ∃ r : Fin m → ((a : ℕ) → a ∈ Finset.range (n + 1) → G) → R, x =
    ∑ i : Fin m, ∑ p in Finset.pi (Finset.range (n + 1)) fun j => (f i j : MonoidAlgebra R G).support \ {1},
      r i p • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (p ↑j j.property) (1:R) - 1) := by
  rw [proof_2, ← Ideal.submodule_span_eq, mem_span_set'] at hx
  obtain ⟨m, ⟨f, ⟨g, h⟩⟩⟩ := hx
  let g' : Fin m → ℕ → (Δ R,G) := fun i j => by
    obtain ⟨d, hd⟩ := g i
    rw [Set.mem_setOf_eq] at hd
    by_cases j = ↑(Fin.last n)
    · exact f i • hd.choose j
    · exact hd.choose j
  have hg : ∀ i : Fin m, f i • (g i : MonoidAlgebra R G) = ∏ j in Finset.range (n + 1), (g' i j : MonoidAlgebra R G) := by
    intro i
    dsimp only [Set.mem_setOf_eq, Set.coe_setOf, eq_mp_eq_cast, cast_eq]
    rw [Finset.prod_range_add]
    simp only [smul_eq_mul, Fin.val_last, Finset.range_one, add_right_inj, dite_eq_ite,
      Finset.prod_singleton, zero_ne_one, add_zero, ite_false]
    rw [← Finset.prod_attach]
    conv =>
      enter [2,1,2,j]
      rw [dif_neg (Nat.lt_or_gt.mpr (Or.inl (Finset.mem_range.mp j.property)))]
    simp only [ite_true, SetLike.val_smul, smul_eq_mul]
    conv => rhs ; rw [←mul_assoc, mul_comm _ (f i), mul_assoc]
    congr
    let hd := (g i).2
    rw [Set.mem_setOf_eq] at hd
    have hh := Finset.prod_attach (s:=(Finset.range n)) (f := fun j => (hd.choose j : MonoidAlgebra R G))
    rw [hh]
    conv => lhs ; rw [← hd.choose_spec, Finset.prod_range_add]
    congr ; simp only [Finset.range_one, Set.mem_setOf_eq, Finset.prod_singleton, add_zero]
  have hgen (i : Fin m) := proof_4 n (f i • ↑(g i)) <| by
    use g' i ; exact (hg i).symm
  conv at h => enter [1,2,i] ; rw [← (hgen i).choose_spec]
  let f' : Fin m → ℕ → (Δ R,G) := fun i => (hgen i).choose
  let r' : Fin m → ((a : ℕ) → a ∈ Finset.range (n + 1) → G) → R := fun i p =>
    (∏ j in Finset.attach (Finset.range (n + 1)), ((f' i ↑j : MonoidAlgebra R G) (p ↑j j.property)))
  use m ; use f' ; use r'
  exact h.symm

lemma npow_mem.linearcomb_prod_basis.proof_2 (n : ℕ) (x : MonoidAlgebra R G) (hx : x ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G))) :
    ∃ A : Type u_2, ∃ α : Finset A, ∃ r : A → R, ∃ f : A → Finset.range (n + 1) → G, x =
    ∑ a in α, r a • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (f a j) (1:R) - 1) := by
  obtain ⟨m, ⟨f, ⟨r, h⟩⟩⟩ := linearcomb_prod_basis.proof_1 R G n x hx
  let fi := fun (i:ℕ) => by
    by_cases i < m
    · exact
      ∑ p in Finset.pi (Finset.range (n + 1)) fun j => ((f ⟨i,h⟩ j) : MonoidAlgebra R G).support \ {1},
        r ⟨i,h⟩ p • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (p ↑j j.property) (1:R) - 1)
    · exact 0
  have hfi (i : Fin m) : fi ↑i =
      ∑ p in Finset.pi (Finset.range (n + 1)) fun j => ((f i j) : MonoidAlgebra R G).support \ {1},
        r i p • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (p ↑j j.property) (1:R) - 1) := by
    simp only [Finsupp.mem_support_iff, ne_eq, not_not, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]
  conv at h => enter [2,2,i] ; rw [← hfi]
  rw [← Finset.sum_range, ←Finset.sum_attach] at h
  dsimp only [fi] at h
  conv at h => enter [2,2,i] ; rw [dif_pos (List.mem_range.mp i.property)]
  rw [Finset.sum_sigma'] at h
  let α := Finset.sigma (Finset.attach (Finset.range m)) fun i =>
      Finset.pi (Finset.range (n + 1)) fun j => ((f ⟨↑i, (List.mem_range.mp i.property)⟩ j) : MonoidAlgebra R G).support \ {1}
  have hα : x = ∑ a in α,
    r ⟨↑a.fst, List.mem_range.mp a.fst.property⟩ a.snd •
      ∏ j in Finset.attach (Finset.range (n + 1)),
        (MonoidAlgebra.single (Sigma.snd a ↑j j.property) 1 - 1) := h
  let A := (_ : { i // i ∈ Finset.range m }) × ((a : ℕ) → a ∈ Finset.range (n + 1) → G)
  let r' : A → R := fun a => r ⟨↑a.fst, List.mem_range.mp a.fst.property⟩ a.snd
  have hr' (a : A) : r' a = r ⟨↑a.fst, List.mem_range.mp a.fst.property⟩ a.snd := rfl
  let f' : A → Finset.range (n + 1) → G := fun a j => Sigma.snd a ↑j j.property
  have hf' (a : A) (j : Finset.range (n + 1)) : f' a j = Sigma.snd a ↑j j.property := rfl
  conv at hα => enter [2,2,a] ; rw [← hr']
  conv at hα => enter [2,2,a,2,2,j] ; rw [← hf' a j]
  use A ; use α ; use r' ; use f'


theorem npow_mem.linearcomb_prod_basis (n : ℕ) (x : MonoidAlgebra R G) (hx : x ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G))) :
    ∃ m, ∃ f : Fin m → Finset.range (n + 1) → G, ∃ r : Fin m → R, x =
    ∑ i : Fin m, r i • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (f i j) (1:R) - 1) := by
  obtain ⟨A, ⟨α, ⟨r, ⟨f, h⟩⟩⟩⟩ := linearcomb_prod_basis.proof_2 R G n x hx
  rw [Finset.sum_equiv_sum_indexed_by_card' α (fun a => r a • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (f a j) (1:R) - 1))] at h
  let m' := Finset.card α
  let f' : Fin m' → { i // i ∈ Finset.range (n + 1) } → G := fun i j => f (↑(Equiv.invFun (Finset.equivFin α) i)) j
  let r' : Fin m' → R := fun i => r ↑(Equiv.invFun (Finset.equivFin α) i)
  use m' ; use f' ; use r'

theorem npow_mem.linearcomb_prod_basis' (n : ℕ) (x : MonoidAlgebra R G) (hx : x ∈ ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G))) :
    ∃ m, ∃ f : Finset.range m → Finset.range (n + 1) → G, ∃ r : Finset.range m → R, x =
    ∑ i in Finset.attach (Finset.range m), r i • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (f i j) (1:R) - 1) := by
  obtain ⟨m, ⟨f, ⟨r, h⟩⟩⟩ := linearcomb_prod_basis R G n x hx
  use m
  use (fun i => f ⟨↑i, List.mem_range.mp i.property⟩)
  use (fun i => r ⟨↑i, List.mem_range.mp i.property⟩)
  rw [h, Finset.sum_fin_eq_sum_range, ← Finset.sum_attach]
  congr ; ext
  rw [dif_pos]

theorem npow_mem.linearcomb_prod_basis_subtype₁ (n : ℕ) (x : ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G))) :
    ∃ m, ∃ f : Finset.range m → Finset.range (n+1) → G, ∃ r : Finset.range m → R, x =
    ∑ i in Finset.attach (Finset.range m), ⟨r i • ∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (f i j) (1:R) - 1), smul_product_of_basis R G n (r i) (f i)⟩ := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨m, ⟨f, ⟨r, h⟩⟩⟩ := linearcomb_prod_basis' R G n x hx
  use m ; use f ; use r
  rw [@Subtype.ext_iff]
  simpa only [AddSubmonoid.coe_finset_sum]

theorem npow_mem.linearcomb_prod_basis_subtype₂ (n : ℕ) (x : ((Δ R,G) ^ (n+1) : Ideal (MonoidAlgebra R G))) :
    ∃ m, ∃ f : Finset.range m → Finset.range (n+1) → G, ∃ r : Finset.range m → R, x =
    ∑ i in Finset.attach (Finset.range m), r i • ⟨∏ j in Finset.attach (Finset.range (n + 1)), (MonoidAlgebra.single (f i j) (1:R) - 1), product_of_basis R G n (f i)⟩ := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨m, ⟨f, ⟨r, h⟩⟩⟩ := linearcomb_prod_basis' R G n x hx
  use m ; use f ; use r
  rw [@Subtype.ext_iff]
  simpa only [AddSubmonoid.coe_finset_sum]

end NPow

end AugmentationIdeal
