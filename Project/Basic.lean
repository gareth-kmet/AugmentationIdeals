import Mathlib
import Project.AugmentationMap


variable (R G : Type*) [CommGroup G] [CommRing R] [NoZeroDivisors R] [DecidableEq G]

def AugmentationIdeal : Ideal (MonoidAlgebra R G) := RingHom.ker (AugmentationIdeal.AugmentationMap R G)

namespace AugmentationIdeal

scoped notation "Δ" R "," G => AugmentationIdeal R G

noncomputable section Quotients

variable (n r : ℕ)

--Notated as `Qₙᵣ` in the thesis
def quotOfPowers : Ideal (MonoidAlgebra R G) :=
  ((Δ R,G) ^ n) / ((Δ R,G) ^ (n + r))

--Notated as `Qₙ` in the thesis
def quotNatOverId : Ideal (MonoidAlgebra R G) := quotOfPowers R G n 1

--Notated as `Pₙ` in the thesis
def quotIdOverNat : Ideal (MonoidAlgebra R G) := quotOfPowers R G 1 n

end Quotients

end AugmentationIdeal

noncomputable section Basis

namespace Finsupp
/-
Lemmas about funute support functions and their sums
-/

open BigOperators

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
  exact Finsupp.finsupp_is_sum_of_singles R G f

lemma sum_single_is_single_sum (f : G →₀ R) (g : G) : (∑ a in f.support, (f a) • (Finsupp.single g (1 : R))) = Finsupp.single g (∑ a in f.support, (f a)) := by
  conv => enter [1, 2, a] ; rw[Finsupp.smul_single', mul_one]
  rw [@Finsupp.single_finset_sum]

end Finsupp

namespace AugmentationIdeal.Basis
/-
the definiton of the basis in the augmentation ideal
-/
open BigOperators


lemma basis_elements_are_in_set (g : G) : (MonoidAlgebra.single g (1 : R)) - (1 : MonoidAlgebra R G) ∈ Δ R,G := by
  unfold AugmentationIdeal
  rw [RingHom.mem_ker, map_sub]
  unfold AugmentationMap ; dsimp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw[MonoidAlgebra.one_def]
  by_cases (1:R) = 0
  · simp only [h, Finsupp.single_zero, Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply,
      Finset.sum_const_zero, sub_self]
  · rw [Finsupp.support_single_ne_zero, Finsupp.support_single_ne_zero, Finset.sum_singleton,
    Finset.sum_singleton, Finsupp.single_eq_same, Finsupp.single_eq_same, sub_self]
    assumption'

def basis_def : {g : G | g ≠ 1} → Δ R,G := fun g => {
  val := (MonoidAlgebra.single (g : G) (1 : R)) - (1 : MonoidAlgebra R G)
  property := basis_elements_are_in_set R G g
}

variable {R G}

theorem funct_is_linearcomb_of_basis_with_offset (f : G →₀ R) : f =
    (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) + MonoidAlgebra.single 1 (AugmentationMap R G f) := by
  calc f
    _ = ∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G) + (1 : MonoidAlgebra R G)) := by
      conv => enter [2, 2, a, 2] ; rw [sub_add_cancel]
      exact Finsupp.finsupp_is_linear_combo_of_singles R G f
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        (∑ a in f.support, (f a) • (1 : MonoidAlgebra R G)) := by
      conv => enter [1, 2, a] ; rw [smul_add]
      rw [← @Finset.sum_add_distrib]
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        MonoidAlgebra.single 1 (∑ a in f.support, (f a)) := by
      rw [MonoidAlgebra.one_def, Finsupp.sum_single_is_single_sum R G f 1]
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        MonoidAlgebra.single 1 (AugmentationMap R G f) := by rw [AugmentationMap] ; dsimp

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

theorem mem_is_linearcomb_of_basis (f : MonoidAlgebra R G) (h : f ∈ Δ R,G) :
    (f : G →₀ R) = (∑ a : ↑(f.support \ {1}), (f a) • (basis_def R G (support_to_basis_index f a))) := by
  conv => lhs ; rw [mem_is_linearcomb_of_basis_singles f h]
  unfold basis_def support_to_basis_index
  simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.singleton_subset_iff,
    Finset.univ_eq_attach, AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid,
    Submodule.coe_smul_of_tower]
  rw [← Finset.sum_attach]

lemma coe_iff (a : Δ R,G) (b : MonoidAlgebra R G) (h : b ∈ Δ R,G) : a = ⟨b, h⟩ ↔ ↑a = b := by
  constructor
  · obtain ⟨a', ha'⟩ := a
    simp only [Subtype.mk.injEq, imp_self]
  · exact fun a_1 => SetCoe.ext a_1

def basis_spans_top_set : ⊤ ≤ Submodule.span R (Set.range (basis_def R G)) := by
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
  dsimp
  let f := fun i => x ↑((Finset.equivFin (x.support \ {1})).symm i) •
      basis_def R G (support_to_basis_index x ((Finset.equivFin (x.support \ {1})).symm i))
  let g := fun (a : ↑(x.support \ {1})) => x ↑a • basis_def R G (support_to_basis_index x a)
  rw[Equiv.sum_comp' (Finset.equivFin (x.support \ {1})).symm f g]
  · dsimp only [g]
    rw [coe_iff, ←mem_is_linearcomb_of_basis x hx]
  · intros ; rfl

example (α : Finset G) (f : G → R) : (∀ a ∈ α, f a = 0) → ∑ a in α, f a = 0 := by
  exact fun a => Finset.sum_eq_zero a

def basis_linear_independent : LinearIndependent R (basis_def R G) := by
  rw [@linearIndependent_iff']
  intro s f h
  rw [@Subtype.ext_iff, @Submodule.coe_sum] at h
  unfold basis_def at h
  dsimp at h
  have h' := Finsupp.support_eq_empty.mpr h
  rw [@Finset.eq_empty_iff_forall_not_mem] at h'
  rintro ⟨i, hi⟩ hi'
  specialize h' i
  rw [@Finsupp.not_mem_support_iff] at h'
  rw[Finset.sum_apply'] at h'
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


def basis : Basis {g : G | g ≠ 1} R (Δ R,G) := Basis.mk basis_linear_independent basis_spans_top_set

end Basis

end AugmentationIdeal
