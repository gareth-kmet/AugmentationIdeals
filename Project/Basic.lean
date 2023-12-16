import Mathlib
import Project.AugmentationMap

open BigOperators

variable (R G : Type*) [CommGroup G] [CommRing R] [NoZeroDivisors R] [DecidableEq G]

def AugmentationIdeal : Ideal (MonoidAlgebra R G) := RingHom.ker (AugmentationIdeal.AugmentationMap' (R:=R) (G:=G))

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

lemma basis_elements_are_in_set (g : G) : (MonoidAlgebra.single g (1 : R)) - (1 : MonoidAlgebra R G) ∈ Δ R,G := by
  unfold AugmentationIdeal
  rw [RingHom.mem_ker, map_sub]
  unfold AugmentationMap' ; dsimp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw[MonoidAlgebra.one_def]
  by_cases (1:R) = 0
  · simp only [h, Finsupp.single_zero, Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply,
      Finset.sum_const_zero, sub_self]
  · rw [Finsupp.support_single_ne_zero, Finsupp.support_single_ne_zero, Finset.sum_singleton,
    Finset.sum_singleton, Finsupp.single_eq_same, Finsupp.single_eq_same, sub_self]
    assumption'

def basis_def' : {g : G | g ≠ 1} → MonoidAlgebra R G := fun g =>
  (MonoidAlgebra.single (g : G) (1 : R)) - (1 : MonoidAlgebra R G)

def basis_def : {g : G | g ≠ 1} → Δ R,G := fun g => {
  val := basis_def' R G g
  property := basis_elements_are_in_set R G g
}

variable {R G}

theorem funct_is_linearcomb_of_basis_with_offset (f : G →₀ R) : f =
    (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) + MonoidAlgebra.single 1 (AugmentationMap' f) := by
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
        MonoidAlgebra.single 1 (AugmentationMap' f) := by rw [AugmentationMap'] ; dsimp

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
  unfold basis_def support_to_basis_index basis_def'
  simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.singleton_subset_iff,
    Finset.univ_eq_attach, AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid,
    Submodule.coe_smul_of_tower]
  rw [← Finset.sum_attach]

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
  dsimp
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
  dsimp at h
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

instance basis : Basis {g : G | g ≠ 1} R (Δ R,G) := Basis.mk Basis.linear_independent Basis.spans_top_set

@[simp]
lemma mul_distrib (f₁ f₂ g₁ g₂ : G) (r₁ r₂ r₃ r₄ : R) : (MonoidAlgebra.single f₁ r₁ + MonoidAlgebra.single f₂ r₂) * (MonoidAlgebra.single g₁ r₃ + MonoidAlgebra.single g₂ r₄) =
    (MonoidAlgebra.single (f₁*g₁) (r₁*r₃)) + (MonoidAlgebra.single (f₁*g₂) (r₁*r₄)) + (MonoidAlgebra.single (f₂*g₁) (r₂*r₃)) + (MonoidAlgebra.single (f₂*g₂) (r₂*r₄)) := by
  group ; simp only [MonoidAlgebra.single_mul_single, mul_comm]

@[simp]
lemma sub_distrib (g : G) (f : MonoidAlgebra R G) (r : R) : f - MonoidAlgebra.single g r = f + MonoidAlgebra.single g (-r) := by
  simp [sub_eq_iff_eq_add']

@[simp]
lemma mul_distrib_of_basis (f g : G) : (MonoidAlgebra.single f (1:R) - 1) * (MonoidAlgebra.single g (1:R) - 1) =
    (MonoidAlgebra.single (f*g) (1:R)) - (MonoidAlgebra.single f (1:R)) - (MonoidAlgebra.single g (1:R)) + 1 := by
  dsimp [MonoidAlgebra.one_def]
  simp only [sub_distrib, mul_distrib]
  group


namespace Cyclic

variable [hG : IsCyclic G] {R G}

def gen : G := Classical.choose hG.exists_generator

lemma gen_def : ∀ x : G, x ∈ Subgroup.zpowers gen := by
  exact Classical.choose_spec hG.exists_generator

lemma gen_is_top : (Subgroup.zpowers (G:=G) gen) = ⊤ := by
  rw [←top_le_iff]
  rw [@SetLike.le_def]
  exact fun ⦃x⦄ _ => gen_def x

def gen_pow_exists (g : G) : ∃ z : ℤ, g = gen ^ z := by
  apply Subgroup.exists_mem_zpowers.mp
  simp only [exists_eq_right']
  exact gen_def g

def gen_pow : G → ℤ :=
  fun g => Classical.choose <| gen_pow_exists g

lemma gen_pow_def (g : G) : gen ^ (gen_pow g) = g := by
  dsimp [gen_pow]
  rw[←Classical.choose_spec <| gen_pow_exists g]

lemma expand_basis_of_power_nat (g : G) (n : ℕ) : (MonoidAlgebra.single (g ^ n) (1:R) - 1) =
    (∑ i : Fin n, MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) * (MonoidAlgebra.single g (1:R) - 1):= by
  induction n with
  | zero => simp [MonoidAlgebra.one_def]
  | succ n ih =>
    rw [MonoidAlgebra.one_def]
    apply symm
    calc (∑ i : Fin (Nat.succ n), MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) * (MonoidAlgebra.single g (1:R) - 1)
      _ = (MonoidAlgebra.single (g ^ n) (1:R) + ∑ i : Fin n, MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) *  (MonoidAlgebra.single g (1:R) - 1) := by
        rw [show Nat.succ n = n + 1 from rfl, Fin.sum_univ_add]
        simp ; ring
      _ = (MonoidAlgebra.single (g ^ n) (1:R) * (MonoidAlgebra.single g (1:R) - 1)) +
          (∑ i : Fin n, MonoidAlgebra.single (g ^ (i:ℕ)) (1:R)) *  (MonoidAlgebra.single g (1:R) - 1) := by ring
      _ = (MonoidAlgebra.single (g ^ n) (1:R) * (MonoidAlgebra.single g (1:R) - 1)) + (MonoidAlgebra.single (g ^ n) (1:R) - 1) := by rw[ih]
      _ = ((MonoidAlgebra.single (g ^ n) (1:R) + MonoidAlgebra.single 1 0) * (MonoidAlgebra.single g (1:R) - MonoidAlgebra.single 1 1)) + (MonoidAlgebra.single (g ^ n) (1:R) - 1) := by
        simp only [Finsupp.single_zero, add_zero, MonoidAlgebra.one_def]
      _ = ((MonoidAlgebra.single (g ^ n) (1:R) + MonoidAlgebra.single 1 0) * (MonoidAlgebra.single g (1:R) + MonoidAlgebra.single 1 (-1))) + (MonoidAlgebra.single (g ^ n) (1:R) - 1) := by
        simp only [sub_distrib, Finsupp.single_neg]
      _ = (MonoidAlgebra.single (g ^ n * g) (1:R) + (MonoidAlgebra.single (g ^ n) (-1:R))) + (MonoidAlgebra.single (g ^ n) (1:R) + MonoidAlgebra.single 1 (-1)) := by
        congr ; rw [mul_distrib] ; group ; simp ; rw [← sub_distrib, MonoidAlgebra.one_def]
      _ = MonoidAlgebra.single (g ^ n * g) (1:R) - 1 := by
        simp [sub_distrib,MonoidAlgebra.one_def] ; group
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
    suffices (AugmentationMap' (R:=R) (G:=G)) (MonoidAlgebra.single gen 1 - 1) = 0 by {
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
    simp

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
  simp [MonoidAlgebra.one_def]

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
    rw [this] ; simp
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
  simp [MonoidAlgebra.one_def]
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

example (n : ℕ) (I : Ideal R) : (Nat.succ n) • I = n • I + I := by
  rw [← Nat.add_one]
  rw [@succ_nsmul']

theorem smul_eq_sup (n : ℕ) (I : Ideal R) : n • I = ⨆ i ∈ (Finset.range n : Set ℕ), I := by
  ext i
  induction n with
  | zero => simp
  | succ n =>
    rw [succ_nsmul, sup_succ]
    simp

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


------ ## Mathlib.LinearAlgebra.Span
------ ## Mathlib.Order.CompleteLattice

#check Submodule.span_induction
#check Submodule.smul_span
variable (n : ℕ)
#check n • Submodule.span R (Set.range (Basis.basis_def' R G))
#check n • (Basis.basis_def' R G)
#check n • (Δ R,G).carrier

#check Basis.mem_span
#check Basis.span_eq
#check Submodule.map
#check LinearMapClass


#check (MonoidAlgebra R G) →ₗ[R] (MonoidAlgebra R G)
variable (G) in
def smul_def_pointwise (n : ℕ) : (MonoidAlgebra R G) →ₗ[R] (MonoidAlgebra R G) where
  toFun r := n • r
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

scoped notation m " •ₚ " b => Submodule.map (smul_def_pointwise m) b

example : (Submodule.span R (Set.range (Basis.basis_def' R G))).map (smul_def_pointwise n) =
    Submodule.span R ((smul_def_pointwise n) '' Set.range (Basis.basis_def' R G)) := by
  rw [@LinearMap.map_span]

example (g : G) (r : R) (h : r ≠ 0) : (MonoidAlgebra.single g r).support = {g} := by
  rw [Finsupp.support_single_ne_zero g h]

variable (G) in
@[deprecated]
theorem card_smul_aug_sub_aug_squared : --- FLASE
    Fintype.card G • (Δ R,G) ≤ (Δ R,G) ^ 2 := by
  intro x
  rw [mem_smul_eq_sum]
  rintro ⟨g, hx⟩
  let f' : Finset.range (Fintype.card G) → ((Δ R,G) ^ 2 : Ideal (MonoidAlgebra R G)) := fun i => {
    val := g i
    property := by
      rw [@sq]
      rw [show ↑(g i) = ↑(g i) * (1:MonoidAlgebra R G) by group]
      apply Ideal.mul_mem_mul
      · exact Submodule.coe_mem (g i)
      · unfold AugmentationIdeal AugmentationMap'
        rw [@RingHom.mem_ker, MonoidAlgebra.one_def]
        simp
        by_cases (1:R) = 0
        · sorry
        · conv =>
            enter [1, 1]
            rw [Finsupp.support_single_ne_zero _ h]
          rw [@Finset.sum_singleton]
          simp
          sorry
  }


#check Ideal.mul_bot
example (I J : Ideal R) (x : R) : x ∈ I * J ↔ ∃ n, ∃ f₁ : Fin n → I, ∃ f₂ : Fin n → J, ∑ i : Fin n, (f₁ i : R) * (f₂ i) = x := by
  sorry

example (I J : Ideal R) : I / J = I := by
  ext x
  rw?
#check Ideal R

--use the distrib mul action given by Mathlib.Algebra.Module.Submodule.Pointwise
#check Submodule.pointwiseDistribMulAction

#check ((Δ R,G) )

section Pointwise
open scoped Pointwise

#synth DistribMulAction ℕ (Submodule R (MonoidAlgebra R G))
variable (n : ℕ)
#check n * (Submodule.span R (Set.range (Basis.basis_def' R G)))
#check n • (Submodule.span R (Set.range (Basis.basis_def' R G)))
#check Submodule.pointwiseDistribMulAction.smul n (Submodule.span R (Set.range (Basis.basis_def' R G)))

example (I : Submodule R (MonoidAlgebra R G)) : Submodule R (MonoidAlgebra R G) := n • I

example (I : Submodule R (MonoidAlgebra R G)) :
    Submodule.pointwiseDistribMulAction.smul n I = n * I := by sorry

example (I : Ideal (MonoidAlgebra R G)) : Submodule R (MonoidAlgebra R G) := by
  exact I

lemma card_smul_pw_aug_sub_aug_squared' :
  Submodule.pointwiseDistribMulAction.smul (Fintype.card G) (Submodule.span R (Set.range (Basis.basis_def' R G)))
  ≤ ((Δ R,G) ^ 2 : Ideal (MonoidAlgebra R G)) := by sorry

variable (M : Type*) [AddCommMonoid M] [Module R M]
variable (α : Type*) [Monoid α] [DistribMulAction α R] --[SMulCommClass α R M]

variable (G) in
lemma card_smul_pw_aug_sub_aug_squared :
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


end Pointwise

lemma card_smul_power_is_subset_succ (n : ℕ) : -- FALSE
    Fintype.card G • (Δ R,G) ^ (n + 1) ≤ (Δ R,G) ^ (n + 2) := by
  rw [show (Δ R,G) ^ (n + 1) = (Δ R,G) * (Δ R,G) ^ n from rfl]
  rw [nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul]
  rw [show (Δ R,G) ^ (n + 2) = (Δ R,G) ^ 2 * (Δ R,G) ^ n by ring]
  apply Ideal.mul_mono_left
  exact card_smul_aug_sub_aug_squared R G





end Quotients

end AugmentationIdeal
