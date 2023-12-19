import Mathlib
import Project.AugmentationMap

--##TODO change the definitions to use the .lift version and then use all the api for it
open BigOperators

variable (R G : Type*) [CommGroup G] [CommRing R] [NoZeroDivisors R] [DecidableEq G]

noncomputable def AugmentationIdeal : Ideal (MonoidAlgebra R G) := RingHom.ker (AugmentationIdeal.AugmentationMap (R:=R) (G:=G))

-- A computable version of AugmentationIdeal
def AugmentationIdeal' : Ideal (MonoidAlgebra R G) := RingHom.ker (AugmentationIdeal'.AugmentationMap (R:=R) (G:=G))

lemma AugmentationIdeal'.eq : AugmentationIdeal' R G = AugmentationIdeal R G := by
  unfold AugmentationIdeal' AugmentationIdeal
  simp

instance Ideal.mul (I : Ideal R) : Mul I where
  mul f g := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', hg⟩ := g
    exact ⟨f' * g', Ideal.mul_mem_left I f' hg⟩

namespace AugmentationIdeal

scoped notation "Δ" R "," G => AugmentationIdeal R G
scoped notation "Δ'" R "," G => AugmentationIdeal' R G

variable {R G} in
@[simp]
lemma mem (f : MonoidAlgebra R G) : f ∈ (Δ R,G) ↔ ∑ a in f.support, f a = 0 := by
  unfold AugmentationIdeal
  rw [@RingHom.mem_ker]
  rw [AugmentationMap.fun_def']

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

namespace Finsupp
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
  exact Finsupp.finsupp_is_sum_of_singles R G f

lemma sum_single_is_single_sum (f : G →₀ R) (g : G) : (∑ a in f.support, (f a) • (Finsupp.single g (1 : R))) = Finsupp.single g (∑ a in f.support, (f a)) := by
  conv => enter [1, 2, a] ; rw[Finsupp.smul_single', mul_one]
  rw [@Finsupp.single_finset_sum]

end Finsupp

namespace AugmentationIdeal.Basis

lemma basis_elements_are_in_set (g : G) : (MonoidAlgebra.single g (1 : R)) - (1 : MonoidAlgebra R G) ∈ Δ R,G := by
  unfold AugmentationIdeal
  rw [RingHom.mem_ker, map_sub]
  by_cases (1:R) = 0
  · simp [AugmentationMap.fun_def', h]
  · simp_rw [AugmentationMap.fun_def'', MonoidAlgebra.one_def]
    rw [Finsupp.support_single_ne_zero, Finsupp.support_single_ne_zero]
    simp ; assumption'

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
      exact Finsupp.finsupp_is_linear_combo_of_singles R G f
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        (∑ a in f.support, (f a) • (1 : MonoidAlgebra R G)) := by
      conv => enter [1, 2, a] ; rw [smul_add]
      rw [← @Finset.sum_add_distrib]
    _ = (∑ a in f.support, (f a) • ((MonoidAlgebra.single a (1 : R)) - (1 : MonoidAlgebra R G))) +
        MonoidAlgebra.single 1 (∑ a in f.support, (f a)) := by
      rw [MonoidAlgebra.one_def, Finsupp.sum_single_is_single_sum R G f 1]
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
  simp [basis_def, support_to_basis_index, basis_def']
  rw [← Finset.sum_attach]

theorem mem_is_linearcomb_of_basis (f : MonoidAlgebra R G) (h : f ∈ Δ R,G) :
    (f : G →₀ R) = (∑ a : ↑(f.support \ {1}), (f a) • (basis_def R G (support_to_basis_index f a))) := by
  unfold basis_def ; simp
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
    property := by simp
  }
  dsimp
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

noncomputable instance basis : Basis {g : G | g ≠ 1} R (Δ R,G) := Basis.mk Basis.linear_independent Basis.spans_top_set

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

section Pointwise
open Pointwise
variable (M : Type*) [AddCommMonoid M] [Module R M]
variable (α : Type*) [Monoid α] [DistribMulAction α R] --[SMulCommClass α R M]

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

variable [DecidableEq (MonoidAlgebra R G)]
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
  dsimp
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
  dsimp ; rw [← h]
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
  apply Ideal.mul_mem_mul <;> simp

theorem card_pwsmul_pow_aug_subset_succ_pow_aug' (n : ℕ):
    {Fintype.card G • f | f ∈ (Δ R,G) ^ (n+1) } ⊆ ((Δ R,G) ^ (n + 2) : Ideal (MonoidAlgebra R G)) :=
  card_pwsmul_aug_npow_subset_def R G n |>.trans
    <| card_pwsmul_aug_mul_npow_aug_subset R G n |>.trans
    <| aug_sq_mul_aug_npow_def_subset R G n


end Pointwise


end Quotients

lemma aser (f : MonoidAlgebra R G) (a₁ : ↑(f.support \ {1})) : ↑a₁ ∈ {g | g ≠ (1:G)} := by
  obtain ⟨_, ha⟩ := a₁
  simp at ha
  simp [ha] at *

lemma aser' (f : MonoidAlgebra R G) (a₁ : ↑(f.support \ {1})) (a : G) : (↑a₁)⁻¹ * a ∈ {g | g ≠ (1:G)} := by
  obtain ⟨a', ha'⟩ := a₁
  simp at ha'
  simp [ha']

example (f g : G →₀ R) (a : G) : (f - g) a = f a - g a := by
  exact rfl

example (f g : MonoidAlgebra R G) (a : G) : (f - g) a = f a - g a := by
  exact rfl

example (a : G) : (MonoidAlgebra.single a (1:R) - MonoidAlgebra.single (1:G) (1:R)) a = MonoidAlgebra.single a (1:R) a - MonoidAlgebra.single (1:G) (1:R) a :=
  by rfl

lemma l123 (a k : G) : (MonoidAlgebra.single k (1:R) - 1) a = MonoidAlgebra.single k (1:R) a - MonoidAlgebra.single (1:G) (1:R) a := by
  rfl


lemma logic {A B : Prop} (h : A ∨ B) (h₁ : ¬B) : A := by
  cases h with
  | inl h₂ => assumption
  | inr h₂ => exfalso ; apply h₁ h₂


example (α : Finset G) (f : G → MonoidAlgebra R G) (a : G) : (∑ i in α, f i) a = ∑ i in α, f i a := by
  exact Finset.sum_apply' a

example (k a : G) (h : a ≠ k): MonoidAlgebra.single k (1:R) a = 0 := by exact
  Finsupp.single_eq_of_ne (id (Ne.symm h))

variable {R G} in
lemma ase (f : MonoidAlgebra R G) (a₁ : G) (k : { x // x ∈ (f.support \ {1}) \ {a₁} }) : ↑k ≠ a₁ := by
  obtain ⟨k', hk⟩ := k
  simp at hk
  simp [hk]

lemma asy (F : Set G) (a x : G) (h : a ∉ F) (hx : x ∈ F): a ≠ x := by
  exact Ne.symm (ne_of_mem_of_not_mem hx h)

lemma ase' (f : MonoidAlgebra R G) (a₁ : { x // x ∈ f.support}) (h1 : 1 ∉ f.support) : (1:G) ≠ a₁ :=
  asy G f.support 1 a₁.val h1 a₁.property



lemma asd (f : MonoidAlgebra R G) (a₁ : G) (h₁ : a₁ ≠ 1) :
    ∑ k in f.support \ {1}, f k • (MonoidAlgebra.single k (1:R) - 1) a₁ = f a₁ • (MonoidAlgebra.single a₁ (1:R) - 1) a₁:= by
  conv =>
    enter [1,2,k,2]
    rw [show (MonoidAlgebra.single (k:G) (1:R) - 1) a₁ = MonoidAlgebra.single (k:G) (1:R) a₁ - MonoidAlgebra.single (1:G) (1:R) a₁ from rfl]
  by_cases a₁ ∉ f.support \ {1}
  · rw [finseter]
    have h' := h
    simp at h ; apply not_or_of_imp at h ; simp at h
    conv =>
      enter [1,2,x,2]
      rw [Finsupp.single_eq_of_ne (Ne.symm h₁)]
      rw [Finsupp.single_eq_of_ne ((ne_of_mem_of_not_mem x.property h'))]
      rw [sub_zero]
    simp
    exact Or.inl <| logic h h₁
  · rw [show f.support \ {1} = (f.support \ {1}) ∪ {a₁} by
      simp at * ; assumption
    ]
    rw [show ∑ k in (f.support \ {1}) ∪ {a₁} , f k • (MonoidAlgebra.single (k:G) (1:R) a₁ - MonoidAlgebra.single (1:G) (1:R) a₁) =
        (∑ k in (f.support \ {1}) \ {a₁}, f k • (MonoidAlgebra.single (k:G) (1:R) a₁ - MonoidAlgebra.single (1:G) (1:R) a₁)) + ∑ k in {a₁}, f k • (MonoidAlgebra.single (k:G) (1:R) a₁ - MonoidAlgebra.single (1:G) (1:R) a₁) by
      rw [Finset.sum_union_is_right_and_sdiff]
    ]
    rw [finseter]
    simp at h
    obtain ⟨_,h₂⟩ := h
    conv =>
      enter [1,1,2,k,2]
      rw [Finsupp.single_eq_of_ne (ase f a₁ k), Finsupp.single_eq_of_ne (Ne.symm h₂), sub_zero]
    simp
    rw [show (MonoidAlgebra.single a₁ (1:R) - 1) a₁ = (MonoidAlgebra.single a₁ 1 a₁ - MonoidAlgebra.single (1:G) (1:R) a₁) from rfl]
    simp [Finsupp.single_eq_of_ne]

lemma finsetsing (a : G) (f : MonoidAlgebra R G) : a ∉ f.support \ {a} := by
  simp

lemma asd' (f : MonoidAlgebra R G) (hf : f ∈ Δ R,G) :
    ∑ k in f.support \ {1}, f k • (MonoidAlgebra.single k (1:R) - 1) 1 = f 1 := by
  rw [MonoidAlgebra.one_def]
  rw [finseter]
  conv =>
    enter [1, 2, k, 2]
    rw [show (MonoidAlgebra.single (k:G) (1:R) - MonoidAlgebra.single (1:G) (1:R)) 1 = MonoidAlgebra.single (k:G) (1:R) (1:G) - MonoidAlgebra.single (1:G) 1 1 by rfl]
    simp
    rw [Finsupp.single_eq_of_ne ((ne_of_mem_of_not_mem k.property (finsetsing 1 f)))]
  rw [← finseter ↑(f.support \ {1}) (fun k => f ↑k • (0 - 1))]
  simp
  by_cases 1 ∈ f.support
  · rw [show f 1 = ∑ x in {1}, f x from (Finset.sum_singleton (fun x => f x) 1).symm]
    rw [@neg_eq_iff_add_eq_zero]
    rw [← Finset.sum_union_is_right_and_sdiff]
    rw [show f.support ∪ {1} = f.support from Finset.union_eq_left.mpr <| Finset.singleton_subset_iff.mpr h]
    rwa [← mem]
  · rw [show f.support \ {1} = f.support from Finset.sdiff_singleton_eq_self h]
    rw [@Finsupp.not_mem_support_iff] at h
    rwa [h, neg_eq_zero, ← mem]


example (f : MonoidAlgebra R G) (a k : G): f k • (MonoidAlgebra.single k (1:R) - 1) a = (f k • (MonoidAlgebra.single k (1:R) - 1)) a := by rfl


theorem mul_def (f g : MonoidAlgebra R G) (hf : f ∈ Δ R,G) (hg : g ∈ Δ R,G) :
    (f * g) x = ∑ a₁ in f.support \ {1}, ((f a₁ * g (a₁⁻¹ * x)) • (MonoidAlgebra.single a₁ (1:R) - 1) * (MonoidAlgebra.single (a₁⁻¹ * x) (1:R) - 1)) x := by
  rw [AugmentationIdeal'.AugmentationMap.mul_def' (f : MonoidAlgebra R G) (g : MonoidAlgebra R G) x]
  conv =>
    enter [1,2,a₁]
    rw [Basis.mem_is_linearcomb_of_basis_singles f hf, Basis.mem_is_linearcomb_of_basis_singles g hg]
    rw [Finset.sum_apply', Finset.sum_apply']
  rw [finseter]
  conv =>
    enter [1,2,a₁,1,2,k]
    rw [show (f k • (MonoidAlgebra.single k (1:R) - 1)) a₁ = f k • (MonoidAlgebra.single k (1:R) - 1) a₁ from rfl]
  conv =>
    enter [1,2,a₁,2,2,k]
    rw [show (g k • (MonoidAlgebra.single k (1:R) - 1)) ((↑a₁)⁻¹ * x) = g k • (MonoidAlgebra.single k (1:R) - 1) ((↑a₁)⁻¹ * x) from rfl]

  by_cases 1 ∉ f.support
  conv =>
    enter [1,2,a₁]
    rw [asd f a₁ (asy G f.support 1 a₁.val h a₁.property).symm]


#check QuotientGroup.quotientKerEquivRange

variable (H₁ H₂ : Type*) [Group H₁] [AddGroup H₂]
#check H₁ ≃* Multiplicative H₂

end AugmentationIdeal