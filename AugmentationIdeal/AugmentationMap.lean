/-
Authors : Gareth Kmet
-/
import AugmentationIdeal.Lemmas

/-!
## Augmentation Map

This file defines the Augmentation Map of the MonoidAlgebra of a group and communative ring.
It defines both a noncomputable definition (use `MonoidAlgebra.lift`) and a computable version. It also
defines a different definition for multiplication of `MonoidAlgebra`

## Main definitions

* `AugmentationIdeal.AugmentationMap` defines the ring homorphism that sends a `MonoidAlgebra` to the sum of its
  `R` coefficients
* `MonoidAlgebra.mul_def'` gives an alternative definition to the multiplication of `MonoidAlgebra` such that
   `f*g a = ∑ a in G, ∑ h in G, f h * g (h⁻¹ * a)`

## Future work

* generalize to non-communative rings as much as possible
* remove the `NoZeroDivisors R` variable

-/


open BigOperators Classical

variable {R G : Type*}

namespace AugmentationIdeal

variable [Group G] [CommRing R] [NoZeroDivisors R]

noncomputable def AugmentationMap : (MonoidAlgebra R G) →+* R :=
  MonoidAlgebra.lift R G R {
    toFun := fun _ => (1 : R)
    map_one' := rfl
    map_mul' := fun _ _ => by simp
  } |>.toRingHom

theorem AugmentationMap.fun_def (f : MonoidAlgebra R G) :
    AugmentationMap f = (Finsupp.sum f fun _ b => b) := by
  simp [AugmentationMap, MonoidAlgebra.lift_apply]

lemma AugmentationMap.fun_def' (f : MonoidAlgebra R G) :
    AugmentationMap f = ∑ a in ↑f.support, (f : G →₀ R) a := by
  simp[fun_def] ; rfl

lemma AugmentationMap.fun_def'' (f : MonoidAlgebra R G) :
    AugmentationMap f = ∑ a : f.support, (f :  G →₀ R) a := by
  simp [fun_def', Finset.sum_attach]

end AugmentationIdeal

namespace MonoidAlgebra

/-!
  Some Lemmas about multiplication within MonoidAlgebras
-/

variable [Group G] [Ring R] [NoZeroDivisors R]-- #TODO reduce
variable (f g : MonoidAlgebra R G)

lemma mul_def'' : f * g = ∑ a₁ in f.support, ∑ a₂ in g.support, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) := by
  rw[MonoidAlgebra.mul_def] ; unfold Finsupp.sum
  dsimp only

namespace mul_def'

lemma single_of_mul_is_non_zero_when_mul_is_single (ha₁ : a₁ ∈ f.support) (ha₂ : a₂ ∈ g.support) : MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) a ≠ 0 ↔ a₁ * a₂ = a := by
  constructor
  · intro ha
    rw [@Finsupp.single_apply_ne_zero] at ha
    obtain ⟨ha', _⟩ := ha ; exact id ha'.symm
  · intro ha
    rw [@Finsupp.single_apply_ne_zero]
    constructor ; exact id ha.symm
    suffices f a₁ ≠ 0 ∧ g a₂ ≠ 0 by
      obtain ⟨hf, hg⟩ := this
      exact mul_ne_zero hf hg
    exact ⟨Finsupp.mem_support_iff.mp ha₁, Finsupp.mem_support_iff.mp ha₂⟩

noncomputable def gsupport_finset (a₁ a : G) : Finset G := Finset.subset_to_finset (s:=g.support) (t:={a₂ ∈ g.support | a₁ * a₂ = a}) <| by
  exact Set.sep_subset (fun x => x ∈ g.support.val) fun x => ↑a₁ * x = a


lemma gsupport_mem (a₁ a : G) : a₂ ∈ gsupport_finset g a₁ a ↔ a₂ ∈ {a₂ ∈ g.support | a₁ * a₂ = a} := by
  unfold gsupport_finset ; unfold Finset.subset_to_finset
  rw [Set.Finite.mem_toFinset]

lemma gsupport_mem' (a₁ a : G) : a₂ ∈ gsupport_finset g a₁ a ↔ a₂ ∈ g.support ∧ a₁ * a₂ = a := by
  rw[gsupport_mem, Set.mem_setOf]

lemma gsupport_finset_is_subset (a₁ a : G) : (gsupport_finset g a₁ a) ⊆ g.support := by
  intro x hx ; rw [gsupport_mem'] at hx
  obtain ⟨_ , _⟩ := hx ; assumption

variable (a₁ a : G)

lemma mul_inner_sum_equiv : (∑ a₂ in g.support, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a =
    (∑ a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a := by
  have h : g.support \ (gsupport_finset g a₁ a) ∪ (gsupport_finset g a₁ a) = g.support := Finset.sdiff_union_of_subset (gsupport_finset_is_subset g a₁ a)
  rw[←h]
  rw [show (∑ a₂ in (g.support \ gsupport_finset g a₁ a ∪ gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) =
      (∑ a₂ in (g.support \ gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) +
      (∑ a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) by
    apply Finset.sum_union_disjoint_is_disjoint_sum
    exact Finset.sdiff_inter_self (gsupport_finset g a₁ a) g.support]
  rw [show (∑ a₂ in g.support \ gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) + ∑ a₂ in gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a =
      (∑ a₂ in g.support \ gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a + (∑ a₂ in gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a from rfl]
  suffices (∑ a₂ in g.support \ gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a = 0 from add_left_eq_self.mpr this
  rw [show (∑ a₂ in g.support \ gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a = ∑ a₂ in g.support \ gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) a from Finset.sum_apply' a]
  suffices ∀ a₂ ∈ g.support \ gsupport_finset g a₁ a, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) a = 0 from Finset.sum_eq_zero this
  intro a₂ ha₂ ; rw [Finset.mem_sdiff] at ha₂ ; obtain ⟨ha₂g, ha₂g'⟩ := ha₂
  unfold gsupport_finset at ha₂g' ; unfold Finset.subset_to_finset at ha₂g'
  simp only [Set.Finite.mem_toFinset, Finsupp.mem_support_iff, ne_eq, Set.mem_setOf_eq, not_and] at ha₂g'
  rw [Finsupp.mem_support_iff] at ha₂g
  rw [Finsupp.single_eq_of_ne (ha₂g' ha₂g)]

lemma sum_gsupport_is_sum_gsupport : (∑ a₁ in f.support, ∑ a₂ in g.support, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a = (∑ a₁ in f.support, (∑ a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂))) a := by
  rw [Finset.sum_apply',Finset.sum_apply']
  suffices ∀ a₁ ∈ f.support, (∑ a₂ in g.support, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a = (∑ a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂)) a from
    Finset.sum_congr rfl this
  exact fun a₁ _ => mul_inner_sum_equiv f g a₁ a

lemma of_sum_sum_is_sum_sum_of (α₁ : Finset G) (α₂ : G → Finset G) (f : G → G → MonoidAlgebra R G) (a : G) : (∑ a₁ in α₁, (∑ a₂ in α₂ a₁, f a₁ a₂)) a = ∑ a₁ in α₁, ∑ a₂ in α₂ a₁, f a₁ a₂ a := by
  rw [Finset.sum_apply'] ; conv => enter [1, 2, k] ; rw [Finset.sum_apply']

variable {f g} in
lemma single_mul_in_gsupport_is_gmul (ha₂ : a₂ ∈ gsupport_finset g a₁ a) : MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) a = MonoidAlgebra.single a (f a₁ * g (a₁⁻¹ * a)) a := by
  rw [gsupport_mem'] at ha₂
  obtain ⟨_, ha₂'⟩ := ha₂ ; rw [ha₂']
  rw [←ha₂'] ; group

lemma gsupport_gives_same_mul : (∑ a₁ in f.support, (∑ a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂))) a = (∑ a₁ in f.support, (∑ _a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single a (f a₁ * g (a₁⁻¹ * a)))) a := by
  rw [of_sum_sum_is_sum_sum_of,of_sum_sum_is_sum_sum_of]
  suffices ∀ a₁ ∈ f.support, (∑ a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) a) = (∑ _a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single a (f a₁ * g (a₁⁻¹ * a)) a) by
    exact Finset.sum_congr rfl this
  intro a₁ _
  suffices ∀ a₂ ∈ (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) a = MonoidAlgebra.single a (f a₁ * g (a₁⁻¹ * a)) a by
    exact Finset.sum_congr rfl this
  exact fun a₂ ha₂ => single_mul_in_gsupport_is_gmul a₁ a ha₂

lemma sum_of_singles_of_x_at_x_is_sum_of_coeficients (α₁: Finset G) (α₂ : G → Finset G) (f : G → G → R):
    (∑ a₁ in α₁, (∑ a₂ in α₂ a₁, MonoidAlgebra.single a (f a₁ a₂))) a = ∑ a₁ in α₁, ∑ a₂ in α₂ a₁, f a₁ a₂ := by
  rw [of_sum_sum_is_sum_sum_of]
  conv => enter [1, 2, a₁, 2, a₂] ; rw [Finsupp.single_eq_same]

lemma sum_of_singles_of_a_at_a_is_sum_of_scalar_of_coeficients : (∑ a₁ in f.support, (∑ _a₂ in (gsupport_finset g a₁ a), MonoidAlgebra.single a (f a₁ * g (a₁⁻¹ * a)))) a = ∑ a₁ in f.support, Finset.card (gsupport_finset g a₁ a) * (f a₁ * g (a₁⁻¹ * a)) := by
  rw [sum_of_singles_of_x_at_x_is_sum_of_coeficients]
  simp only [Finset.sum_const, nsmul_eq_mul]

lemma gsupport_finset_all_elements_same (x y : G): x ∈ gsupport_finset g a₁ a → y ∈ gsupport_finset g a₁ a → x = y := by
  intro hx hy ; rw [gsupport_mem'] at hx hy
  obtain ⟨_, hx'⟩ := hx ; obtain ⟨_, hy'⟩ := hy
  rwa [←hy', mul_right_inj] at hx'


lemma gsupport_finset_card_le_one : Finset.card (gsupport_finset g a₁ a) ≤ 1 := by
  rw [Finset.card_le_one_iff_subset_singleton]
  by_cases gsupport_finset g a₁ a = ∅
  · rw[h] ; simp only [Finset.subset_singleton_iff, true_or, exists_const]
  · have hg : Finset.Nonempty (gsupport_finset g a₁ a) := by exact Finset.nonempty_of_ne_empty h
    unfold Finset.Nonempty at hg ;
    obtain ⟨x, hx⟩ := hg ; use x
    intro y hy ; rw [Finset.mem_singleton]
    exact gsupport_finset_all_elements_same g a₁ a y x hy hx


lemma gsupport_finset_nonempty (h : a₁⁻¹ * a ∈ g.support) : Finset.Nonempty (gsupport_finset g a₁ a) := by
  unfold Finset.Nonempty ; use a₁⁻¹ * a ; rw [gsupport_mem']
  constructor ; exact h ; group

lemma gsupport_finset_card_eq_one (h : a₁⁻¹ * a ∈ g.support) : Finset.card (gsupport_finset g a₁ a) = 1 := by
  rw [Nat.le_antisymm_iff] ; constructor ; simp only [gsupport_finset_card_le_one]
  rw [Nat.one_le_iff_ne_zero] ; simp only [ne_eq, Finset.card_eq_zero]
  rw[←ne_eq, ←Finset.nonempty_iff_ne_empty]
  exact gsupport_finset_nonempty g a₁ a h

lemma mul_inner_sum_unecessary: Finset.card (gsupport_finset g a₁ a) * (f a₁ * g (a₁⁻¹ * a)) = f a₁ * g (a₁⁻¹ * a) := by
  by_cases a₁⁻¹ * a ∈ g.support
  · rw [show Finset.card (gsupport_finset g a₁ a) = 1 from gsupport_finset_card_eq_one g a₁ a h]
    simp only [Nat.cast_one, one_mul]
  · rw [Finsupp.not_mem_support_iff] at h
    rw [h] ; simp only [mul_zero]

end mul_def'

theorem mul_def'.at (a : G) : (f * g) a = ∑ a₁ in f.support, f a₁ * g (a₁⁻¹ * a) := by
  rw [mul_def'', mul_def'.sum_gsupport_is_sum_gsupport, mul_def'.gsupport_gives_same_mul, mul_def'.sum_of_singles_of_a_at_a_is_sum_of_scalar_of_coeficients]
  conv => enter [1, 2, a₁] ; rw [mul_def'.mul_inner_sum_unecessary]

lemma mul_def'.toFun : ↑(f * g) = fun a => ∑ a₁ in f.support, f a₁ * g (a₁⁻¹ * a) := by
  ext ; exact mul_def'.at _ _ _

lemma mul_support_mem₁ : x ∈ (f * g).support ↔ x ∈ {x | ∑ a in f.support, f a * g (a⁻¹ * x) ≠ 0} := by
  simp only [Finsupp.mem_support_iff, Set.mem_setOf_eq, mul_def'.at]

lemma mul_support_mem₂ : x ∈ (f*g).support → ∃ a ∈ f.support, g (a⁻¹ * x) ≠ 0 := by
  rw[mul_support_mem₁]
  intro hx ; rw [Set.mem_setOf] at hx
  apply Finset.exists_ne_zero_of_sum_ne_zero at hx
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := hx ; use a
  constructor ; exact ha₁
  apply right_ne_zero_of_mul at ha₂
  assumption

lemma mul_support_mem₃ : x ∈ (f*g).support → ∃ a ∈ f.support, a⁻¹ * x ∈ g.support := by
  intro hx ; apply mul_support_mem₂ at hx
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := hx
  use a ; constructor ; exact ha₁
  rwa [Finsupp.mem_support_iff]

lemma mul_support_def'' : (f * g).support = {x | ∑ a in f.support, f a * g (a⁻¹ * x) ≠ 0} := by
  ext x ; simp only [Finset.mem_coe, Set.mem_setOf_eq, mul_support_mem₁]

noncomputable def mul_support_def : Finset G :=
  Finset.subset_to_finset (A:=G) (s:=(f*g).support) (t:={x | ∑ a in f.support, f a * g (a⁻¹ * x) ≠ 0}) <| by
    rw [mul_support_def'']

lemma mul_support_def' : mul_support_def f g = (f * g).support := by
  unfold mul_support_def ; unfold Finset.subset_to_finset
  ext x ; rw [Set.Finite.mem_toFinset]
  rw[mul_support_mem₁]

theorem mul_def' : f * g = ∑ a₁ in mul_support_def f g, MonoidAlgebra.single a₁ (∑ a in f.support, f a * g (a⁻¹ * a₁)) := by
  unfold MonoidAlgebra
  ext a₁
  rw [mul_def'.at]
  rw [@Finset.sum_apply']
  conv => rhs ; rw [Finset.sum_in_eq_sum_type]
  let r : G → R := fun x => by
    by_cases x = a₁
    · exact ∑ a in f.support, f a * g (a⁻¹ * a₁)
    · exact 0
  have (x : mul_support_def f g) : r ↑x = (single (↑x) (∑ a in f.support, f a * g (a⁻¹ * x))) a₁ := by
    dsimp only [dite_eq_ite]
    by_cases ↑x = a₁
    · simp only [Finsupp.single_eq_same, h, ite_true]
    · rw [@Finsupp.single_apply]
      simp only [h, ite_false]
  conv => enter [2,2,x] ; rw [←this x]
  conv => rhs ; rw [← Finset.sum_in_eq_sum_type]
  dsimp only [dite_eq_ite]
  rw [@Finset.sum_ite_eq']
  by_cases a₁ ∈ mul_support_def f g
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    rw [mul_support_def', mul_support_mem₁] at h
    simp only [ne_eq, Set.mem_setOf_eq, not_not] at h
    assumption



end MonoidAlgebra

namespace AugmentationIdeal'.AugmentationMap

variable [Group G] [Ring R] [NoZeroDivisors R]
variable (f g : MonoidAlgebra R G)

namespace mulHom

lemma support_sdiff_equiv₁ (y : G): (fun x => y * x) '' ↑(g.support \ Set.toFinset ((fun x => y⁻¹ * x) '' ↑(f * g).support)) =
    ((fun x => y * x) '' ↑g.support) \ ((fun x => y * x) '' ↑(Set.toFinset ((fun x => y⁻¹ * x) '' ↑(f * g).support.toSet))) := by
  rw [@Finset.coe_sdiff, Finset.image_sdiff_is_sdiff_image]
  intro _ _ h ; rwa [mul_left_cancel_iff] at h

lemma support_sdiff_equiv₂ (y : G) : Set.toFinset ((fun x₁ => y * x₁) '' ↑(g.support \ Set.toFinset ((fun x_1 => y⁻¹ * x_1) '' ↑(f * g).support))) =
    Set.toFinset (((fun x => y * x) '' g.support) \ ((fun x => y * x) '' Set.toFinset ((fun x => y⁻¹ * x) '' (f * g).support.toSet))) := by
  ext a ; rw[Set.mem_toFinset, Set.mem_toFinset]
  rw[support_sdiff_equiv₁]

lemma support_sdiff_equiv₃ (y : G) : Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support \ (fun x_1 => x * x_1) '' ↑(Set.toFinset ((fun x_1 => x⁻¹ * x_1) '' ↑(f * g).support))) =
    Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support \ (f * g).support.toSet) := by
  suffices (fun x_1 => x * x_1) '' ↑(Set.toFinset ((fun x_1 => x⁻¹ * x_1) '' ↑(f * g).support)) = (f * g).support.toSet by {
    ext a ; rw [Set.mem_toFinset, Set.mem_toFinset, this]
  }
  ext a
  rw[Set.coe_toFinset, ←Set.image_comp]
  simp only [Function.comp_apply, mul_inv_cancel_left, Set.image_id', Finset.mem_coe,
    Finsupp.mem_support_iff, ne_eq]

noncomputable instance : Fintype (⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' g.support.toSet) := by
  exact Fintype.ofFinite ↑(⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' g.support.toSet)


lemma proof_1.proof_1 (x₂' : G) (hx₂' : x₂' ∈ f.support): Set.toFinset (⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \ (f * g).support =
    Set.toFinset (((⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \ (fun x_1 => x₂' * x_1) '' ↑g.support) ∪ (fun x_1 => x₂' * x_1) '' ↑g.support) \ (f * g).support := by
  ext a
  simp only [Finset.mem_sdiff, Set.mem_toFinset]
  constructor
  · rintro ⟨haunion, hasupport⟩
    constructor
    · rw [Set.mem_union]
      by_cases a ∈ (fun x_1 => x₂' * x_1) '' g.support.toSet
      · exact Or.inr h
      · exact Or.inl <| by
          rw [Set.mem_diff]
          constructor ; assumption'
    · exact hasupport
  · rintro ⟨haunion, hasupport⟩
    rw [Set.mem_union, Set.mem_diff] at haunion
    constructor
    · obtain ⟨ha₁, _⟩ | ha₃ := haunion
      · assumption
      · exact Set.mem_biUnion hx₂' ha₃
    · exact hasupport

lemma proof_1.proof_2 (x : G) (h : x ∈ f.support): ∑ x_1 in Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support \ (f * g).support), f x * g (x⁻¹ * x_1) =
    ∑ x_1 in Set.toFinset (⋃ x₂ ∈ f.support, (fun x' => x₂ * x') '' ↑g.support) \ (f * g).support, f x * g (x⁻¹ * x_1) := by
  rw[proof_1 f g x h]
  rw [ show Set.toFinset
        ((⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \ (fun x_1 => x * x_1) '' ↑g.support ∪
          (fun x_1 => x * x_1) '' ↑g.support) = Set.toFinset (((⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \ (fun x_1 => x * x_1) '' ↑g.support)) ∪ Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support) by
    exact
      Set.toFinset_union
        ((⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \
          (fun x_1 => x * x_1) '' ↑g.support)
        ((fun x_1 => x * x_1) '' ↑g.support)
  ]
  rw[Finset.sum_union_sdiff_is_sum_sdiff]
  simp only [Set.image_mul_left, Set.toFinset_diff, Finset.toFinset_coe,
    Finset.image_mul_left, Finsupp.mem_support_iff, ne_eq, Finset.sdiff_inter_self,
    Finset.empty_sdiff, Finset.sum_empty, sub_zero, self_eq_add_left]
  suffices ∀ y ∈ (Set.toFinset (⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \
        Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support)) \
      (f * g).support, f x * g (x⁻¹ * y) = 0 from Finset.sum_eq_zero this
  intro y hy
  simp only [Finsupp.mem_support_iff, ne_eq, Set.image_mul_left, Set.toFinset_image,
    Finset.toFinset_coe, Finset.image_mul_left, Finset.mem_sdiff, Set.mem_toFinset, Set.mem_iUnion,
    Set.mem_preimage, Finset.mem_coe, exists_prop, Finset.mem_preimage, not_not] at hy
  obtain ⟨⟨_, h₁⟩, _⟩ := hy
  exact mul_eq_zero_of_right (f x) h₁


lemma proof_1 : ∑ y in f.support, f y * ∑ b in Set.toFinset ((fun x => y⁻¹ * x) '' (f * g).support), g b =
    ∑ y in f.support, f y * ∑ b in Set.toFinset ((fun x => y⁻¹ * x) '' (f * g).support) ∪ g.support, g b := by
  conv => enter [2, 2, y, 2] ; rw [Finset.sum_union_is_left_and_sdiff]
  conv => enter [2, 2, y] ; rw [left_distrib]
  rw[Finset.sum_add_distrib]
  suffices ∑ x in f.support, f x * ∑ y in g.support \ Set.toFinset ((fun x_1 => x⁻¹ * x_1) '' (f * g).support), g y = 0 by {
    rw [this] ; simp only [Set.image_mul_left, inv_inv, Set.toFinset_image, Finset.toFinset_coe,
      Finset.image_mul_left, add_zero]
  }
  conv => enter [1, 2, x]
  let φ : G → G → G := fun x x₁ => x * x₁
  have hφ : ∀ x x₁ : G, x⁻¹ * φ x x₁ = x₁ := by
    intro x x₁ ; dsimp ; group
  have hφ' (x : G) : ∀ x₁ x₂ : G, φ x x₁ = φ x x₂ → x₁ = x₂ := by
    intro x₁ x₂ h ; dsimp at h ; rwa [mul_left_cancel_iff] at h
  conv => enter [1, 2, x, 2, 2, y] ; rw [←hφ x y]
  conv =>
    enter [1, 2, x, 2]
    rw [@Finset.sum_of_funct_is_sum_over_image'₂ _ _ _ _ (φ x) (fun x' => x⁻¹ * x') (g.support \ Set.toFinset ((fun x_1 => x⁻¹ * x_1) '' ↑(f * g).support)) g (hφ' x)]
  conv =>
    enter [1, 2, x, 2, 1]
    dsimp ; rw [support_sdiff_equiv₂, support_sdiff_equiv₃ f g x]
  conv => enter [1, 2, x] ; rw[Finset.mul_sum]
  conv => enter [1, 2, x, 2, x]
  suffices ∀ x : G, ∑ x_1 in Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support \ ↑(f * g).support), f x * g (x⁻¹ * x_1) =
      ∑ x_1 in Set.toFinset ↑(⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' g.support.toSet) \ ↑(f * g).support, f x * g (x⁻¹ * x_1) by {
    conv => enter [1, 2, x] ; rw[this]
    rw [Finset.sum_comm]
    conv => enter [1, 2, y] ; rw[← MonoidAlgebra.mul_def'.at]
    suffices ∀ y ∈ Set.toFinset (⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \ (f * g).support, (f * g) y = 0 from Finset.sum_eq_zero this
    intro y hy ; rw [Finset.mem_sdiff] at hy
    obtain ⟨_, hy'⟩ := hy ; simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hy'
    assumption
  }
  intro x
  by_cases x ∈ f.support ; rwa [proof_1.proof_2]
  rw [Finsupp.not_mem_support_iff] at h ; rw[h]
  simp only [Set.image_mul_left, Set.toFinset_diff, Set.toFinset_image, Finset.toFinset_coe,
    Finset.image_mul_left, zero_mul, Finset.sum_const_zero, Finsupp.mem_support_iff, ne_eq]


lemma proof_2 : ∑ a in f.support, f a * ∑ x in g.support, g x =
    ∑ y in f.support, f y * ∑ b in Set.toFinset ((fun x => y⁻¹ * x) '' (f * g).support) ∪ g.support, g b := by
  conv => enter [2, 2, y, 2, 1] ; rw[Finset.union_comm]
  conv => enter [2, 2, y, 2] ; rw[Finset.sum_union_is_left_and_sdiff]
  suffices ∀ y : G, ∑ x in Set.toFinset ((fun x => y⁻¹ * x) '' ↑(f * g).support) \ g.support, g x = 0 by {
    conv => enter [2, 2, y, 2, 2] ; rw [this]
    rw [add_zero]
  }
  intro y
  suffices ∀ x ∈ Set.toFinset ((fun x => y⁻¹ * x) '' (f * g).support) \ g.support, g x = 0 from
    Finset.sum_eq_zero this
  intro _ hx
  simp only [Set.image_mul_left, inv_inv, Set.toFinset_image, Finset.toFinset_coe,
    Finset.image_mul_left, Finset.mem_sdiff, Finset.mem_preimage, Finsupp.mem_support_iff, ne_eq,
    not_not] at hx
  obtain ⟨_, hx'⟩ := hx ; assumption

end mulHom

theorem mulHom (f g : MonoidAlgebra R G): ∑ a in (f * g).support, (f * g) a = (∑ a in f.support, f a) * (∑ a in g.support, g a) := by
  conv => enter [1, 2, a] ; rw [MonoidAlgebra.mul_def'.at]
  rw[Finset.sum_comm]
  conv => enter [1, 2, y] ; rw[Finset.mul_sum.symm]
  rw[Finset.sum_mul_sum_is_sum_sum_mul]
  conv =>
    enter [2, 2, a]
    rw[←Finset.mul_sum]
  have hφ (y : G) : ∀ x₁ ∈ (f * g).support, ∀ x₂ ∈ (f * g).support, y⁻¹ * x₁ = y⁻¹ * x₂ → x₁ = x₂ := by
    intro x₁ _ x₂ _ h ; rwa [mul_left_cancel_iff] at h
  conv =>
    enter [1, 2, y, 2]
    rw [Finset.sum_of_funct_is_sum_over_image g (hφ y)]
  rw[mulHom.proof_1, mulHom.proof_2]

end AugmentationMap

variable [Group G] [CommRing R] [NoZeroDivisors R]

-- A computable version of `AugmentationIdeal.AugmenationMap`
def AugmentationMap : (MonoidAlgebra R G) →+* R where
  toFun := by intro f ; exact ∑ a in ↑f.support, (f : G →₀ R) a
  map_mul' _ _ := AugmentationMap.mulHom _ _
  map_zero' := by dsimp
  map_one' := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.single]
    by_cases (1:R)=0
    · simp only [h, Finsupp.single_zero, Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply,
      Finset.sum_const_zero]
    · rw [(Finsupp.support_single_ne_zero 1)]
      · simp only [ne_eq, Finset.sum_singleton, Finsupp.single_eq_same]
      · rw [@ne_eq] ; exact h
  map_add' := by
    dsimp ; intro (f : G →₀ R) (g : G →₀ R) ; rw[Finsupp.sum_coefficents_is_add_hom]

@[simp]
lemma AugmentationMap.fun_def (f : MonoidAlgebra R G) :
    AugmentationMap f = AugmentationIdeal.AugmentationMap f := by
  simp [AugmentationMap, AugmentationIdeal.AugmentationMap.fun_def']

@[simp]
lemma AugmentationMap.eq :
    AugmentationMap (R:=R) (G:=G) = AugmentationIdeal.AugmentationMap := by
  ext <;> simp

end AugmentationIdeal'
