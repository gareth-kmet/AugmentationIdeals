import Mathlib -- #TODO Reduce


/-!
  Defines the augmentation map, this is the homomorphism that sends
  a MonoidAlgebra (a Finsupp) to the sum of the image of the function.
  This function will be denoted by `AugmentationIdeal.AugmentationMap.ε`

  Also contained below its different definitions of the multiplication
  of two MonoidAlgebra, including the definition that
  `(f*g) a = ∑ h in G, f h * g (h⁻¹ * a)`

  The assumptions are made that the MonoidAlgebra uses a abelian group,
  `G` and a communative nonzerodivisor ring `R`.

  #TODO change this to be a group and a ring


  Author : Gareth Kmet 2023
-/

open BigOperators


variable {R G : Type*} [DecidableEq G]

namespace AugmentationIdeal

variable [CommGroup G] [CommRing R] [NoZeroDivisors R]

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

namespace Finset
/-!
  Some lemmas about sums of finsets
-/

variable {f g : G → R}

section combinations
/-!
  Some lemmas about Finsets and their unions/intersections/differences
-/

lemma set_is_union_of_set_and_sdiff (I J : Finset G) : I = (I ∩ J) ∪ (I \ J) := by
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

lemma image_sdiff_is_sdiff_image (I J : Finset G) (γ : G → G) (hγ : ∀ g₁ g₂ : G, γ g₁ = γ g₂ → g₁ = g₂) : γ '' (I \ J) = (γ '' I) \ (γ '' J) := by
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


lemma union_decomp (I J : Finset G) : I ∩ J ∪ I \ J ∪ J \ I = I ∪ J := by
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

lemma empty_decomp (I J : Finset G) : (I ∩ J ∪ I \ J) ∩ (J \ I) = ∅ := by
  ext x ; simp only [mem_sdiff, mem_union, mem_inter]
  constructor
  · rintro ⟨⟨hI, _⟩ | ⟨_, hnJ⟩, ⟨hJ, hnI⟩⟩
    · exact (hnI hI).elim
    · exact (hnJ hJ).elim
  · intro hx ; exfalso
    exact (List.mem_nil_iff x).mp hx


end combinations

section sums
/-!
  Some Lemmas about the sums of finsets
-/
variable [AddCommGroup R] --#TODO reduce this assumption

lemma sum_union_disjoint_is_disjoint_sum (I J : Finset G) (hij : I ∩ J = ∅) : (∑ x in (I ∪ J), f x) = (∑ x in I, f x) + (∑ x in J, f x) := by
  rw [← @Finset.sum_union_inter, hij]
  exact self_eq_add_right.mpr rfl

lemma sum_union_is_left_and_sdiff (I J : Finset G) : (∑ x in (I ∪ J), f x) = (∑ x in I, f x) + (∑ x in J \ I, f x) := by
  rw [← Finset.sum_union]
  · suffices I ∪ J = I ∪ J \ I by rw[this]
    rw [union_sdiff_self_eq_union]
  · exact disjoint_sdiff

lemma sum_union_is_right_and_sdiff (I J : Finset G) : (∑ x in (I ∪ J), f x) = (∑ x in I \ J, f x) + (∑ x in J, f x) := by
  rw [← Finset.sum_union]
  · suffices I ∪ J = I \ J ∪ J by rw[this]
    rw [sdiff_union_self_eq_union]
  · exact sdiff_disjoint

lemma sum_union_sdiff_is_sum_sdiff (I J K : Finset G) : ∑ x in (I ∪ J) \ K, f x = (∑ x in I \ K, f x) + (∑ x in J \ K, f x) - (∑ x in (I ∩ J) \ K, f x) := by
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
  exact self_eq_add_right.mpr rfl

lemma sum_of_funct_is_sum_over_image (β : Finset G) (γ : G → R) (φ : G → G) (h : ∀ x₁ ∈ β, ∀ x₂ ∈ β, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a in β, γ (φ a) = ∑ b in (φ '' β).toFinset, γ b := by
  simp only [Set.toFinset_image, Finset.toFinset_coe] ; rwa [Finset.sum_image]

lemma sum_of_funct_is_sum_over_image' (β : Finset G) (γ : G → R) (φ ψ : G → G) (h : ∀ x₁ ∈ β, ∀ x₂ ∈ β, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a in β, γ (ψ (φ a)) = ∑ b in (φ '' β).toFinset, γ (ψ b) := by
  simp only [Set.toFinset_image, Finset.toFinset_coe] ; rwa [Finset.sum_image]

lemma sum_of_funct_is_sum_over_image'₂ (β : Finset G) (γ : G → R) (φ ψ : G → G) (h : ∀ x₁ x₂ : G, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a in β, γ (ψ (φ a)) = ∑ b in (φ '' β).toFinset, γ (ψ b) := by
  simp only [Set.toFinset_image, Finset.toFinset_coe] ; rw [Finset.sum_image]
  intro x _ y _ hxy
  apply h ; assumption

lemma sum_of_funct_is_sum_over_image'' (β : Finset G) (γ : G → R) (φ : G → G) (h : ∀ x₁ ∈ β, ∀ x₂ ∈ β, φ x₁ = φ x₂ → x₁ = x₂) : ∑ a : β, γ (φ a) = ∑ b : (φ '' β).toFinset, γ b := by
  simp only [univ_eq_attach,@sum_attach, Set.toFinset_image, toFinset_coe]
  rw [sum_image, ← @sum_coe_sort_eq_attach]
  refine (sum_subtype β ?_ fun a => γ (φ a)).symm
  simp only [implies_true]
  assumption

lemma sum_in_eq_sum_type {A : Type*} (α : Finset A) (f : A → R) : ∑ a in α, f a = ∑ a : α, f ↑a := by
  rw [← Finset.sum_attach]
  simp

lemma sum_of_funct_is_sum_over_image_equiv_nat (β : Finset G) (γ : G → R) (φ : ℕ → G) (ψ : G → ℕ)
    (h : ∀ x ∈ β, φ (ψ x) = x) (inj : ∀ x ∈ β, ∀ y ∈ β, ψ x = ψ y → x = y) :
    ∑ a in β, γ a = ∑ i in (ψ '' β).toFinset, γ (φ i) := by
  simp ; rw [sum_image]
  conv => rhs ; rw [sum_in_eq_sum_type]
  conv => enter [2, 2, x] ; rw [h ↑x x.property]
  rwa [← sum_in_eq_sum_type]

lemma sum_of_funct_is_sum_over_image_equiv_nat' (β : Finset G) (γ : G → R) (φ : ℕ → G) (ψ : G → ℕ)
    (h : ∀ x ∈ β, φ (ψ x) = x) (inj : ∀ x ∈ β, ∀ y ∈ β, ψ x = ψ y → x = y) :
    ∑ a : β, γ a = ∑ i : (ψ '' β).toFinset, γ (φ i) := by
  rw [← sum_in_eq_sum_type]
  conv => rhs ; rw [← sum_in_eq_sum_type (ψ '' β).toFinset (fun a => γ (φ a))]
  rw [sum_of_funct_is_sum_over_image_equiv_nat]
  assumption'

lemma sum_equiv_sum_indexed_by_card (β : Finset G) (γ : G → R) :
    ∑ a : β, γ a = ∑ i : Fin β.card, γ (β.equivFin.invFun i) := by
  by_cases hcard : β.card = 0
  · rw [@card_eq_zero] at hcard ; rw [hcard]
    simp
  · let φ : ℕ → G := fun i => by
      by_cases i < β.card
      · exact ↑(β.equivFin.invFun ⟨i,h⟩)
      · exact ↑(β.equivFin.invFun ⟨0, Nat.pos_of_ne_zero hcard⟩)
    let ψ : G → ℕ := fun g => by
      by_cases g ∈ β
      · exact ↑(β.equivFin.toFun ⟨g,h⟩)
      · exact 0
    have hψ : ∀ b : β, ↑(β.equivFin.toFun b) = ψ ↑b := by simp
    have hh : ∀ x ∈ β, φ (ψ x) = x := by
      intro _ h' ; simp [dif_pos h']
    have inj : ∀ x ∈ β, ∀ y ∈ β, ψ x = ψ y → x = y := by
      intro x hx y hy
      rw [← hψ ⟨x,hx⟩, ← hψ ⟨y,hy⟩]
      have h : Function.Injective β.equivFin.toFun := by
        rw [@Equiv.toFun_as_coe]
        exact Equiv.injective (equivFin β)
      intro heq
      unfold Function.Injective at h
      have h' : (⟨x,hx⟩ : β) = ⟨y,hy⟩ → x = y := by simp
      apply h' ; apply h
      exact Fin.ext heq
    rw [sum_of_funct_is_sum_over_image_equiv_nat' β γ φ ψ hh inj]
    rw [← sum_in_eq_sum_type (Set.toFinset (ψ '' β)) (fun x => γ (φ x))]
    rw [sum_fin_eq_sum_range]
    have hf : Set.toFinset (ψ '' ↑β) = range (card β) := by
      ext i
      constructor
      · intro hi
        rw [@Set.mem_toFinset] at hi
        obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := hi
        dsimp at hx₂
        rw [@mem_coe] at hx₁
        rw [dif_pos hx₁] at hx₂
        simp
        have hi' : ∃ j : Fin β.card, ↑j = i := by
          use (β.equivFin ⟨x,hx₁⟩)
        obtain ⟨⟨j,hj₁⟩, hj₂⟩ := hi'
        simp at hj₂
        rwa [← hj₂]
      · intro hi
        rw [Set.mem_toFinset]
        rw [@Set.mem_image]
        dsimp
        simp at hi
        use β.equivFin.invFun ⟨i, hi⟩
        simp
    rw [hf, sum_in_eq_sum_type]
    conv => rhs ; rw [sum_in_eq_sum_type]
    congr ; ext j
    obtain ⟨i, hi⟩ := j
    simp at hi
    simp [dif_pos hi]

lemma sum_equiv_sum_indexed_by_card' (β : Finset G) (γ : G → R) :
    ∑ a in β, γ a = ∑ i : Fin β.card, γ (β.equivFin.invFun i) := by
  rw [sum_in_eq_sum_type]
  exact sum_equiv_sum_indexed_by_card β γ


variable [CommRing R]

lemma sum_mul_sum_is_sum_sum_mul (α β : Finset G) (φ ψ : G → R) : (∑ a in α, ψ a) * (∑ b in β, φ b) = ∑ a in α, ∑ b in β, ψ a * φ b := by
  conv => enter [2, 2, a] ; rw[Finset.mul_sum.symm , mul_comm]
  conv => rhs ; rw[←Finset.mul_sum]
  rw[mul_comm]

end sums

section subsets

noncomputable def subset_to_finset {α : Type*} {s : Finset α} {t : Set α} (ht : t ⊆ s) : Finset α := Set.Finite.toFinset <| Set.Finite.subset (s.finite_toSet) ht

end subsets

end Finset

namespace Finsupp

/-!
  Some lemmas about sums on finsupps
-/
variable [CommGroup G] [CommRing R] -- #TODO reduce
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
  simp [Finset.union_sum_decomp, outside_supp_mul_is_zero, mul_outside_supp_is_zero, add_zero]

end Finsupp

namespace AugmentationIdeal'.AugmentationMap

/-!
  Some Lemmas about multiplication within MonoidAlgebras
-/

variable [CommGroup G] [CommRing R] [NoZeroDivisors R]-- #TODO reduce
variable (f g : MonoidAlgebra R G)

lemma mul_def'' : f * g = ∑ a₁ in f.support, ∑ a₂ in g.support, MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) := by
  rw[MonoidAlgebra.mul_def] ; unfold Finsupp.sum
  dsimp only

def mul_g' (a : G) : MonoidAlgebra R G where -- #TODO remove (used in one two lemmas as a place holder)
  support := ((fun x => a * x⁻¹) '' g.support).toFinset
  toFun u := g (u⁻¹ * a)
  mem_support_toFun := by
    intro u ; simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.mem_image,
      Finsupp.mem_support_iff, ne_eq]
    constructor
    · rintro ⟨x, ⟨hx₁, hx₂⟩⟩
      replace hx₂ : x = u⁻¹ * a := by rw [←hx₂] ; group
      rw [←hx₂] ; exact hx₁
    · intro hu ; use u⁻¹ * a
      constructor ; exact hu ; group

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

noncomputable section calculations

def gsupport_finset (a₁ a : G) : Finset G := Finset.subset_to_finset (s:=g.support) (t:={a₂ ∈ g.support | a₁ * a₂ = a}) <| by
  exact Set.sep_subset (fun x => x ∈ g.support.val) fun x => ↑a₁ * x = a

@[simp]
lemma gsupport_mem (a₁ a : G) : a₂ ∈ gsupport_finset g a₁ a ↔ a₂ ∈ {a₂ ∈ g.support | a₁ * a₂ = a} := by
  unfold gsupport_finset ; unfold Finset.subset_to_finset
  rw [Set.Finite.mem_toFinset]

@[simp]
lemma gsupport_mem' (a₁ a : G) : a₂ ∈ gsupport_finset g a₁ a ↔ a₂ ∈ g.support ∧ a₁ * a₂ = a := by
  rw[gsupport_mem, Set.mem_setOf]


@[simp]
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
  suffices ∀ a₂ ∈ (gsupport_finset g a₁ a), MonoidAlgebra.single (a₁ * a₂) (f a₁ * g a₂) a = MonoidAlgebra.single a (f a₁ * mul_g' g a a₁) a by
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
  · rw [show Finset.card (gsupport_finset g a₁ a) = 1 from gsupport_finset_card_eq_one g a₁ a h] ; group
  · rw [Finsupp.not_mem_support_iff] at h
    rw [h] ; group

/-
  The main definition of multiplication for the ring group
-/
theorem mul_def' : (f * g) a = ∑ a₁ in f.support, f a₁ * g (a₁⁻¹ * a) := by
  rw [mul_def'', sum_gsupport_is_sum_gsupport, gsupport_gives_same_mul, sum_of_singles_of_a_at_a_is_sum_of_scalar_of_coeficients]
  conv => enter [1, 2, a₁] ; rw [mul_inner_sum_unecessary]

lemma mul_def''' : ↑(f * g) = fun a => ∑ a₁ in f.support, f a₁ * g (a₁⁻¹ * a) := by
  ext ; exact mul_def' _ _ _

lemma mul_support_mem₁ : x ∈ (f * g).support ↔ x ∈ {x | ∑ a in f.support, f a * g (a⁻¹ * x) ≠ 0} := by
  simp only [Finsupp.mem_support_iff, Set.mem_setOf_eq, mul_def']

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

def mul_support_def : Finset G :=
  Finset.subset_to_finset (α:=G) (s:=(f*g).support) (t:={x | ∑ a in f.support, f a * g (a⁻¹ * x) ≠ 0}) <| by
    rw [mul_support_def'']

lemma mul_support_def' : mul_support_def f g = (f * g).support := by
  unfold mul_support_def ; unfold Finset.subset_to_finset
  ext x ; rw [Set.Finite.mem_toFinset]
  rw[mul_support_mem₁]


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

instance max_gsupport_finset : Fintype (⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' g.support.toSet) := by
  exact Fintype.ofFinite ↑(⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' g.support.toSet)

lemma max_gsupport_equiv (x₂' : G) (hx₂' : x₂' ∈ f.support): Set.toFinset (⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \ (f * g).support =
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

lemma sum_is_equal_with_max_gsupport_finset (x : G) (h : x ∈ f.support): ∑ x_1 in Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support \ (f * g).support), f x * g (x⁻¹ * x_1) =
    ∑ x_1 in Set.toFinset (⋃ x₂ ∈ f.support, (fun x' => x₂ * x') '' ↑g.support) \ (f * g).support, f x * g (x⁻¹ * x_1) := by
  rw[max_gsupport_equiv f g x h]
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


lemma finset_is_finset_union_support : ∑ y in f.support, f y * ∑ b in Set.toFinset ((fun x => y⁻¹ * x) '' (f * g).support), g b =
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
    rw [Finset.sum_of_funct_is_sum_over_image'₂ (g.support \ Set.toFinset ((fun x_1 => x⁻¹ * x_1) '' ↑(f * g).support)) g (φ x) (fun x' => x⁻¹ * x') (hφ' x)]
  conv =>
    enter [1, 2, x, 2, 1]
    dsimp ; rw [support_sdiff_equiv₂, support_sdiff_equiv₃ f g x]
  conv => enter [1, 2, x] ; rw[mul_comm, Finset.sum_mul]
  conv => enter [1, 2, x, 2, x] ; rw[mul_comm]
  suffices ∀ x : G, ∑ x_1 in Set.toFinset ((fun x_1 => x * x_1) '' ↑g.support \ ↑(f * g).support), f x * g (x⁻¹ * x_1) =
      ∑ x_1 in Set.toFinset ↑(⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' g.support.toSet) \ ↑(f * g).support, f x * g (x⁻¹ * x_1) by {
    conv => enter [1, 2, x] ; rw[this]
    rw [Finset.sum_comm]
    conv => enter [1, 2, y] ; rw[←mul_def']
    suffices ∀ y ∈ Set.toFinset (⋃ x₂ ∈ f.support, (fun x_1 => x₂ * x_1) '' ↑g.support) \ (f * g).support, (f * g) y = 0 from Finset.sum_eq_zero this
    intro y hy ; rw [Finset.mem_sdiff] at hy
    obtain ⟨_, hy'⟩ := hy ; simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hy'
    assumption
  }
  intro x
  by_cases x ∈ f.support ; rwa [sum_is_equal_with_max_gsupport_finset]
  rw [Finsupp.not_mem_support_iff] at h ; rw[h]
  simp only [Set.image_mul_left, Set.toFinset_diff, Set.toFinset_image, Finset.toFinset_coe,
    Finset.image_mul_left, zero_mul, Finset.sum_const_zero, Finsupp.mem_support_iff, ne_eq]


lemma support_is_finset_union_support : ∑ a in f.support, f a * ∑ x in g.support, g x =
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


theorem mul_coeffients_is_mul_hom (f g : MonoidAlgebra R G): ∑ a in (f * g).support, (f * g) a = (∑ a in f.support, f a) * (∑ a in g.support, g a) := by
  conv => enter [1, 2, a] ; rw [mul_def']
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
    rw [Finset.sum_of_funct_is_sum_over_image (f * g).support g (fun x => y⁻¹ * x) (hφ y)]
  rw[finset_is_finset_union_support, support_is_finset_union_support]

end calculations

end AugmentationMap

variable [CommGroup G] [CommRing R] [NoZeroDivisors R]

-- A computable version of `AugmentationIdeal.AugmenationMap`
def AugmentationMap : (MonoidAlgebra R G) →+* R where
  toFun := by intro f ; exact ∑ a in ↑f.support, (f : G →₀ R) a
  map_mul' _ _ := AugmentationMap.mul_coeffients_is_mul_hom _ _
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
