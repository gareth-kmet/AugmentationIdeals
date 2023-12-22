import Project.Basic2

open BigOperators

variable {G : Type*} [CommGroup G] [DecidableEq G]

namespace AugmentationIdeal.Integers

variable (G)

noncomputable def integerAugmentationIdeal : Ideal (MonoidAlgebra ℤ G) := AugmentationIdeal ℤ G

def integerAugmentationIdeal' : Ideal (MonoidAlgebra ℤ G) := AugmentationIdeal' ℤ G

scoped notation "Δℤ" G => integerAugmentationIdeal G

variable {G}

namespace Quotients
open AugmentationIdeal.Quotients

variable (G)
theorem quot_generating_set (n : ℕ) : AddSubgroup.closure
    { QuotientAddGroup.mk (s:=nrpow_addsubgroup_of_npow ℤ G (n+1) 1)
      (⟨∏ i in Finset.attach (Finset.range (n + 1)),(MonoidAlgebra.single (f i) (1:ℤ) - 1), asd' ℤ G n f⟩ : ((Δ ℤ,G) ^ (n+1) : Ideal (MonoidAlgebra ℤ G)))
      | f : (Finset.range (n + 1)) → G} = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro x
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨m, ⟨f, ⟨r, rfl⟩⟩⟩ := npow_mem_linearcomb_prod_basis_subtype₂ ℤ G n x
  rw [AddSubgroup.mem_closure]
  intro K hK
  rw [QuotientAddGroup.mk_sum]
  apply AddSubgroup.sum_mem
  intro i hi
  rw [QuotientAddGroup.mk_zsmul]
  apply AddSubgroup.zsmul_mem
  rw [Set.subset_def] at hK
  apply hK
  simp only [Set.mem_setOf_eq, exists_apply_eq_apply]

instance finiteGenGroup (n : ℕ) [Fintype G] : AddGroup.FG (quotNatOverSucc ℤ G (n+1)) := AddGroup.fg_iff.mpr <| by
  use { QuotientAddGroup.mk (s:=nrpow_addsubgroup_of_npow ℤ G (n+1) 1)
      (⟨∏ i in Finset.attach (Finset.range (n + 1)),(MonoidAlgebra.single (f i) (1:ℤ) - 1), asd' ℤ G n f⟩ : ((Δ ℤ,G) ^ (n+1) : Ideal (MonoidAlgebra ℤ G)))
      | f : (Finset.range (n + 1)) → G}
  exact ⟨quot_generating_set G n, Set.toFinite ..⟩

instance quot_finite (n : ℕ) [Fintype G] : Finite (quotNatOverSucc ℤ G (n+1)) := by
  apply AddCommGroup.finite_of_fg_torsion
  letI : DecidableEq (MonoidAlgebra ℤ G) := Classical.decEq (MonoidAlgebra ℤ G)
  exact quot_torsion

end Quotients


theorem t : Additive G ≃+ quotNatOverSucc ℤ G 1 := by sorry
theorem t' (n : ℕ) : quotNatOverSucc ℤ G 1 ≃+ quotNatOverSucc ℤ G n := by sorry
theorem t'' (n : ℕ) : Additive G ≃+ quotNatOverSucc ℤ G n := t.trans (t' n)


def basis_hom (f : MonoidAlgebra ℤ G) : G := by
  exact ∏ a : ↑(f.support \ {1}), (Basis.support_to_basis_index f a) ^ (f a)

variable (G) in
def homit : (Δ ℤ,G) →+ Additive G where
  toFun := fun ⟨f, _⟩ => (∑ a : ↑(f.support \ {1}), f a • Additive.ofMul (Basis.support_to_basis_index f a : G))
  map_zero' := by simp only [Finsupp.support_zero, Finset.univ_eq_attach, Finsupp.coe_zero,
    Pi.zero_apply, ne_eq, Set.mem_setOf_eq, zero_smul, Finset.sum_const_zero]
  map_add' f g := by
    simp only [Finset.univ_eq_attach, ne_eq, Set.mem_setOf_eq]
    sorry

lemma ker : (homit G).ker = nrpow_addsubgroup_of_npow ℤ G 1 1 := by sorry

lemma sd (f g : Δℤ G) : basis_hom (f * g) = 1 := by
  unfold basis_hom
  unfold Basis.support_to_basis_index
  simp
  apply Finset.prod_eq_one
  intro x hx
  rw [AugmentationIdeal'.AugmentationMap.mul_def']

lemma ads (f g : MonoidAlgebra ℤ G) (hf : f ∈ Δℤ G) (hg : g ∈ Δℤ G) : (f * g) a =
    ∑ a : f.support ∪ g.support, f a * g a *

lemma kernal_sub (f : MonoidAlgebra ℤ G) (hf : f ∈ Δℤ G) : basis_hom ⟨f,hf⟩ = 1 → f ∈ (Δℤ G) ^ 2 := by
  sorry

lemma kernal_sup (f : MonoidAlgebra ℤ G) (hf : f ∈ Δℤ G) : f ∈ (Δℤ G) ^ 2 → basis_hom ⟨f,hf⟩ = 1:= by sorry

theorem kernal_def (f : MonoidAlgebra ℤ G) (hf : f ∈ Δℤ G) : basis_hom ⟨f,hf⟩ = 1 ↔ f ∈ (Δℤ G) ^ 2 :=
  ⟨kernal_sub f hf, kernal_sup f hf⟩


namespace Cyclic
set_option synthInstance.maxHeartbeats 0
theorem iso_aug_quot_qug_sq : G ≃ (quotOfPowers R G 1 1) := by sorry

variable (I J : Ideal R)
#check I ⧸ J

variable (H : Type*) [Group H]
example (f : G →* H) (hf : Function.Surjective f) : G⧸f.ker ≃* H := by
  exact QuotientGroup.quotientKerEquivOfSurjective f hf



lemma as : G ≃* H := by


end Cyclic
