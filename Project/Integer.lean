import Project.Basic2

open BigOperators

variable {G : Type*} [CommGroup G] [DecidableEq G]

namespace AugmentationIdeal.Integers

variable (G)

noncomputable def integerAugmentationIdeal : Ideal (MonoidAlgebra ℤ G) := AugmentationIdeal ℤ G

def integerAugmentationIdeal' : Ideal (MonoidAlgebra ℤ G) := AugmentationIdeal' ℤ G

scoped notation "Δℤ" G => integerAugmentationIdeal G

variable {G}

def basis_hom (f : MonoidAlgebra ℤ G) : G := by
  exact ∏ a : ↑(f.support \ {1}), (Basis.support_to_basis_index f a) ^ (f a)

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
