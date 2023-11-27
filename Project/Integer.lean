import Project.Basic

variable {G : Type*} [CommGroup G] [DecidableEq G]

namespace AugmentationIdeal.Integers

variable (G)

def integerAugmentationIdeal : Ideal (MonoidAlgebra ℤ G) := AugmentationIdeal ℤ G

scoped notation "Δℤ" G => integerAugmentationIdeal G

end AugmentationIdeal.Integers
