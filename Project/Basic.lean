import Mathlib
import Project.AugmentationMap


variable (R G : Type*) [CommGroup G] [CommRing R] [NoZeroDivisors R] [DecidableEq G]

def AugmentationIdeal : Ideal (MonoidAlgebra R G) := RingHom.ker (AugmentationIdeal.AugmentationMap.ε R G)

namespace AugmentationIdeal

scoped notation "Δ" R "," G => AugmentationIdeal R G

noncomputable section Quotients

variable (n r : ℕ)

def quotOfPowers : Ideal (MonoidAlgebra R G) :=
  ((Δ R,G) ^ n) / ((Δ R,G) ^ (n + r))

def quotNatOverId : Ideal (MonoidAlgebra R G) := quotOfPowers R G n 1

def quotIdOverNat : Ideal (MonoidAlgebra R G) := quotOfPowers R G 1 n

end Quotients

end AugmentationIdeal
