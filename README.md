# Augmentation Ideal

<p>
In this project we define the Augmentation Ideal of a communative group ring (i.e. where both the ring and group are communative). 
This is precisely the set of elements whose sum of coefficients is 0. We then prove some lemmas and theorems about this ideal, including
its basis as an R module. We then go on to look at the naturals powers of the augmentation ideal and prove theorems about membership and spanning
sets in both the cyclic and non-cycli case. Finally, we look at the quotient of a power of the augementation ideal by the succeding power and prove
theorems about its finiteness, its spanning sets and, in the case that the ring is integers and the group is finite, the finite generating set of
this quotient.
</p>

<p>
This project follows the thesis *Calculation of Augmentation Termainals* (1988) by John Kmet and covers the prerequisites and section 1 of chapter 1.
</p>

<p>
This project requires knowledge of group theory, ring theory, knowledge about group rings, some knowledge about submodules and some knowledge about
torsions of groups.
</p>

**NOTES**: This project assumes that the group is communative although the thesis does not, and in fact it is the focus of the thesis when the group is
not communative. This choice was made to make some of the proofs easier but also since `Pow (Ideal (MonoidAlgebra R G)) ℕ` is no longer defined when 
`G` is non-abelian. This project also assumes that the ring has no zero divisors to make proofs easier.


# Project structure

This project is split into 5 files *AugmentationMap*, *Basic*, *Integer*, *Lemmas* and *IdealNSMul*. 
* *AugmentationMap* includes theorems and lemmas, alongside the definition, of the `AugmentationMap` for
    a given group and ring, neither needing to be communative
* *Basic* defines the `AugmentationIdeal` for generic communative groups and generic communative rings.
    It also conatins all the theorems and lemmas
* *Integer* contains some proofs about the quotients of powers of the `AugmentationIdeal` in the case of the integer ring
* *Lemmas* defines some helpful theorems and lemmas about `Finset`, `Finsupp`, `Ideal`, and `BigOperators`
* *IdealNSMul* contains a couple of lemmas and alternitive definitions for scaling an Ideal by a natural number. 
    This file is a result of "going down a rabbit hole* and is _not_ imported anywhere in the project

# Main definitions

The main definition and theorems of this project are found in the three files, *Basic*, *AugmentationMap* and *Integer*.

*AugmentationIdeal.Basic*

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
  for any `n > 0` (i.e., any element of the quotient has finite order)
* `AugmentationIdeal.npow_mem.linearcomb_prod_basis` states that any element of `(Δ R,G) ^ n` is a linear combination
  of `∏ i : Fin n, MonoidAlgebra.of gᵢ - 1` with `R` coefficients for `n > 0`

*AugmentationIdeal.AugmentationMap*

* `AugmentationIdeal.AugmentationMap` defines the ring homorphism that sends a `MonoidAlgebra` to the sum of its
  `R` coefficients. This definition requires that the ring has no zero divisors but _not_ that the ring is communative.
* `AugmentationIdeal'.AugmentationMap` defines the equivalent noncomputable ring homorphism using `MonoidAlgebra.lift`.
  This definition requires that the ring is communative but _not_ that it must have no zero divisors
* `MonoidAlgebra.mul_def'` gives an alternative definition to the multiplication of `MonoidAlgebra` such that

*AugmentationIdeal.Integer*

* `AugmentationIdeal.Integers.Quotients.quot_generating_set` states that `(Δ R,G) ^ n ⧸ (Δ R,G) ^ (n+1)` is
  an additive group generated by the set of elements of the form 
  `(∏ i : Fin n, MonoidAlgebra.of gᵢ - 1) + (Δ R,G)^(n+1)`.
* `AugmentationIdeal.Integers.Quotients.finiteGenGroup` defines the `AddGroup.FG` instance for
  `(Δ R,G) ^ n ⧸ (Δ R,G) ^ (n+1)` when `G` is finite
* `AugmentationIdeal.Integers.Quotients.quot_finite` states that `(Δ R,G) ^ n ⧸ (Δ R,G) ^ (n+1)` is a finite
  when `G` is finite

# Future work

This project only encompasses the first section of the first chapter of the four chapter thesis. Work should be done to complte the remaining parts of the thesis.
Work should also be done to change all current definitions to use non-abelian groups as the result are not dependent on abelianness. 

# Authors
* Gareth Kmet - 22 Dec 2023