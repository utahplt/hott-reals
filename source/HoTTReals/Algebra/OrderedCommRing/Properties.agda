module HoTTReals.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Base
import Cubical.Algebra.OrderedCommRing.Properties as OrderedCommRingProperties

open import Cubical.Relation.Binary.Order.Pseudolattice.Base
open import Cubical.Relation.Binary.Order.Pseudolattice.Properties
  using (DualPseudolattice)

private
  variable
    ℓ ℓ' : Level

module _ (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    R≤ = OrderedCommRing→PseudoLattice R'
  open OrderedCommRingStr (snd R')
  open OrderedCommRingProperties.OrderedCommRingTheory R' using (abs)

  module OrderedCommRingTheory where

    +PseudolatticeEquivR : (z : R) → PseudolatticeEquiv R≤ R≤
    fst (fst (+PseudolatticeEquivR z)) = _+ z
    snd (fst (+PseudolatticeEquivR z)) = {!!}
    snd (+PseudolatticeEquivR z) = {!!}

    +DistL⊓ : (x y z : R) → (x ⊓ y) + z ≡ (x + z) ⊓ (y + z)
    +DistL⊓ = {!!}

    +DistL⊔ : (x y z : R) → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
    +DistL⊔ = {!!}

    -PseudolatticeEquiv : PseudolatticeEquiv R≤ (DualPseudolattice R≤)
    fst (fst -PseudolatticeEquiv) = -_
    snd (fst -PseudolatticeEquiv) = {!!}
    snd -PseudolatticeEquiv = {!!}

    -⊓ : (x y : R) → - (x ⊓ y) ≡ (- x) ⊔ (- y)
    -⊓ = {!!}

    -⊔ : (x y : R) → - (x ⊔ y) ≡ (- x) ⊓ (- y)
    -⊔ = {!!}

    absΔ⊔≤R : (x y z : R) → abs ((x ⊔ z) - (y ⊔ z)) ≤ abs (x - y)
    absΔ⊔≤R = {!!}

    absΔ⊔≤L : (x y z : R) → abs ((x ⊔ y) - (x ⊔ z)) ≤ abs (y - z)
    absΔ⊔≤L = {!!}

    absΔ⊓≤R : (x y z : R) → abs ((x ⊓ z) - (y ⊓ z)) ≤ abs (x - y)
    absΔ⊓≤R = {!!}

    absΔ⊓≤L : (x y z : R) → abs ((x ⊓ y) - (x ⊓ z)) ≤ abs (y - z)
    absΔ⊓≤L = {!!}
