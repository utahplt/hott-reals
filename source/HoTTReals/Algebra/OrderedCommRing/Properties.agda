module HoTTReals.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Relation.Binary.Order.Pseudolattice.Base

private
  variable
    ℓ ℓ' : Level

module _ (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    R≤ = OrderedCommRing→PseudoLattice R'
  open OrderedCommRingStr (snd R')

  module OrderedCommRingTheory where

    +PseudolatticeEquivR : (z : R) → PseudolatticeEquiv R≤ R≤
    fst (fst (+PseudolatticeEquivR z)) = _+ z
    snd (fst (+PseudolatticeEquivR z)) = {!!}
    snd (+PseudolatticeEquivR z) = {!!}

    +DistL⊓ : (x y z : R) → (x ⊓ y) + z ≡ (x + z) ⊓ (y + z)
    +DistL⊓ = {!!}

    +DistL⊔ : (x y z : R) → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
    +DistL⊔ = {!!}
