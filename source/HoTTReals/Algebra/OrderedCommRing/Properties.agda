module HoTTReals.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.OrderedCommRing.Base
import Cubical.Algebra.OrderedCommRing.Properties as OrderedCommRingProperties
open import Cubical.Algebra.Ring

open import Cubical.Relation.Binary.Order.Pseudolattice.Base
open import Cubical.Relation.Binary.Order.Pseudolattice.Properties
  using (DualPseudolattice)

open import Cubical.Tactics.CommRingSolver

open import HoTTReals.Relation.Binary.Order.Pseudolattice.Properties

private
  variable
    ℓ ℓ' : Level

module _ (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    R≤ = OrderedCommRing→PseudoLattice R'
    RCR = OrderedCommRing→CommRing R'
  open OrderedCommRingStr (snd R')

  module OrderedCommRingTheory where
    open OrderedCommRingProperties.OrderedCommRingReasoning R'
    open OrderedCommRingProperties.OrderedCommRingTheory R'
      using (⊔LUB ; ⊔Comm ; ⊓Comm ; -Flip≤ ; 0≤→-≤0 ;
             abs ; ≤abs ; 0≤abs ; abs- ; abs-Comm)
    open RingTheory (OrderedCommRingProperties.OrderedCommRing→Ring R')
      using (-Idempotent)
    open MeetProperties R≤ using (∧Mono)

    +PseudolatticeEquivR : (z : R) → PseudolatticeEquiv R≤ R≤
    fst (fst (+PseudolatticeEquivR z)) = _+ z
    snd (fst (+PseudolatticeEquivR z)) =
      isoToIsEquiv
        (iso (_+ z) (_- z) subtractAddInverse addSubtractInverse)
      where
      subtractAddInverse : (x : R) → (x - z) + z ≡ x
      subtractAddInverse x = solve! RCR

      addSubtractInverse : (x : R) → (x + z) - z ≡ x
      addSubtractInverse x = solve! RCR
    snd (+PseudolatticeEquivR z) =
      makeIsPseudolatticeEquiv
        (fst (+PseudolatticeEquivR z))
        (λ x y → +MonoR≤ x y z)
        (λ x y → +MonoR≤ x y (- z))

    +DistL⊓ : (x y z : R) → (x ⊓ y) + z ≡ (x + z) ⊓ (y + z)
    +DistL⊓ x y z = pres∧ (+PseudolatticeEquivR z) x y

    +DistL⊔ : (x y z : R) → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
    +DistL⊔ x y z = pres∨ (+PseudolatticeEquivR z) x y

    -PseudolatticeEquiv : PseudolatticeEquiv R≤ (DualPseudolattice R≤)
    fst (fst -PseudolatticeEquiv) = -_
    snd (fst -PseudolatticeEquiv) =
      isoToIsEquiv (iso -_ -_ -Idempotent -Idempotent)
    snd -PseudolatticeEquiv =
      makeIsPseudolatticeEquiv
        (fst -PseudolatticeEquiv)
        -Flip≤
        (flip -Flip≤)

    -⊓ : (x y : R) → - (x ⊓ y) ≡ (- x) ⊔ (- y)
    -⊓ = pres∧ -PseudolatticeEquiv

    -- TODO: Use solver?
    -⊔ : (x y : R) → - (x ⊔ y) ≡ (- x) ⊓ (- y)
    -⊔ x y =
      - (x ⊔ y)
        ≡⟨ cong -_ (sym (cong₂ _⊔_ (-Idempotent x) (-Idempotent y))) ⟩
      - ((- (- x)) ⊔ (- (- y)))
        ≡⟨ cong -_ (sym (-⊓ (- x) (- y))) ⟩
      - (- ((- x) ⊓ (- y)))
        ≡⟨ -Idempotent _ ⟩
      (- x) ⊓ (- y) ∎

    absΔ⊓≤R : (x y z : R) → abs ((x ⊓ z) - (y ⊓ z)) ≤ abs (x - y)
    absΔ⊓≤R x y z =
      ⊔LUB
        ( Δ⊓≤ x y)
        ( subst2
          ( _≤_)
          ( swapDifference)
          ( abs-Comm y x)
          ( Δ⊓≤ y x))
      where
      swapDifference : (y ⊓ z) - (x ⊓ z) ≡ - ((x ⊓ z) - (y ⊓ z))
      swapDifference = solve! RCR

      Δ⊓≤ : (a b : R) → (a ⊓ z) - (b ⊓ z) ≤ abs (a - b)
      Δ⊓≤ a b = begin≤
        (a ⊓ z) - (b ⊓ z)
          ≡→≤⟨ solve! RCR ⟩
        ((a ⊓ z) - d) + (d - (b ⊓ z))
          ≤⟨ meetSubtractBound≤ ≤+[ d - (b ⊓ z) ] ⟩
        (b ⊓ z) + (d - (b ⊓ z))
          ≡→≤⟨ solve! RCR ⟩
        d ◾
        where
        d : R
        d = abs (a - b)

        subtractBound≤ : a - d ≤ b
        subtractBound≤ = begin≤
          a - d
            ≡→≤⟨ solve! RCR ⟩
          (a - b) + (b - d)
            ≤⟨ ≤abs (a - b) ≤+[ b - d ] ⟩
          d + (b - d)
            ≡→≤⟨ solve! RCR ⟩
          b ◾

        subtractNonnegative≤ : z - d ≤ z
        subtractNonnegative≤ = begin≤
          z - d
            ≤⟨ [ z ]+≤ 0≤→-≤0 d (0≤abs (a - b)) ⟩
          z + 0r
            ≡→≤⟨ +IdR z ⟩
          z ◾

        meetSubtractBound≤ : (a ⊓ z) - d ≤ b ⊓ z
        meetSubtractBound≤ = begin≤
          (a ⊓ z) - d
            ≡→≤⟨ +DistL⊓ a z (- d) ⟩
          (a - d) ⊓ (z - d)
            ≤⟨ ∧Mono subtractBound≤ subtractNonnegative≤ ⟩
          b ⊓ z ◾

    absΔ⊓≤L : (x y z : R) → abs ((x ⊓ y) - (x ⊓ z)) ≤ abs (y - z)
    absΔ⊓≤L x y z =
      subst (λ w → abs w ≤ abs (y - z)) (cong₂ _-_ ⊓Comm ⊓Comm) (absΔ⊓≤R y z x)

    absΔ⊔≤R : (x y z : R) → abs ((x ⊔ z) - (y ⊔ z)) ≤ abs (x - y)
    absΔ⊔≤R x y z =
      subst2 _≤_
        (cong abs (cong₂ _-_ (sym (-⊔ x z)) (sym (-⊔ y z))) ∙
         absΔ- (x ⊔ z) (y ⊔ z))
        (absΔ- x y)
        (absΔ⊓≤R (- x) (- y) (- z))
      where
      absΔ- : (a b : R) → abs (- a - (- b)) ≡ abs (a - b)
      absΔ- a b = cong abs (solve! RCR) ∙ abs- (a - b)

    absΔ⊔≤L : (x y z : R) → abs ((x ⊔ y) - (x ⊔ z)) ≤ abs (y - z)
    absΔ⊔≤L x y z =
      subst (λ w → abs w ≤ abs (y - z)) (cong₂ _-_ ⊔Comm ⊔Comm) (absΔ⊔≤R y z x)
