module HoTTReals.Algebra.OrderedAbGroup.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice.Base
import Cubical.Relation.Binary.Order.Pseudolattice.Properties as
  PseudolatticeProperties
open import Cubical.Relation.Binary.Order.Pseudolattice.Properties using
  ( DualPseudolattice)
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.QuosetReasoning

open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Relation.Binary.Order.Pseudolattice.Properties

private
  variable
    ℓ ℓ' : Level

module _ (G' : OrderedAbGroup ℓ ℓ') where
  private
    G = fst G'
    G≤ = OrderedAbGroup→Pseudolattice G'
  open OrderedAbGroupStr (snd G')

  module OrderedAbGroupReasoning where
    open <-≤-Reasoning
      ( fst G')
      ( str (OrderedAbGroup→Poset G'))
      ( str (OrderedAbGroup→Quoset G'))
      ( λ x {y} {z} → <-≤-trans x y z)
      ( λ x {y} {z} → ≤-<-trans x y z)
      ( λ {x} {y} → <-≤-weaken x y)
      public

    open <-syntax public
    open ≤-syntax public
    open ≡-syntax public

    _<+[_] : {x y : G} → x < y → (z : G) → x + z < y + z
    _<+[_] x<y z = +MonoR< _ _ z x<y

    [_]+<_ : {x y : G} (z : G) → x < y → z + x < z + y
    [_]+<_ z = subst2 _<_ (+Comm _ z) (+Comm _ z) ∘ +MonoR< _ _ z

    _≤+[_] : {x y : G} → x ≤ y → (z : G) → x + z ≤ y + z
    _≤+[_] x≤y z = +MonoR≤ _ _ z x≤y

    [_]+≤_ : {x y : G} (z : G) → x ≤ y → z + x ≤ z + y
    [_]+≤_ z = subst2 _≤_ (+Comm _ z) (+Comm _ z) ∘ +MonoR≤ _ _ z

  open OrderedAbGroupReasoning

  module OrderedAbGroupTheory where
    open PseudolatticeProperties.PseudolatticeTheory G≤ public using ()
      renaming
      ( L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨Comm to ⊔Comm ; ∨Idem to ⊔Idem ;
        ∨LUB to ⊔LUB ; ∧≤L to ⊓≤L ; ∧≤R to ⊓≤R ; ∧Comm to ⊓Comm ;
        ∧Idem to ⊓Idem ; ∧GLB to ⊓GLB)
    open PseudolatticeProperties.JoinProperties G≤ using (isJoin∨)
    open GroupTheory (AbGroup→Group (OrderedAbGroup→AbGroup G')) using
      ( invInv ; invDistr ; inv1g)
    open MeetProperties G≤ using (∧Mono)

    +PseudolatticeEquivR : (z : G) → PseudolatticeEquiv G≤ G≤
    fst (fst (+PseudolatticeEquivR z)) = _+ z
    snd (fst (+PseudolatticeEquivR z)) =
      isoToIsEquiv (iso (_+ z) (_- z) subtractAddInverse addSubtractInverse)
      where
      subtractAddInverse : (x : G) → (x - z) + z ≡ x
      subtractAddInverse x =
        (x - z) + z
          ≡⟨ sym (+Assoc x (- z) z) ⟩
        x + (- z + z)
          ≡⟨ cong (x +_) (+InvL z) ⟩
        x + 0g
          ≡⟨ +IdR x ⟩
        x ∎

      addSubtractInverse : (x : G) → (x + z) - z ≡ x
      addSubtractInverse x =
        (x + z) - z
          ≡⟨ sym (+Assoc x z (- z)) ⟩
        x + (z - z)
          ≡⟨ cong (x +_) (+InvR z) ⟩
        x + 0g
          ≡⟨ +IdR x ⟩
        x ∎
    snd (+PseudolatticeEquivR z) =
      makeIsPseudolatticeEquiv
        ( fst (+PseudolatticeEquivR z))
        ( λ x y → +MonoR≤ x y z)
        ( λ x y → +MonoR≤ x y (- z))

    +DistL⊓ : (x y z : G) → (x ⊓ y) + z ≡ (x + z) ⊓ (y + z)
    +DistL⊓ x y z = pres∧ (+PseudolatticeEquivR z) x y

    +DistL⊔ : (x y z : G) → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
    +DistL⊔ x y z = pres∨ (+PseudolatticeEquivR z) x y

    -Flip≤ : {x y : G} → x ≤ y → - y ≤ - x
    -Flip≤ {x} {y} x≤y = begin≤
      - y
        ≡→≤⟨ expandNeg ⟩
      x + (- x - y)
        ≤⟨ x≤y ≤+[ - x - y ] ⟩
      y + (- x - y)
        ≡→≤⟨ collapseNeg ⟩
      - x ◾
      where
      expandNeg : - y ≡ x + (- x - y)
      expandNeg =
        - y
          ≡⟨ sym (+IdL (- y)) ⟩
        0g - y
          ≡⟨ cong (_- y) (sym (+InvR x)) ⟩
        (x - x) - y
          ≡⟨ sym (+Assoc x (- x) (- y)) ⟩
        x + (- x - y) ∎

      collapseNeg : y + (- x - y) ≡ - x
      collapseNeg =
        y + (- x - y)
          ≡⟨ cong (y +_) (+Comm (- x) (- y)) ⟩
        y + (- y - x)
          ≡⟨ +Assoc y (- y) (- x) ⟩
        (y - y) - x
          ≡⟨ cong (_- x) (+InvR y) ⟩
        0g - x
          ≡⟨ +IdL (- x) ⟩
        - x ∎

    -Flip< : {x y : G} → x < y → - y < - x
    -Flip< {x} {y} x<y = begin<
      - y
        ≡→≤⟨ expandNeg ⟩
      x + (- x - y)
        <⟨ x<y <+[ - x - y ] ⟩
      y + (- x - y)
        ≡→≤⟨ collapseNeg ⟩
      - x ◾
      where
      expandNeg : - y ≡ x + (- x - y)
      expandNeg =
        - y
          ≡⟨ sym (+IdL (- y)) ⟩
        0g - y
          ≡⟨ cong (_- y) (sym (+InvR x)) ⟩
        (x - x) - y
          ≡⟨ sym (+Assoc x (- x) (- y)) ⟩
        x + (- x - y) ∎

      collapseNeg : y + (- x - y) ≡ - x
      collapseNeg =
        y + (- x - y)
          ≡⟨ cong (y +_) (+Comm (- x) (- y)) ⟩
        y + (- y - x)
          ≡⟨ +Assoc y (- y) (- x) ⟩
        (y - y) - x
          ≡⟨ cong (_- x) (+InvR y) ⟩
        0g - x
          ≡⟨ +IdL (- x) ⟩
        - x ∎

    -PseudolatticeEquiv : PseudolatticeEquiv G≤ (DualPseudolattice G≤)
    fst (fst -PseudolatticeEquiv) = -_
    snd (fst -PseudolatticeEquiv) = isoToIsEquiv (iso -_ -_ invInv invInv)
    snd -PseudolatticeEquiv =
      makeIsPseudolatticeEquiv
        ( fst -PseudolatticeEquiv)
        ( λ x y → -Flip≤ {x} {y})
        ( λ x y → -Flip≤ {y} {x})

    -⊓ : (x y : G) → - (x ⊓ y) ≡ (- x) ⊔ (- y)
    -⊓ x y = pres∧ -PseudolatticeEquiv x y

    -⊔ : (x y : G) → - (x ⊔ y) ≡ (- x) ⊓ (- y)
    -⊔ x y = pres∨ -PseudolatticeEquiv x y

    abs : G → G
    abs z = z ⊔ (- z)

    ≤abs : (z : G) → z ≤ abs z
    ≤abs z = L≤⊔

    -≤abs : (z : G) → - z ≤ abs z
    -≤abs z = R≤⊔

    0≤abs : (z : G) → 0g ≤ abs z
    0≤abs z =
      invEq
        ( ≤≃¬> 0g (abs z))
        ( λ ∣z∣<0 →
          is-irrefl 0g
            ( begin<
              0g
                ≡→≤⟨ sym inv1g ⟩
              - 0g
                <⟨ -Flip< ∣z∣<0 ⟩
              - abs z
                ≤⟨ -Flip≤ (≤abs z) ⟩
              - z
                ≤⟨ -≤abs z ⟩
              abs z
                <⟨ ∣z∣<0 ⟩
              0g ◾))

    abs- : (x : G) → abs (- x) ≡ abs x
    abs- x = cong ((- x) ⊔_) (invInv x) ∙ ⊔Comm

    abs-Comm : (x y : G) → abs (x - y) ≡ abs (y - x)
    abs-Comm x y =
      (x - y) ⊔ (- (x - y))
        ≡⟨ ⊔Comm ⟩
      (- (x - y)) ⊔ (x - y)
        ≡⟨ cong₂ _⊔_ (negDifference x y) (sym (negDifference y x)) ⟩
      (y - x) ⊔ (- (y - x)) ∎
      where
      negDifference : (a b : G) → - (a - b) ≡ b - a
      negDifference a b = invDistr a (- b) ∙ cong (_- a) (invInv b)

    absΔ<→<+ : {x y z : G} → abs (x - y) < z → y < x + z
    absΔ<→<+ {x} {y} {z} ∣x-y∣<z = begin<
      y
        ≡→≤⟨ sym undoDifference ⟩
      x + (- (x - y))
        ≤⟨ [ x ]+≤ -≤abs (x - y) ⟩
      x + abs (x - y)
        <⟨ [ x ]+< ∣x-y∣<z ⟩
      x + z ◾
      where
      undoDifference : x + (- (x - y)) ≡ y
      undoDifference =
        x + (- (x - y))
          ≡⟨ cong (x +_) (invDistr x (- y)) ⟩
        x + (- (- y) - x)
          ≡⟨ cong (λ w → x + (w - x)) (invInv y) ⟩
        x + (y - x)
          ≡⟨ cong (x +_) (+Comm y (- x)) ⟩
        x + (- x + y)
          ≡⟨ +Assoc x (- x) y ⟩
        (x - x) + y
          ≡⟨ cong (_+ y) (+InvR x) ⟩
        0g + y
          ≡⟨ +IdL y ⟩
        y ∎

    absΔ⊓≤R : (x y z : G) → abs ((x ⊓ z) - (y ⊓ z)) ≤ abs (x - y)
    absΔ⊓≤R x y z =
      ⊔LUB (Δ⊓≤ x y)
        ( subst2 _≤_ (sym (negDifference (x ⊓ z) (y ⊓ z))) (abs-Comm y x)
          ( Δ⊓≤ y x))
      where
      negDifference : (a b : G) → - (a - b) ≡ b - a
      negDifference a b = invDistr a (- b) ∙ cong (_- a) (invInv b)

      splitDifference : (p q r : G) → (p - q) + (q - r) ≡ p - r
      splitDifference p q r =
        (p - q) + (q - r)
          ≡⟨ sym (+Assoc p (- q) (q - r)) ⟩
        p + (- q + (q - r))
          ≡⟨ cong (p +_) (+Assoc (- q) q (- r)) ⟩
        p + ((- q + q) - r)
          ≡⟨ cong (λ w → p + (w - r)) (+InvL q) ⟩
        p + (0g - r)
          ≡⟨ cong (p +_) (+IdL (- r)) ⟩
        p - r ∎

      addDifference : (q r : G) → q + (r - q) ≡ r
      addDifference q r =
        q + (r - q)
          ≡⟨ cong (q +_) (+Comm r (- q)) ⟩
        q + (- q + r)
          ≡⟨ +Assoc q (- q) r ⟩
        (q - q) + r
          ≡⟨ cong (_+ r) (+InvR q) ⟩
        0g + r
          ≡⟨ +IdL r ⟩
        r ∎

      Δ⊓≤ : (a b : G) → (a ⊓ z) - (b ⊓ z) ≤ abs (a - b)
      Δ⊓≤ a b = begin≤
        (a ⊓ z) - (b ⊓ z)
          ≡→≤⟨ sym (splitDifference (a ⊓ z) d (b ⊓ z)) ⟩
        ((a ⊓ z) - d) + (d - (b ⊓ z))
          ≤⟨ meetSubtractBound≤ ≤+[ d - (b ⊓ z) ] ⟩
        (b ⊓ z) + (d - (b ⊓ z))
          ≡→≤⟨ addDifference (b ⊓ z) d ⟩
        d ◾
        where
        d : G
        d = abs (a - b)

        subtractBound≤ : a - d ≤ b
        subtractBound≤ = begin≤
          a - d
            ≡→≤⟨ sym (splitDifference a b d) ⟩
          (a - b) + (b - d)
            ≤⟨ ≤abs (a - b) ≤+[ b - d ] ⟩
          d + (b - d)
            ≡→≤⟨ addDifference d b ⟩
          b ◾

        subtractNonnegative≤ : z - d ≤ z
        subtractNonnegative≤ = begin≤
          z - d
            ≤⟨ [ z ]+≤ -Flip≤ (0≤abs (a - b)) ⟩
          z + (- 0g)
            ≡→≤⟨ cong (z +_) inv1g ∙ +IdR z ⟩
          z ◾

        meetSubtractBound≤ : (a ⊓ z) - d ≤ b ⊓ z
        meetSubtractBound≤ = begin≤
          (a ⊓ z) - d
            ≡→≤⟨ +DistL⊓ a z (- d) ⟩
          (a - d) ⊓ (z - d)
            ≤⟨ ∧Mono subtractBound≤ subtractNonnegative≤ ⟩
          b ⊓ z ◾

    absΔ⊓≤L : (x y z : G) → abs ((x ⊓ y) - (x ⊓ z)) ≤ abs (y - z)
    absΔ⊓≤L x y z =
      subst
        ( λ w → abs w ≤ abs (y - z))
        ( cong₂ _-_ ⊓Comm ⊓Comm)
        ( absΔ⊓≤R y z x)

    absΔ⊔≤R : (x y z : G) → abs ((x ⊔ z) - (y ⊔ z)) ≤ abs (x - y)
    absΔ⊔≤R x y z =
      subst2 _≤_ meetsToJoins (absΔ- x y) (absΔ⊓≤R (- x) (- y) (- z))
      where
      differenceNeg : (a b : G) → (- a) - (- b) ≡ - (a - b)
      differenceNeg a b = +Comm (- a) (- (- b)) ∙ sym (invDistr a (- b))

      absΔ- : (a b : G) → abs ((- a) - (- b)) ≡ abs (a - b)
      absΔ- a b = cong abs (differenceNeg a b) ∙ abs- (a - b)

      meetsToJoins :
        abs (((- x) ⊓ (- z)) - ((- y) ⊓ (- z))) ≡ abs ((x ⊔ z) - (y ⊔ z))
      meetsToJoins =
        abs (((- x) ⊓ (- z)) - ((- y) ⊓ (- z)))
          ≡⟨ cong abs (cong₂ _-_ (sym (-⊔ x z)) (sym (-⊔ y z))) ⟩
        abs ((- (x ⊔ z)) - (- (y ⊔ z)))
          ≡⟨ absΔ- (x ⊔ z) (y ⊔ z) ⟩
        abs ((x ⊔ z) - (y ⊔ z)) ∎

    absΔ⊔≤L : (x y z : G) → abs ((x ⊔ y) - (x ⊔ z)) ≤ abs (y - z)
    absΔ⊔≤L x y z =
      subst
        ( λ w → abs w ≤ abs (y - z))
        ( cong₂ _-_ ⊔Comm ⊔Comm)
        ( absΔ⊔≤R y z x)

    0≤→abs≡id : {x : G} → 0g ≤ x → abs x ≡ x
    0≤→abs≡id {x} 0≤x =
      is-antisym (abs x) x
        ( ⊔LUB
          ( is-refl x)
          ( is-trans≤ (- x) 0g x (subst (- x ≤_) inv1g (-Flip≤ 0≤x)) 0≤x))
        ( ≤abs x)

    absAbs : (x : G) → abs (abs x) ≡ abs x
    absAbs x = 0≤→abs≡id (0≤abs x)

    ▵≤ : (x y : G) → abs (x + y) ≤ abs x + abs y
    ▵≤ x y =
      ⊔LUB
        ( begin≤
          x + y
            ≤⟨ ≤abs x ≤+[ y ] ⟩
          abs x + y
            ≤⟨ [ abs x ]+≤ ≤abs y ⟩
          abs x + abs y ◾)
        ( begin≤
          - (x + y)
            ≡→≤⟨ negSum ⟩
          - x - y
            ≤⟨ -≤abs x ≤+[ - y ] ⟩
          abs x - y
            ≤⟨ [ abs x ]+≤ -≤abs y ⟩
          abs x + abs y ◾)
      where
      negSum : - (x + y) ≡ - x - y
      negSum = invDistr x y ∙ +Comm (- y) (- x)

    abs≤≃ : {x y : G} → (abs x ≤ y) ≃ (x ≤ y) × (- x ≤ y)
    abs≤≃ {x} {y} = isJoin∨

    absΔabs≤ : (x y : G) → abs (abs x - abs y) ≤ abs (x - y)
    absΔabs≤ x y =
      invEq
        ( abs≤≃ {abs x - abs y} {abs (x - y)})
        ( bound x y ,
          subst2 _≤_ negateDifference (abs-Comm y x) (bound y x))
      where
      negateDifference : abs y - abs x ≡ - (abs x - abs y)
      negateDifference =
        abs y - abs x
          ≡⟨ cong (_- abs x) (sym (invInv (abs y))) ⟩
        - (- abs y) - abs x
          ≡⟨ sym (invDistr (abs x) (- abs y)) ⟩
        - (abs x - abs y) ∎

      bound : (a b : G) → abs a - abs b ≤ abs (a - b)
      bound a b = begin≤
        abs a - abs b
          ≤⟨ absBelowSum ≤+[ - abs b ] ⟩
        (abs (a - b) + abs b) - abs b
          ≡→≤⟨ cancelTranslation ⟩
        abs (a - b) ◾
        where
        restoreDifference : (a - b) + b ≡ a
        restoreDifference =
          (a - b) + b
            ≡⟨ sym (+Assoc a (- b) b) ⟩
          a + (- b + b)
            ≡⟨ cong (a +_) (+InvL b) ⟩
          a + 0g
            ≡⟨ +IdR a ⟩
          a ∎

        absBelowSum : abs a ≤ abs (a - b) + abs b
        absBelowSum = begin≤
          abs a
            ≡→≤⟨ cong abs (sym restoreDifference) ⟩
          abs ((a - b) + b)
            ≤⟨ ▵≤ (a - b) b ⟩
          abs (a - b) + abs b ◾

        cancelTranslation : (abs (a - b) + abs b) - abs b ≡ abs (a - b)
        cancelTranslation =
          (abs (a - b) + abs b) - abs b
            ≡⟨ sym (+Assoc (abs (a - b)) (abs b) (- abs b)) ⟩
          abs (a - b) + (abs b - abs b)
            ≡⟨ cong (abs (a - b) +_) (+InvR (abs b)) ⟩
          abs (a - b) + 0g
            ≡⟨ +IdR (abs (a - b)) ⟩
          abs (a - b) ∎

    abs<→< : {x y : G} → abs x < y → x < y
    abs<→< {x} {y} ∣x∣<y = ≤-<-trans x (abs x) y (≤abs x) ∣x∣<y

    abs<→-< : {x y : G} → abs x < y → - y < x
    abs<→-< {x} {y} ∣x∣<y =
      subst
        ( - y <_)
        ( invInv x)
        ( -Flip< (≤-<-trans (- x) (abs x) y (-≤abs x) ∣x∣<y))
