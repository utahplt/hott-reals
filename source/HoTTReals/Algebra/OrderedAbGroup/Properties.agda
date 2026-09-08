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
    _<+[_] = {!!}

    [_]+<_ : {x y : G} (z : G) → x < y → z + x < z + y
    [_]+<_ = {!!}

    _≤+[_] : {x y : G} → x ≤ y → (z : G) → x + z ≤ y + z
    _≤+[_] = {!!}

    [_]+≤_ : {x y : G} (z : G) → x ≤ y → z + x ≤ z + y
    [_]+≤_ = {!!}

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
    snd (fst (+PseudolatticeEquivR z)) = {!!}
    snd (+PseudolatticeEquivR z) = {!!}

    +DistL⊓ : (x y z : G) → (x ⊓ y) + z ≡ (x + z) ⊓ (y + z)
    +DistL⊓ = {!!}

    +DistL⊔ : (x y z : G) → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
    +DistL⊔ = {!!}

    -Flip≤ : {x y : G} → x ≤ y → - y ≤ - x
    -Flip≤ {x} {y} = {!!}

    -Flip< : {x y : G} → x < y → - y < - x
    -Flip< {x} {y} = {!!}

    -PseudolatticeEquiv : PseudolatticeEquiv G≤ (DualPseudolattice G≤)
    fst (fst -PseudolatticeEquiv) = -_
    snd (fst -PseudolatticeEquiv) = {!!}
    snd -PseudolatticeEquiv = {!!}

    -⊓ : (x y : G) → - (x ⊓ y) ≡ (- x) ⊔ (- y)
    -⊓ = {!!}

    -⊔ : (x y : G) → - (x ⊔ y) ≡ (- x) ⊓ (- y)
    -⊔ = {!!}

    abs : G → G
    abs z = z ⊔ (- z)

    ≤abs : (z : G) → z ≤ abs z
    ≤abs = {!!}

    -≤abs : (z : G) → - z ≤ abs z
    -≤abs = {!!}

    0≤abs : (z : G) → 0g ≤ abs z
    0≤abs = {!!}

    abs- : (x : G) → abs (- x) ≡ abs x
    abs- = {!!}

    abs-Comm : (x y : G) → abs (x - y) ≡ abs (y - x)
    abs-Comm = {!!}

    absΔ<→<+ : {x y z : G} → abs (x - y) < z → y < x + z
    absΔ<→<+ {x} {y} {z} = {!!}

    absΔ⊓≤R : (x y z : G) → abs ((x ⊓ z) - (y ⊓ z)) ≤ abs (x - y)
    absΔ⊓≤R = {!!}

    absΔ⊓≤L : (x y z : G) → abs ((x ⊓ y) - (x ⊓ z)) ≤ abs (y - z)
    absΔ⊓≤L = {!!}

    absΔ⊔≤R : (x y z : G) → abs ((x ⊔ z) - (y ⊔ z)) ≤ abs (x - y)
    absΔ⊔≤R = {!!}

    absΔ⊔≤L : (x y z : G) → abs ((x ⊔ y) - (x ⊔ z)) ≤ abs (y - z)
    absΔ⊔≤L = {!!}

    0≤→abs≡id : {x : G} → 0g ≤ x → abs x ≡ x
    0≤→abs≡id {x} = {!!}

    absAbs : (x : G) → abs (abs x) ≡ abs x
    absAbs = {!!}

    ▵≤ : (x y : G) → abs (x + y) ≤ abs x + abs y
    ▵≤ = {!!}

    abs≤≃ : {x y : G} → (abs x ≤ y) ≃ (x ≤ y) × (- x ≤ y)
    abs≤≃ {x} {y} = {!!}

    absΔabs≤ : (x y : G) → abs (abs x - abs y) ≤ abs (x - y)
    absΔabs≤ = {!!}

    abs<→< : {x y : G} → abs x < y → x < y
    abs<→< {x} {y} = {!!}

    abs<→-< : {x y : G} → abs x < y → - y < x
    abs<→-< {x} {y} = {!!}
