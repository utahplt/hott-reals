module HoTTReals.Relation.Binary.Order.Proset.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Proset.Base

private
  variable
    ℓ ℓ' : Level

module _
  {A : Type ℓ}
  {_≲_ : Rel A A ℓ'}
  (pre : IsProset _≲_)
  where
  open IsProset pre

  ≡Weaken≤ : {x y : A} → x ≡ y → x ≲ y
  ≡Weaken≤ {x} {y} x≡y = subst (x ≲_) x≡y (is-refl x)
