module HoTTReals.Logic where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

≠-symmetric : {i : Level} {A : Type i} → 
              {x y : A} → ¬ x ≡ y → ¬ y ≡ x
≠-symmetric p q = p (sym q)
