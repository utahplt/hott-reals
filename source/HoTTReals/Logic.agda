module HoTTReals.Logic where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

_↔_ : {i j : Level} → Type i → Type j → Type (ℓ-max i j)
A ↔ B = (A → B) × (B → A)

≠-symmetric : {i : Level} {A : Type i} → 
              {x y : A} → ¬ x ≡ y → ¬ y ≡ x
≠-symmetric p q = p (sym q)
