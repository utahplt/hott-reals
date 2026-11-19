module HoTTReals.Foundations.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level
    A  : Type ℓ

-- syntax for chains of implications, from qlbrpl's PR #1228:
step→ : (B : Type ℓ') → (A → B) → A → B
step→ _ f = f

step→⟨⟩ : (A : Type ℓ) → A → A
step→⟨⟩ A a = a

syntax step→ B f x = x →⟨ f ⟩ B
syntax step→⟨⟩ A a = a →⟨⟩ A
infixl 2 step→ step→⟨⟩

begin→ : (A : Type ℓ) → A → A
begin→ = idfun

syntax begin→ A a = begin→[ a ] A
infixr 3 begin→
