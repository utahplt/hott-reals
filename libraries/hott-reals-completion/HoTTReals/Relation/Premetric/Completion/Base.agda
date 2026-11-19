open import Cubical.Relation.Premetric.Base

module HoTTReals.Relation.Premetric.Completion.Base {ℓ} {ℓ'}
  (M : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Rationals.Positive

private
  variable
    x y : ⟨ M ⟩
    ε : ℚ₊

open PremetricStr (snd M)

data ℭ : Type (ℓ-max ℓ ℓ')
data _∼[_]_ : ℭ → ℚ₊ → ℭ → Type (ℓ-max ℓ ℓ')

isCauchy∼ : (ℚ₊ → ℭ) → Type (ℓ-max ℓ ℓ')
isCauchy∼ x = ∀ ε δ → x ε ∼[ ε +₊ δ ] x δ

data ℭ where
  ι   : ⟨ M ⟩ → ℭ
  lim : ∀ x → isCauchy∼ x → ℭ
  eqℭ : ∀ x y → (∀ ε → x ∼[ ε ] y) → x ≡ y

data _∼[_]_ where
  ι-ι     : x ≈[ ε ] y → ι x ∼[ ε ] ι y
  ι-lim   : ∀ {y} δ yc
            → ι x ∼[ ε ] y δ
            → ι x ∼[ ε +₊ δ ] lim y yc
  lim-ι   : ∀ {x} δ xc
            → x δ ∼[ ε ] ι y
            → lim x xc ∼[ ε +₊ δ ] ι y
  lim-lim : ∀ {x y} δ η xc yc
            → x δ ∼[ ε ] y η
            → lim x xc ∼[ ε +₊ (δ +₊ η) ] lim y yc
  isProp∼ : ∀ x ε y → isProp (x ∼[ ε ] y)

subst∼ : ∀ x y {ε ε'} → ⟨ ε ⟩₊ ≡ ⟨ ε' ⟩₊ → x ∼[ ε ] y → x ∼[ ε' ] y
subst∼ x y = subst (x ∼[_] y) ∘ ℚ₊≡
