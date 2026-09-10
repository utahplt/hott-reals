module HoTTReals.Algebra.ArchimedeanField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using
  ( ℚOrderedCommRing ; module 1/2∈ℚ ; module PositiveRationals)

open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)

open import Cubical.HITs.PropositionalTruncation as PT

open import HoTTReals.Algebra.OrderedCommRing.Morphisms
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Algebra.OrderedField.Instances.Rationals
open import HoTTReals.Algebra.ArchimedeanField.Base

open OrderedFieldStr (snd ℚOrderedField) renaming (isOrderedField to isOFℚ)
open 1/2∈ℚ

open ArchimedeanFieldStr

ℚArchimedeanField : ArchimedeanField ℓ-zero ℓ-zero
fst ℚArchimedeanField = ℚ
0f  (snd ℚArchimedeanField) = 0
1f  (snd ℚArchimedeanField) = 1
_+_ (snd ℚArchimedeanField) = ℚ._+_
_·_ (snd ℚArchimedeanField) = ℚ._·_
-_  (snd ℚArchimedeanField) = ℚ.-_
_<_ (snd ℚArchimedeanField) = ℚ._<_
_≤_ (snd ℚArchimedeanField) = ℚ._≤_
ι   (snd ℚArchimedeanField) = idfun ℚ
isArchimedeanField (snd ℚArchimedeanField) = isArchimedeanFieldℚ
  where
  open IsArchimedeanField

  isArchimedeanFieldℚ : IsArchimedeanField _ _ _ _ _ _ _ _
  isArchimedeanFieldℚ .isOrderedField      = isOFℚ
  isArchimedeanFieldℚ .isOrderedFieldHom   = snd (idOrderedCommRingMono ℚOrderedCommRing)
  isArchimedeanFieldℚ .archimedeanProperty = λ x y x<y →
    ∣ mean x y , <→<mean x y x<y , <→mean< x y x<y ∣₁
