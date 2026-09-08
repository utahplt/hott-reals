module HoTTReals.Algebra.ArchimedeanOrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Structure

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Fast.Int
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import HoTTReals.Algebra.ArchimedeanRing.Base
open import HoTTReals.Algebra.HeytingField.Base
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Algebra.OrderedField.Properties

private
  variable
    ℓ ℓ' : Level

record IsArchimedeanOrderedField
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_<_ _≤_ : F → F → Type ℓ')
  (ι : ℤ → F) : Type (ℓ-max ℓ ℓ') where
  constructor isarchimedeanorderedfield
  field
    isOrderedField : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_
    isMonomorphism :
      IsOrderedCommRingMono (str ℤOrderedCommRing) ι
        ( orderedcommringstr _ _ _ _ _ _ _
          ( IsOrderedField.isOrderedCommRing isOrderedField))
    archimedeanProperty : (x y : F) → 0f < y → ∃[ k ∈ ℤ ] x < (ι k · y)

  open IsOrderedField isOrderedField public

record ArchimedeanOrderedFieldStr (ℓ' : Level) (F : Type ℓ) :
  Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor archimedeanorderedfieldstr
  field
    0f 1f : F
    _+_ _·_ : F → F → F
    -_ : F → F
    _<_ _≤_ : F → F → Type ℓ'
    ι : ℤ → F
    isArchimedeanOrderedField :
      IsArchimedeanOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_ ι

  open IsArchimedeanOrderedField isArchimedeanOrderedField public

  infix 8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

ArchimedeanOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanOrderedField ℓ ℓ' = TypeWithStr ℓ (ArchimedeanOrderedFieldStr ℓ')

ArchimedeanOrderedField→OrderedField :
  ArchimedeanOrderedField ℓ ℓ' → OrderedField ℓ ℓ'
ArchimedeanOrderedField→OrderedField F =
  fst F , orderedfieldstr _ _ _ _ _ _ _ isOrderedField
  where open ArchimedeanOrderedFieldStr (snd F)

ArchimedeanOrderedField→ArchimedeanRing :
  ArchimedeanOrderedField ℓ ℓ' → ArchimedeanRing ℓ ℓ'
fst (ArchimedeanOrderedField→ArchimedeanRing F) = fst F
snd (ArchimedeanOrderedField→ArchimedeanRing F) =
  archimedeanringstr _ _ _ _ _ _ _ ι isArchimedeanRingF
  where
  open ArchimedeanOrderedFieldStr (snd F)
  isArchimedeanRingF : IsArchimedeanRing 0f 1f _+_ _·_ -_ _<_ _≤_ ι
  IsArchimedeanRing.isOrderedCommRing isArchimedeanRingF = {!!}
  IsArchimedeanRing.·CancelR< isArchimedeanRingF = {!!}
  IsArchimedeanRing.isMonomorphism isArchimedeanRingF = {!!}
  IsArchimedeanRing.archimedeanProperty isArchimedeanRingF = {!!}

ArchimedeanOrderedField→HeytingField :
  ArchimedeanOrderedField ℓ ℓ' → HeytingField ℓ ℓ'
ArchimedeanOrderedField→HeytingField =
  OrderedField→HeytingField ∘ ArchimedeanOrderedField→OrderedField
