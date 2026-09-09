-- Vendored from LorenzoMolena by hand 09-08-2026
module HoTTReals.Algebra.ArchimedeanField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import HoTTReals.Algebra.HeytingField.Base
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Algebra.OrderedField.Instances.Rationals

private
  variable
    ℓ ℓ' : Level

record IsArchimedeanField
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_<_ _≤_ : F → F → Type ℓ')
  (ι : ℚ → F) : Type (ℓ-max ℓ ℓ') where
  constructor isarchimedeanfield
  field
    isOrderedField : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_
    isOrderedFieldHom :
      IsOrderedFieldHom (snd ℚOrderedField) ι
        ( orderedfieldstr _ _ _ _ _ _ _ isOrderedField)
    archimedeanProperty :
      (x y : F) → x < y → ∃[ q ∈ ℚ ] (x < ι q) × (ι q < y)

  open IsOrderedField isOrderedField public
  open IsOrderedCommRingMono isOrderedFieldHom public
    renaming
      ( isOrderedCommRingHom to isOrderedCommRingHomι ;
        isCommRingHom to isCommRingHomι ;
        pres0 to ιpres0 ;
        pres1 to ιpres1 ;
        pres+ to ιpres+ ;
        pres· to ιpres· ;
        pres- to ιpres- ;
        pres≤ to ιpres≤ ;
        reflect< to ιreflect< ;
        pres< to ιpres<)

record ArchimedeanFieldStr (ℓ' : Level) (F : Type ℓ) :
  Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor archimedeanfieldstr
  field
    0f 1f : F
    _+_ _·_ : F → F → F
    -_ : F → F
    _<_ _≤_ : F → F → Type ℓ'
    ι : ℚ → F
    isArchimedeanField : IsArchimedeanField 0f 1f _+_ _·_ -_ _<_ _≤_ ι

  open IsArchimedeanField isArchimedeanField public

  infix 8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

ArchimedeanField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanField ℓ ℓ' = TypeWithStr ℓ (ArchimedeanFieldStr ℓ')

ArchimedeanField→OrderedField : ArchimedeanField ℓ ℓ' → OrderedField ℓ ℓ'
ArchimedeanField→OrderedField F =
  fst F , orderedfieldstr _ _ _ _ _ _ _ isOrderedField
  where open ArchimedeanFieldStr (snd F)

ArchimedeanField→HeytingField : ArchimedeanField ℓ ℓ' → HeytingField ℓ ℓ'
ArchimedeanField→HeytingField =
  OrderedField→HeytingField ∘ ArchimedeanField→OrderedField

ArchimedeanField→OrderedCommRing : ArchimedeanField ℓ ℓ' → OrderedCommRing ℓ ℓ'
ArchimedeanField→OrderedCommRing =
  OrderedField→OrderedCommRing ∘ ArchimedeanField→OrderedField

IsArchimedeanOrderedField : OrderedField ℓ ℓ' → Type (ℓ-max ℓ ℓ')
IsArchimedeanOrderedField F =
  Σ[ ι ∈ (ℚ → ⟨ F ⟩) ]
    IsOrderedFieldHom (snd ℚOrderedField) ι (snd F) ×
    ((x y : ⟨ F ⟩) → x < y → ∃[ q ∈ ℚ ] (x < ι q) × (ι q < y))
  where open OrderedFieldStr (snd F)

OrderedField→ArchimedeanField :
  (F : OrderedField ℓ ℓ') → IsArchimedeanOrderedField F → ArchimedeanField ℓ ℓ'
OrderedField→ArchimedeanField F (ι , isOrderedFieldHom , archimedeanProperty) =
  fst F ,
  archimedeanfieldstr _ _ _ _ _ _ _ ι
    ( isarchimedeanfield isOrderedField isOrderedFieldHom archimedeanProperty)
  where open OrderedFieldStr (snd F)
