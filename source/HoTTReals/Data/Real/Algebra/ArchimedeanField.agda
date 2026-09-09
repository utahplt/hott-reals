module HoTTReals.Data.Real.Algebra.ArchimedeanField where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using
  ( ℚOrderedCommRing)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.ArchimedeanField.Base
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Algebra.OrderedCommRing
open import HoTTReals.Data.Real.Algebra.OrderedField
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Relation.Premetric.Instances.ArchimedeanField

ℝArchimedeanField : ArchimedeanField ℓ-zero ℓ-zero
fst ℝArchimedeanField = ℝ
ArchimedeanFieldStr.0f (snd ℝArchimedeanField) = 0
ArchimedeanFieldStr.1f (snd ℝArchimedeanField) = 1
ArchimedeanFieldStr._+_ (snd ℝArchimedeanField) = _+_
ArchimedeanFieldStr._·_ (snd ℝArchimedeanField) = _·_
ArchimedeanFieldStr.-_ (snd ℝArchimedeanField) = -_
ArchimedeanFieldStr._<_ (snd ℝArchimedeanField) = _<_
ArchimedeanFieldStr._≤_ (snd ℝArchimedeanField) = _≤_
ArchimedeanFieldStr.ι (snd ℝArchimedeanField) = rat
ArchimedeanFieldStr.isArchimedeanField (snd ℝArchimedeanField) =
  isArchimedeanFieldℝ
  where
  isCommRingHomrat : IsCommRingHom (snd ℚCommRing) rat (snd ℝCommRing)
  IsCommRingHom.pres0 isCommRingHomrat = refl
  IsCommRingHom.pres1 isCommRingHomrat = refl
  IsCommRingHom.pres+ isCommRingHomrat = λ q r → refl
  IsCommRingHom.pres· isCommRingHomrat = λ q r → sym (rat·rat q r)
  IsCommRingHom.pres- isCommRingHomrat = λ q → refl

  isOrderedCommRingHomrat :
    IsOrderedCommRingHom (snd ℚOrderedCommRing) rat (snd ℝOrderedCommRing)
  IsOrderedCommRingHom.isCommRingHom isOrderedCommRingHomrat =
    isCommRingHomrat
  IsOrderedCommRingHom.pres≤ isOrderedCommRingHomrat =
    λ q r → equivFun (≤≃rat≤ {q} {r})
  IsOrderedCommRingHom.reflect< isOrderedCommRingHomrat =
    λ q r → invEq (<≃rat< {q} {r})

  isArchimedeanFieldℝ :
    IsArchimedeanField 0 1 _+_ _·_ -_ _<_ _≤_ rat
  IsArchimedeanField.isOrderedField isArchimedeanFieldℝ =
    OrderedFieldStr.isOrderedField $ snd ℝOrderedField
  IsOrderedCommRingMono.isOrderedCommRingHom
    ( IsArchimedeanField.isOrderedFieldHom isArchimedeanFieldℝ) =
    isOrderedCommRingHomrat
  IsOrderedCommRingMono.pres<
    ( IsArchimedeanField.isOrderedFieldHom isArchimedeanFieldℝ) =
    λ q r → equivFun (<≃rat< {q} {r})
  IsArchimedeanField.archimedeanProperty isArchimedeanFieldℝ = isArchimedean<

inducedPremetricSpaceℝ≡ :
  inducedPremetricSpace ℝArchimedeanField ≡ ℝPremetricSpace
inducedPremetricSpaceℝ≡ i .fst = ℝ
inducedPremetricSpaceℝ≡ i .snd = premetricstr (≈≡ i) (isPremetric≡ i)
  where
  ≈≡ : _≈ᶠ[_]_ ℝArchimedeanField ≡ PremetricStr._≈[_]_ (snd ℝPremetricSpace)
  ≈≡ = funExt λ x → funExt λ ε → funExt λ y → sym $ ua (∼≃abs< {x} {y} {ε})

  isPremetric≡ :
    PathP
      ( λ i → IsPremetric (≈≡ i))
      ( isPremetricᶠ ℝArchimedeanField)
      ( PremetricStr.isPremetric (snd ℝPremetricSpace))
  isPremetric≡ = isProp→PathP (λ i → isPropIsPremetric (≈≡ i)) _ _

isCauchyCompleteℝ : IsCauchyComplete ℝArchimedeanField
isCauchyCompleteℝ =
  subst PremetricTheory.isComplete (sym inducedPremetricSpaceℝ≡) isCompleteℝ
