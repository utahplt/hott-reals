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
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals as ℝ hiding (
  _+_ ; -_)

open import HoTTReals.Algebra.ArchimedeanField.Base
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Data.Real.Algebra.Addition as ℝ
open import HoTTReals.Data.Real.Algebra.Multiplication as ℝ hiding (_·_)
open import HoTTReals.Data.Real.Algebra.OrderedCommRing as ℝ
open import HoTTReals.Data.Real.Algebra.OrderedField as ℝ
open import HoTTReals.Data.Real.Order.Base as ℝ hiding (_<_ ; _≤_)
open import HoTTReals.Data.Real.Order.Magnitude as ℝ
open import HoTTReals.Relation.Premetric.Instances.ArchimedeanField

open ArchimedeanFieldStr

ℝArchimedeanField : ArchimedeanField ℓ-zero ℓ-zero
fst ℝArchimedeanField = ℝ
0f  (snd ℝArchimedeanField) = 0
1f  (snd ℝArchimedeanField) = 1
_+_ (snd ℝArchimedeanField) = ℝ._+_
_·_ (snd ℝArchimedeanField) = ℝ._·_
-_  (snd ℝArchimedeanField) = ℝ.-_
_<_ (snd ℝArchimedeanField) = ℝ._<_
_≤_ (snd ℝArchimedeanField) = ℝ._≤_
ι   (snd ℝArchimedeanField) = ℝ.rat
isArchimedeanField (snd ℝArchimedeanField) = isArchimedeanFieldℝ
  where
  open IsArchimedeanField
  open OrderedFieldStr (snd ℝOrderedField) renaming (isOrderedField to isOFℝ)

  isArchimedeanFieldℝ : IsArchimedeanField _ _ _ _ _ _ _ _
  isArchimedeanFieldℝ .isOrderedField      = isOFℝ
  isArchimedeanFieldℝ .isOrderedFieldHom   = snd ratᶠ
  isArchimedeanFieldℝ .archimedeanProperty = ℝ.isArchimedean<

inducedPremetricSpaceℝ≡ :
  ArchimedeanField→PremetricSpace ℝArchimedeanField ≡ ℝPremetricSpace
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

isCauchyCompleteArchimedeanOrderedFieldℝ :
  IsCauchyCompleteArchimedeanOrderedField ℝOrderedField
isCauchyCompleteArchimedeanOrderedFieldℝ =
  ( rat
  , ArchimedeanFieldStr.isOrderedFieldHom (snd ℝArchimedeanField)
  , isArchimedean<)
  , isCauchyCompleteℝ
