module HoTTReals.Data.Real.Algebra.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Categories.Limits.Initial

open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Categories.Instances.CauchyCompleteArchimedeanFields
open import HoTTReals.Data.Real.Algebra.ArchimedeanField
open import HoTTReals.Data.Real.Algebra.OrderedField
open import HoTTReals.Relation.Premetric.Instances.ArchimedeanField

private
  variable
    ℓ ℓ' : Level

isContrOrderedFieldHomℝ :
  (F : OrderedField ℓ ℓ') → IsCauchyCompleteArchimedeanOrderedField F →
  isContr
    ( OrderedCommRingMono
      ( OrderedField→OrderedCommRing ℝOrderedField)
      ( OrderedField→OrderedCommRing F))
isContrOrderedFieldHomℝ F isCauchyCompleteArchimedeanOrderedField = {!!}

isInitialℝ :
  isInitial
    ( CauchyCompleteArchimedeanFieldsCategory {ℓ-zero} {ℓ-zero})
    ( ℝOrderedField , isCauchyCompleteArchimedeanOrderedFieldℝ)
isInitialℝ (F , isCauchyCompleteArchimedeanOrderedField) =
  isContrOrderedFieldHomℝ F isCauchyCompleteArchimedeanOrderedField
