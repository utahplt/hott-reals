module HoTTReals.Categories.Instances.CauchyCompleteArchimedeanFields where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.FullSubcategory

open import HoTTReals.Categories.Instances.OrderedFields
open import HoTTReals.Relation.Premetric.Instances.ArchimedeanField

private
  variable
    ℓ ℓ' : Level

CauchyCompleteArchimedeanFieldsCategory :
  Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
CauchyCompleteArchimedeanFieldsCategory {ℓ} {ℓ'} =
  FullSubcategory
    ( OrderedFieldsCategory {ℓ} {ℓ'})
    ( IsCauchyCompleteArchimedeanOrderedField)
