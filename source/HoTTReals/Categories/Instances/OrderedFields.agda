module HoTTReals.Categories.Instances.OrderedFields where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Categories.Category.Base

open import HoTTReals.Algebra.OrderedCommRing.Morphisms
open import HoTTReals.Algebra.OrderedField.Base

private
  variable
    ℓ ℓ' : Level

open Category

OrderedFieldsCategory : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
ob (OrderedFieldsCategory {ℓ} {ℓ'}) = OrderedField ℓ ℓ'
Hom[_,_] (OrderedFieldsCategory {ℓ} {ℓ'}) F K =
  OrderedCommRingMono
    ( OrderedField→OrderedCommRing F)
    ( OrderedField→OrderedCommRing K)
id (OrderedFieldsCategory {ℓ} {ℓ'}) {F} =
  idOrderedCommRingMono (OrderedField→OrderedCommRing F)
_⋆_ (OrderedFieldsCategory {ℓ} {ℓ'}) = compOrderedCommRingMono
⋆IdL (OrderedFieldsCategory {ℓ} {ℓ'}) = compIdOrderedCommRingMono
⋆IdR (OrderedFieldsCategory {ℓ} {ℓ'}) = idCompOrderedCommRingMono
⋆Assoc (OrderedFieldsCategory {ℓ} {ℓ'}) = compAssocOrderedCommRingMono
isSetHom (OrderedFieldsCategory {ℓ} {ℓ'}) {F} {K} =
  isSetOrderedCommRingMono
    ( OrderedField→OrderedCommRing F)
    ( OrderedField→OrderedCommRing K)
