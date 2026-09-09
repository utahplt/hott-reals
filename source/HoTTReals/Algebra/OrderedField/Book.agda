module HoTTReals.Algebra.OrderedField.Book where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base
import Cubical.Algebra.OrderedCommRing.Properties as
  CubicalOrderedCommRingProperties

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

import Cubical.Functions.Logic as L

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Order.Apartness.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties using
  ( isPoset→isProset)
open import Cubical.Relation.Binary.Order.Proset.Properties using
  ( isMeet ; isJoin)
open import Cubical.Relation.Binary.Order.Pseudolattice.Base
open import Cubical.Relation.Binary.Order.StrictOrder.Base
open import Cubical.Relation.Binary.Order.StrictOrder.Properties
open import Cubical.Relation.Nullary

open import HoTTReals.Algebra.OrderedAbGroup.Base
import HoTTReals.Algebra.OrderedAbGroup.Properties as OrderedAbGroupProperties
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Algebra.OrderedField.Properties

private
  variable
    ℓ ℓ' : Level

record IsOrderedFieldBook
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ : F → F → F)
  (-_ : F → F)
  (_·_ : F → F → F)
  (min max : F → F → F)
  (_≤_ _<_ _#_ : F → F → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isorderedfieldbook
  field
    isCommRing : IsCommRing 0f 1f _+_ _·_ -_
    isInv≃#0 : (x : F) → (Σ[ y ∈ F ] x · y ≡ 1f) ≃ (x # 0f)
    isPoset : IsPoset _≤_
    isMeetMin : (x y : F) → isMeet (isPoset→isProset isPoset) x y (min x y)
    isJoinMax : (x y : F) → isJoin (isPoset→isProset isPoset) x y (max x y)
    isStrictOrder : IsStrictOrder _<_
    isApartness : IsApartness _#_
    ≤≃¬> : (x y : F) → (x ≤ y) ≃ (¬ (y < x))
    #≃<∨> : (x y : F) → (x # y) ≃ ((x < y) L.⊔′ (y < x))
    ≤≃+≤ : (x y z : F) → (x ≤ y) ≃ ((x + z) ≤ (y + z))
    <≃+< : (x y z : F) → (x < y) ≃ ((x + z) < (y + z))
    posSum→pos∨pos : (x y : F) → 0f < (x + y) → (0f < x) L.⊔′ (0f < y)
    <-≤-trans : (x y z : F) → x < y → y ≤ z → x < z
    ≤-<-trans : (x y z : F) → x ≤ y → y < z → x < z
    ·MonoR≤ : (x y z : F) → x ≤ y → 0f ≤ z → (x · z) ≤ (y · z)
    0<→<≃·< : (x y z : F) → 0f < z → (x < y) ≃ ((x · z) < (y · z))
    0<1 : 0f < 1f

  open IsCommRing isCommRing public
  open IsPoset isPoset hiding (is-set) renaming
    ( is-prop-valued to is-prop-valued≤ ; is-trans to is-trans≤)
    public
  open IsStrictOrder isStrictOrder hiding (is-set) renaming
    ( is-prop-valued to is-prop-valued< ; is-trans to is-trans<)
    public
  open IsApartness isApartness hiding (is-set) renaming
    ( is-prop-valued to is-prop-valued# ; is-irrefl to is-irrefl#)
    public

module _ {F : Type ℓ} {_<_ : F → F → Type ℓ'}
  (isStrictOrder : IsStrictOrder _<_) where

  <∨>≃<⊎> : (x y : F) → ((x < y) L.⊔′ (y < x)) ≃ ((x < y) ⊎ (y < x))
  <∨>≃<⊎> x y =
    propTruncIdempotent≃
      ( IsApartness.is-prop-valued
        ( isStrictOrder→isApartnessSymClosure isStrictOrder) x y)

module _ {F : Type ℓ} {0f 1f : F} {_+_ _·_ : F → F → F} { -_ : F → F}
  {_<_ _≤_ : F → F → Type ℓ'}
  (f : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_) where

  open IsOrderedField f

  private
    FOrderedAbGroup : OrderedAbGroup ℓ ℓ'
    FOrderedAbGroup =
      OrderedCommRing→OrderedAbGroup
        ( _ , orderedcommringstr _ _ _ _ _ _ _ isOrderedCommRing)

    FOrderedField : OrderedField ℓ ℓ'
    FOrderedField = _ , orderedfieldstr _ _ _ _ _ _ _ f

  open OrderedAbGroupProperties.OrderedAbGroupTheory FOrderedAbGroup using
    ( +CancelR≤ ; +CancelR<)
  open OrderedFieldTheory FOrderedField using (·CancelR<)

  IsOrderedField→IsOrderedFieldBook :
    IsOrderedFieldBook 0f 1f _+_ -_ _·_ _⊓_ _⊔_ _≤_ _<_
      ( λ x y → (x < y) ⊎ (y < x))
  IsOrderedFieldBook.isCommRing IsOrderedField→IsOrderedFieldBook = isCommRing
  IsOrderedFieldBook.isInv≃#0 IsOrderedField→IsOrderedFieldBook =
    λ x →
      propBiimpl→Equiv
        ( Units.inverseUniqueness (_ , commringstr _ _ _ _ _ isCommRing) x)
        ( IsApartness.is-prop-valued
          ( isStrictOrder→isApartnessSymClosure isStrictOrder) x 0f)
        ( uncurry $ isInv→#0 x)
        ( #0→isInv x)
  IsOrderedFieldBook.isPoset IsOrderedField→IsOrderedFieldBook = isPoset
  IsOrderedFieldBook.isMeetMin IsOrderedField→IsOrderedFieldBook =
    λ x y → is-pseudolattice .fst x y .snd
  IsOrderedFieldBook.isJoinMax IsOrderedField→IsOrderedFieldBook =
    λ x y → is-pseudolattice .snd x y .snd
  IsOrderedFieldBook.isStrictOrder IsOrderedField→IsOrderedFieldBook =
    isStrictOrder
  IsOrderedFieldBook.isApartness IsOrderedField→IsOrderedFieldBook =
    isStrictOrder→isApartnessSymClosure isStrictOrder
  IsOrderedFieldBook.≤≃¬> IsOrderedField→IsOrderedFieldBook = ≤≃¬>
  IsOrderedFieldBook.#≃<∨> IsOrderedField→IsOrderedFieldBook =
    λ x y → invEquiv $ <∨>≃<⊎> isStrictOrder x y
  IsOrderedFieldBook.≤≃+≤ IsOrderedField→IsOrderedFieldBook =
    λ x y z →
      propBiimpl→Equiv
        ( is-prop-valued≤ x y)
        ( is-prop-valued≤ (x + z) (y + z))
        ( +MonoR≤ x y z)
        ( +CancelR≤)
  IsOrderedFieldBook.<≃+< IsOrderedField→IsOrderedFieldBook =
    λ x y z →
      propBiimpl→Equiv
        ( is-prop-valued< x y)
        ( is-prop-valued< (x + z) (y + z))
        ( +MonoR< x y z)
        ( +CancelR<)
  IsOrderedFieldBook.posSum→pos∨pos IsOrderedField→IsOrderedFieldBook =
    posSum→pos∨pos
  IsOrderedFieldBook.<-≤-trans IsOrderedField→IsOrderedFieldBook = <-≤-trans
  IsOrderedFieldBook.≤-<-trans IsOrderedField→IsOrderedFieldBook = ≤-<-trans
  IsOrderedFieldBook.·MonoR≤ IsOrderedField→IsOrderedFieldBook =
    λ x y z x≤y 0≤z → ·MonoR≤ x y z 0≤z x≤y
  IsOrderedFieldBook.0<→<≃·< IsOrderedField→IsOrderedFieldBook =
    λ x y z 0<z →
      propBiimpl→Equiv
        ( is-prop-valued< x y)
        ( is-prop-valued< (x · z) (y · z))
        ( ·MonoR< x y z 0<z)
        ( ·CancelR< x y z 0<z)
  IsOrderedFieldBook.0<1 IsOrderedField→IsOrderedFieldBook = 0<1

module _ {F : Type ℓ} {0f 1f : F} {_+_ : F → F → F} { -_ : F → F}
  {_·_ : F → F → F} {min max : F → F → F} {_≤_ _<_ _#_ : F → F → Type ℓ'}
  (b : IsOrderedFieldBook 0f 1f _+_ -_ _·_ min max _≤_ _<_ _#_) where

  open IsOrderedFieldBook b

  <-≤-weaken : (x y : F) → x < y → x ≤ y
  <-≤-weaken x y x<y = invEq (≤≃¬> x y) (is-asym x y x<y)

  IsOrderedFieldBook→IsOrderedField : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_
  IsOrderedField.isOrderedCommRing IsOrderedFieldBook→IsOrderedField =
    isOrderedCommRingBook
    where
    isOrderedCommRingBook : IsOrderedCommRing 0f 1f _+_ _·_ -_ _<_ _≤_
    IsOrderedCommRing.isCommRing isOrderedCommRingBook = isCommRing
    IsOrderedCommRing.isPseudolattice isOrderedCommRingBook =
      ispseudolattice isPoset
        ( (λ x y → min x y , isMeetMin x y) ,
          (λ x y → max x y , isJoinMax x y))
    IsOrderedCommRing.isStrictOrder isOrderedCommRingBook = isStrictOrder
    IsOrderedCommRing.<-≤-weaken isOrderedCommRingBook = <-≤-weaken
    IsOrderedCommRing.≤≃¬> isOrderedCommRingBook = ≤≃¬>
    IsOrderedCommRing.+MonoR≤ isOrderedCommRingBook =
      λ x y z → equivFun $ ≤≃+≤ x y z
    IsOrderedCommRing.+MonoR< isOrderedCommRingBook =
      λ x y z → equivFun $ <≃+< x y z
    IsOrderedCommRing.posSum→pos∨pos isOrderedCommRingBook = posSum→pos∨pos
    IsOrderedCommRing.<-≤-trans isOrderedCommRingBook = <-≤-trans
    IsOrderedCommRing.≤-<-trans isOrderedCommRingBook = ≤-<-trans
    IsOrderedCommRing.·MonoR≤ isOrderedCommRingBook =
      λ x y z 0≤z x≤y → ·MonoR≤ x y z x≤y 0≤z
    IsOrderedCommRing.·MonoR< isOrderedCommRingBook =
      λ x y z 0<z → equivFun $ 0<→<≃·< x y z 0<z
    IsOrderedCommRing.0<1 isOrderedCommRingBook = 0<1
  IsOrderedField.#0→isInv IsOrderedFieldBook→IsOrderedField =
    λ x x#0 → invEq (isInv≃#0 x) (invEq (#≃<∨> x 0f) ∣ x#0 ∣₁)
  IsOrderedField.isInv→#0 IsOrderedFieldBook→IsOrderedField =
    λ x y xy≡1 →
      equivFun (<∨>≃<⊎> isStrictOrder x 0f)
        ( equivFun (#≃<∨> x 0f) (equivFun (isInv≃#0 x) (y , xy≡1)))
