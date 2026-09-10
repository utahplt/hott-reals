-- Vendored from LorenzoMolena/cubical algebraic-structures-wip ee4207d0,
-- Cubical/Algebra/OrderedField/Base.agda, on 2026-09-08. Edited: no.
module HoTTReals.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommRing
open import HoTTReals.Algebra.HeytingField.Base
open import HoTTReals.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Morphisms

import HoTTReals.Algebra.OrderedCommRing.Properties as
  HoTTRealsOrderedCommRingProperties

open import Cubical.Data.Sum as ⊎

open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ<≤ ℓ<≤' : Level

record IsOrderedField
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_<_ _≤_ : F → F → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isorderedfield
  field
    isOrderedCommRing   : IsOrderedCommRing 0f 1f _+_ _·_ -_ _<_ _≤_
    #0→isInv            : ∀ x → (x < 0f) ⊎ (0f < x) → Σ[ y ∈ F ] x · y ≡ 1f
    isInv→#0            : ∀ x y → x · y ≡ 1f → (x < 0f) ⊎ (0f < x)

  open IsOrderedCommRing isOrderedCommRing public

record OrderedFieldStr (ℓ' : Level) (F : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedfieldstr
  field
    0f 1f : F
    _+_ _·_ : F → F → F
    -_ : F → F
    _<_ _≤_ : F → F → Type ℓ'
    isOrderedField : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_

  open IsOrderedField isOrderedField public

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix  4 _<_ _≤_

OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' = TypeWithStr ℓ (OrderedFieldStr ℓ')

OrderedField→OrderedCommRing : OrderedField ℓ ℓ' → OrderedCommRing ℓ ℓ'
OrderedField→OrderedCommRing F .fst = F . fst
OrderedField→OrderedCommRing F .snd = orderedcommringstr _ _ _ _ _ _ _ isOrderedCommRing
  where open OrderedFieldStr (snd F)

OrderedField→Apartness : OrderedField ℓ ℓ' → Apartness ℓ ℓ'
OrderedField→Apartness = OrderedCommRing→Apartness ∘ OrderedField→OrderedCommRing

-- The naïve definition of "OCR + invertible iff apart from zero",
-- with apartness derived from the stric order, is sufficient to satisfy
-- the conditions of Anshwad10's presentation of Heyting Fields.
-- TO DO: show that `·CancelR<` is derivable, and that such presentation satisfies
-- all the axioms in the HoTT book / A. Booij PhD Thesis definition of Ordered Field.
OrderedField→HeytingField : OrderedField ℓ ℓ' → HeytingField ℓ ℓ'
fst (OrderedField→HeytingField F) = fst F
snd (OrderedField→HeytingField F) = heytingfieldstr _ _ _ _ _ _ isHF where
  open IsHeytingField
  module F where
    open OrderedFieldStr (str F) public
    open ApartnessStr (str (OrderedField→Apartness F)) public
    open OrderedCommRingTheory (OrderedField→OrderedCommRing F) hiding (_#_) public
    open HoTTRealsOrderedCommRingProperties.OrderedCommRingTheory
      (OrderedField→OrderedCommRing F) using (isTight#) public

  isHF : IsHeytingField F.0f F.1f F._+_ F._·_ F.-_ F._#_
  isHF .isCommRing  = F.isCommRing
  isHF .isApartness = F.isApartness
  isHF .isTight     = F.isTight#
  isHF .+Respect#R  = λ x y z → ⊎.map (F.+MonoR< x y z) (F.+MonoR< y x z)
  isHF .#0→isInv    = F.#0→isInv
  isHF .isInv→#0    = F.isInv→#0

module _ {A : Type ℓ} {B : Type ℓ'} where
  IsOrderedFieldHom : OrderedFieldStr ℓ<≤ A → (A → B) → OrderedFieldStr ℓ<≤' B → Type _
  IsOrderedFieldHom F f K = IsOrderedCommRingMono
    (snd (OrderedField→OrderedCommRing (_ , F)))
    f
    (snd (OrderedField→OrderedCommRing (_ , K)))

OrderedFieldHom : OrderedField ℓ ℓ<≤ → OrderedField ℓ' ℓ<≤' → Type _
OrderedFieldHom F K = Σ[ f ∈ (⟨ F ⟩ → ⟨ K ⟩) ] IsOrderedFieldHom (F .snd) f (K .snd)

module _
  {ℓ ℓ' ℓ'' ℓ<≤ ℓ<≤' ℓ<≤'' : Level}
  {F : OrderedField ℓ ℓ<≤} {K : OrderedField ℓ' ℓ<≤'} {H : OrderedField ℓ'' ℓ<≤''}
  where
  _∘of_ : OrderedFieldHom K H → OrderedFieldHom F K → OrderedFieldHom F H
  _∘of_ = flip compOrderedCommRingMono
