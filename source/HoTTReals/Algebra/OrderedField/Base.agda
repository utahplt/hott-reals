-- Vendored from LorenzoMolena/cubical algebraic-structures-wip ee4207d0,
-- Cubical/Algebra/OrderedField/Base.agda, on 2026-09-08. Edited: no.
module HoTTReals.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommRing
open import HoTTReals.Algebra.HeytingField.Base
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

{-
-- ??
module _ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {B : Type ℓB} where
  IsOrderedFieldHom : (OrderedFieldStr ℓA' A) → (A → B) → (OrderedFieldStr ℓB' B) → Type _
  IsOrderedFieldHom F f K = IsOrderedCommRingHom
    (snd (OrderedField→OrderedCommRing (_ , F)))
    f
    (snd (OrderedField→OrderedCommRing (_ , K)))

-- record IsOrderedFieldHom {A : Type ℓ} {B : Type ℓ'}
--   (F : OrderedFieldStr ℓ<≤ A)
--   (f : A → B)
--   (K : OrderedFieldStr ℓ<≤' B)
--   : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ<≤ ℓ<≤')))
--   where
--   no-eta-equality
--   private
--     module F = OrderedFieldStr F
--     module K = OrderedFieldStr K
--     Focring = str (OrderedField→OrderedCommRing (_ , F))
--     Kocring = str (OrderedField→OrderedCommRing (_ , K))
--
--   field
--     isOrderedCommRingHom : IsOrderedCommRingHom Focring f Kocring
--
--   open IsOrderedCommRingHom isOrderedCommRingHom public

-- OrderedFieldHom : OrderedField ℓ ℓ<≤ → OrderedField ℓ' ℓ<≤' → Type _
-- OrderedFieldHom F K = Σ[ f ∈ (⟨ F ⟩ → ⟨ K ⟩) ] IsOrderedFieldHom (F .snd) f (K .snd)
OrderedFieldHom : OrderedField ℓ ℓ<≤ → OrderedField ℓ' ℓ<≤' → Type _
OrderedFieldHom F K =
  OrderedCommRingHom (OrderedField→OrderedCommRing F) (OrderedField→OrderedCommRing K)

module _ {A : OrderedField ℓ ℓ<≤} {B : OrderedField ℓ' ℓ<≤'} where

  open IsOrderedCommRingMono

  private
    A' = OrderedField→OrderedCommRing A
    B' = OrderedField→OrderedCommRing B

  OrderedFieldHom→OrderedCommRingHom : OrderedFieldHom A B → OrderedCommRingHom A' B'
  fst (OrderedFieldHom→OrderedCommRingHom f) = fst f
  snd (OrderedFieldHom→OrderedCommRingHom f) = snd f
    -- isOrderedCommRingHom
    -- where open IsOrderedFieldHom (snd f)

  OrderedFieldHom→OrderedCommRingMono : OrderedFieldHom A B → OrderedCommRingMono A' B'
  fst (OrderedFieldHom→OrderedCommRingMono f) = fst f
  snd (OrderedFieldHom→OrderedCommRingMono f) .isOrderedCommRingHom = snd f
  snd (OrderedFieldHom→OrderedCommRingMono f) .pres< x y x<y = {!   !}
  -- x<y → 0<y-x → Σ z = (y-x)⁻¹
  -- 1 = f 1 = f ((y-x) · z) = f (y - x) · f z
  -- → Σ w = (f y - f x)⁻¹
  -- → (f y - f x)⁻¹ # 0
  -- 1) 0 < f y - f x → f x < f y
  -- 2) f y - f x < 0 → f y < f x
  --    → y < x ⇒⇐
    -- where open IsOrderedFieldHom (snd f)
-- -}
