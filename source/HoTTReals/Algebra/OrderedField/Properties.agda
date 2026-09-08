-- Vendored from LorenzoMolena/cubical algebraic-structures-wip ee4207d0,
-- Cubical/Algebra/OrderedField/Properties.agda, on 2026-09-08. Edited: no.
module HoTTReals.Algebra.OrderedField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import HoTTReals.Algebra.HeytingField.Base
open import HoTTReals.Algebra.HeytingField.Properties
open import Cubical.Algebra.OrderedCommRing as OCR hiding (module Positive)
open import HoTTReals.Algebra.OrderedField.Base
open import Cubical.Algebra.Ring

import HoTTReals.Algebra.OrderedCommRing.Properties as
  HoTTRealsOrderedCommRingProperties

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.Fast.Int.Base as ℤ
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_ ; _-_ to _-ℤ_)
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Sum

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level

OrderedField→StrictOrder : OrderedField ℓ ℓ' → StrictOrder ℓ ℓ'
OrderedField→StrictOrder = OrderedCommRing→StrictOrder ∘ OrderedField→OrderedCommRing

OrderedField→CommRing : OrderedField ℓ ℓ' → CommRing ℓ
OrderedField→CommRing = OrderedCommRing→CommRing ∘ OrderedField→OrderedCommRing

OrderedField→Ring : OrderedField ℓ ℓ' → Ring ℓ
OrderedField→Ring = OrderedCommRing→Ring ∘ OrderedField→OrderedCommRing

OrderedField→PseudoLattice : OrderedField ℓ ℓ' → Pseudolattice ℓ ℓ'
OrderedField→PseudoLattice = OrderedCommRing→PseudoLattice ∘ OrderedField→OrderedCommRing

OrderedField→Poset : OrderedField ℓ ℓ' → Poset ℓ ℓ'
OrderedField→Poset = OrderedCommRing→Poset ∘ OrderedField→OrderedCommRing

OrderedField→Quoset : OrderedField ℓ ℓ' → Quoset ℓ ℓ'
OrderedField→Quoset = OrderedCommRing→Quoset ∘ OrderedField→OrderedCommRing

module _ (F' : OrderedField ℓ ℓ') where
  private
    F = fst F'
    FOCR = OrderedField→OrderedCommRing F'
    FCR  = OrderedField→CommRing F'

  -- open RingTheory (OrderedField→Ring F')
  -- open HeytingFieldStr (snd ?)
  -- open OrderedFieldStr (snd F')

  -- open HeytingFieldStr (snd (OrderedField→HeytingField F')) using (_[_]⁻¹)
  open module OrderedFieldReasoning = OrderedCommRingReasoning FOCR

  open OrderedFieldStr (snd F')
  open HeytingFieldStr (snd (OrderedField→HeytingField F')) using (_#_)

  module OrderedFieldTheory where
    open OrderedCommRingTheory FOCR hiding (_#_) public
    open FieldTheory (OrderedField→HeytingField F') public
    open Exponentiation FCR

    0<→∈Fˣ : {x : F} {0< : 0f < x} → x ∈ Fˣ
    0<→∈Fˣ {x} {0<} = #0→isInv x (inr 0<)

    0<→0<⁻¹ : (x : F) → 0f < x → ⦃ _ : x # 0f ⦄ → 0f < x ⁻¹
    0<→0<⁻¹ x 0<x with uncurry (isInv→#0 (x ⁻¹)) (RˣInvClosed x)
    ... | inl x⁻¹<0 = ⊥.rec $ is-asym 0f 1f 0<1 $
      subst2 _<_ (·-rinv x) (0RightAnnihilates x) ([ x , 0<x ]·< x⁻¹<0)
    ... | inr 0<x⁻¹ = 0<x⁻¹

    <0→⁻¹<0 : (x : F) → x < 0f → ⦃ _ : x # 0f ⦄ → x ⁻¹ < 0f
    <0→⁻¹<0 x x<0 with uncurry (isInv→#0 (x ⁻¹)) (RˣInvClosed x)
    ... | inl x⁻¹<0 = x⁻¹<0
    ... | inr 0<x⁻¹ = ⊥.rec $ is-asym (- 1f) 0f (0<→-<0 1f 0<1) $
      subst2 _<_ (0RightAnnihilates (- x)) (-DistL· x (x ⁻¹) ∙ cong -_ (·-rinv x))
        ([ - x , <0→0<- x x<0 ]·< 0<x⁻¹)

    ·CancelR< : ∀ x y z → 0f < z → x · z < y · z → x < y
    ·CancelR< x y z 0<z = let instance z#0 = inr 0<z in
        subst2 _<_ (multiplyDivide x z) (multiplyDivide y z)
      ∘ ·MonoR< _ _ (z ⁻¹) (0<→0<⁻¹ z 0<z)

    ·CancelL< : ∀ x y z → 0f < z → z · x < z · y → x < y
    ·CancelL< x y z 0<z = ·CancelR< x y z 0<z ∘ subst2 _<_ (·Comm _ _) (·Comm _ _)

    0<→⁻¹Flip< : (x y : F) ⦃ _ : x # 0f ⦄ ⦃ _ : y # 0f ⦄ → 0f < x → x < y → y ⁻¹ < x ⁻¹
    0<→⁻¹Flip< x y 0<x x<y = ·CancelL< _ _ (x · y)
      (subst (_< _) (0LeftAnnihilates y) (·MonoR< _ _ _ (is-trans< _ _ _ 0<x x<y) 0<x))
      (subst2 _<_ (sym (·R/ x y)) (sym (·L/ x y)) x<y)

    0<→⁻¹Flip<' : (x y : F) ⦃ _ : x # 0f ⦄ ⦃ _ : y # 0f ⦄ → 0f < y → y ⁻¹ < x ⁻¹ → x < y
    0<→⁻¹Flip<' x y 0<y y⁻¹<x⁻¹ = subst2 _<_
      (isInvol⁻¹ x ⦃ r⁻¹∈Rˣ = #0→isInv (x ⁻¹) (x ⁻¹#0) ⦄)
      (isInvol⁻¹ y ⦃ r⁻¹∈Rˣ = #0→isInv (y ⁻¹) (y ⁻¹#0) ⦄)
      (0<→⁻¹Flip< _ _ ⦃ y ⁻¹#0 ⦄ ⦃ x ⁻¹#0 ⦄ (0<→0<⁻¹ y 0<y) y⁻¹<x⁻¹)

  open OrderedFieldTheory

  module Positive
    (0<+Closed : (x y : F) → 0f < x → 0f < y → 0f < x + y)
    (0<·Closed : (x y : F) → 0f < x → 0f < y → 0f < x · y)
    where

    open OCR.Positive FOCR 0<+Closed 0<·Closed public renaming (
      R₊ to F₊ ; isSetR₊ to isSetF₊ ; ≡₊→R₊ to ≡₊→F₊)
    open HoTTRealsOrderedCommRingProperties.Positive FOCR 0<+Closed 0<·Closed
      public

    instance
      ₊→#0 : {y : F₊} → ⟨ y ⟩₊ # 0f
      ₊→#0 {y} = inr (snd y)

    _⁻¹₊ : F₊ → F₊
    fst (y ⁻¹₊) = ⟨ y ⟩₊ ⁻¹
    snd (y ⁻¹₊) = 0<→0<⁻¹ ⟨ y ⟩₊ (snd y) ⦃ inr (snd y) ⦄

    _/₊_ : F → F₊ → F
    x /₊ y = x · ⟨ y ⁻¹₊ ⟩₊

    _₊/₊_ : F₊ → F₊ → F₊
    x ₊/₊ y = x ·₊ y ⁻¹₊

    infix 9 _⁻¹₊
    infixl 9 _/₊_ _₊/₊_

    /₊· : ∀ x y → x /₊ y · ⟨ y ⟩₊ ≡ x
    /₊· x y = divideMultiply x ⟨ y ⟩₊

    ₊/₊· : ∀ x y → ⟨ x ₊/₊ y ⟩₊ · ⟨ y ⟩₊ ≡ ⟨ x ⟩₊
    ₊/₊· x y = divideMultiply ⟨ x ⟩₊ ⟨ y ⟩₊

    ⁻¹Flip<₊ : ∀ x y → x <₊ y → y ⁻¹₊ <₊ x ⁻¹₊
    ⁻¹Flip<₊ x y = 0<→⁻¹Flip< ⟨ x ⟩₊ ⟨ y ⟩₊ (snd x)

    ⁻¹Flip<₊' : ∀ x y → y ⁻¹₊ <₊ x ⁻¹₊ → x <₊ y
    ⁻¹Flip<₊' x y = 0<→⁻¹Flip<' ⟨ x ⟩₊ ⟨ y ⟩₊ (snd y)

    <₊1→1<₊⁻¹ : ∀ x → x <₊ 1₊ → 1₊ <₊ x ⁻¹₊
    <₊1→1<₊⁻¹ x = subst (_< ⟨ x ⁻¹₊ ⟩₊) (1⁻¹≡1 ⦃ 0<→∈Fˣ ⦄) ∘ ⁻¹Flip<₊ x 1₊

    ₊^∘⁻¹₊≡⁻¹₊∘₊^ : ∀ x n → ⟨ (x ⁻¹₊) ₊^ n ⟩₊ ≡ ⟨ (x ₊^ n) ⁻¹₊ ⟩₊
    ₊^∘⁻¹₊≡⁻¹₊∘₊^ x zero    = sym $ 1⁻¹≡1 ⦃ 0<→∈Fˣ ⦄
    ₊^∘⁻¹₊≡⁻¹₊∘₊^ x (suc n) =
      let
        x⁻¹ = x ⁻¹₊ ; _ⁿ = ⟨_⟩₊ ∘ (_₊^ n) ; _¹⁺ⁿ = ⟨_⟩₊ ∘ (_₊^ suc n)
      in
        sym $ ⁻¹≡ $
        x ¹⁺ⁿ · x⁻¹ ¹⁺ⁿ                  ≡⟨⟩
        ⟨ x ⟩₊ · x ⁿ · (⟨ x⁻¹ ⟩₊ · x⁻¹ ⁿ) ≡⟨ solve! FCR ⟩
        ⟨ x ⟩₊ · ⟨ x⁻¹ ⟩₊ · (x ⁿ · x⁻¹ ⁿ) ≡⟨ congL _·_ (·-rinv ⟨ x ⟩₊) ∙ ·IdL _ ⟩
        x ⁿ · x⁻¹ ⁿ                      ≡⟨ congR _·_ (₊^∘⁻¹₊≡⁻¹₊∘₊^ x n) ⟩
        x ⁿ · ⟨ (x ₊^ n) ⁻¹₊ ⟩₊           ≡⟨ ·-rinv (x ⁿ) ⟩
        1f                               ∎
