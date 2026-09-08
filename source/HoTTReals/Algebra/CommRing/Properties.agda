-- Vendored from LorenzoMolena/cubical algebraic-structures-wip ee4207d0,
-- the Units hunk of Cubical/Algebra/CommRing/Properties.agda, on 2026-09-08.
-- Edited: no.
module HoTTReals.Algebra.CommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing.Base
import Cubical.Algebra.CommRing.Properties as CubicalCommRingProperties
open import Cubical.Algebra.Ring

private
  variable
    ℓ : Level

module Units (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open CubicalCommRingProperties.Units R'
 private R = fst R'

 _/_ : (x y : R) → ⦃ y ∈ Rˣ ⦄ → R
 _/_ x y = x · y ⁻¹

 infixl 9 _/_

 divideMultiply : ∀ x y ⦃ _ : y ∈ Rˣ ⦄ → x / y · y ≡ x
 divideMultiply x y = sym (·Assoc x _ _) ∙∙ congR _·_ (·-linv y) ∙∙ ·IdR x

 multiplyDivide : ∀ x y ⦃ _ : y ∈ Rˣ ⦄ → (x · y) / y ≡ x
 multiplyDivide x y = sym (·Assoc x _ _) ∙∙ congR _·_ (·-rinv y) ∙∙ ·IdR x

 ⁻¹-eq-elim' : {r r' r'' : R} ⦃ r∈Rˣ : r ∈ Rˣ ⦄ → r' ≡ r · r'' → r' · r ⁻¹ ≡ r''
 ⁻¹-eq-elim' = ⁻¹-eq-elim ∘ (_∙ ·Comm _ _)

 ⁻¹≡ : {r r' : R} → ⦃ r∈Rˣ : r ∈ Rˣ ⦄ → r · r' ≡ 1r → r ⁻¹ ≡ r'
 ⁻¹≡ ⦃ r∈Rˣ ⦄ rr'≡1 = cong fst (inverseUniqueness _ r∈Rˣ (_ , rr'≡1))

 isInvol⁻¹ : (r : R) → ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r⁻¹∈Rˣ : r ⁻¹ ∈ Rˣ ⦄ → r ⁻¹ ⁻¹ ≡ r
 isInvol⁻¹ r = ⁻¹≡ (·-linv r)

 cross-multiply : ∀ {r r' r'' r'''} ⦃ r''∈Rˣ : r'' ∈ Rˣ ⦄ ⦃ r'''∈Rˣ : r''' ∈ Rˣ ⦄
                 → r'' · r' ≡ r''' · r → r / r'' ≡ r' / r'''
 cross-multiply = ⁻¹-eq-elim' ∘ sym ∘ (·Assoc _ _ _ ∙_) ∘ ⁻¹-eq-elim'
