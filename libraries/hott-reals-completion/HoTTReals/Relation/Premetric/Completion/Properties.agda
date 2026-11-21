{-
  This module prove that ℭM is a Cauchy-complete premetric space, following
  Formalising real numbers in homotopy type theory, Gaëtan Gilbert, 2017
-}
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric

-- we use this combinations of levels to avoid using `Lift`s when not needed
module HoTTReals.Relation.Premetric.Completion.Properties {ℓ} ℓ'
  (M : PremetricSpace ℓ (ℓ-max ℓ ℓ')) where

open import Cubical.Foundations.Function
open import HoTTReals.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals renaming (ℚCommRing to ℚCR)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Functions.Embedding

open import Cubical.Relation.Binary.Properties
open import Cubical.Relation.Premetric.Mappings
open import HoTTReals.Relation.Premetric.Completion.Base M renaming (ℭ to ℭM)
open import HoTTReals.Relation.Premetric.Completion.Closeness ℓ' M
open import HoTTReals.Relation.Premetric.Completion.Elim M as E
open E public using (isSym∼)

open import Cubical.Tactics.CommRingSolver

open 1/2∈ℚ
open PremetricStr (snd M)
open PremetricTheory

private
  ℓ'' = ℓ-max ℓ ℓ'

  module _ (R : CommRing ℓ-zero) where
    open CommRingStr (snd R) using () renaming (_+_ to _+r_)
    opaque
      lemma : ∀ η/4 δ ε →
        (η/4 +r (η/4 +r η/4)) +r δ +r (η/4 +r ε) ≡
        ε +r ((η/4 +r η/4) +r (η/4 +r η/4) +r δ)
      lemma _ _ _ = solve! R

-- Lemma 3.5
isRefl∼ : ∀ x ε → x ∼[ ε ] x
isRefl∼ = Elimℭ-Prop.go e where
  open Elimℭ-Prop
  e : Elimℭ-Prop λ x → (ε : ℚ₊) → x ∼[ ε ] x
  e .funι    = λ x ε → ι-ι (isRefl≈ x ε)
  e .funLim  = λ x xc IH ε → subst∼ _ _
    (cong (⟨ ε ⟩₊ /2 ℚ.+_) (/4+/4≡/2 ⟨ ε ⟩₊) ∙ /2+/2≡id ⟨ ε ⟩₊)
    (lim-lim _ _ xc xc (IH (ε /4₊) (ε /2₊)))
  e .is-prop = λ x → isPropΠ λ ε → isProp∼ x ε x

-- Lemma 3.6
isSetℭ : isSet ℭM
isSetℭ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼[ ε ] y) isRefl∼ (λ _ _ → isPropΠ (λ _ → isProp∼ _ _ _)) (eqℭ _ _)

isTriangular∼ : ∀ x y z ε δ → x ∼[ ε ] y → y ∼[ δ ] z → x ∼[ ε +₊ δ ] z
isTriangular∼ x y z ε δ x∼y y∼z =
  (B→∼ (isTriangularBall (snd B⟨ x ,⟩) ε δ y z (∼→B x∼y) y∼z))
  where open IsBall

isRounded∼ : ∀ x y ε → x ∼[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × x ∼[ δ ] y
isRounded∼ x y ε x∼y = PT.map (λ (δ , δ<ε , B[δ]x,y) → (δ , δ<ε , B→∼ B[δ]x,y))
  (isRoundedBall (snd B⟨ x ,⟩) ε y (∼→B x∼y))
  where open IsBall

-- Theorem 3.16
ℭPremetricSpace : PremetricSpace ℓ'' ℓ''
fst ℭPremetricSpace = ℭM
PremetricStr._≈[_]_      (snd ℭPremetricSpace) = _∼[_]_
PremetricStr.isPremetric (snd ℭPremetricSpace) = isPMℭ where
  open IsPremetric

  isPMℭ : IsPremetric _∼[_]_
  isPMℭ .is-set        = isSetℭ
  isPMℭ .isProp≈       = flip ∘ isProp∼
  isPMℭ .isRefl≈       = isRefl∼
  isPMℭ .isSym≈        = isSym∼
  isPMℭ .isSeparated≈  = eqℭ
  isPMℭ .isTriangular≈ = isTriangular∼
  isPMℭ .isRounded≈    = isRounded∼

-- Theorem 3.17
isInjectiveι : ∀ x y → ι x ≡ ι y → x ≡ y
isInjectiveι x y ιx≡ιy = isSeparated≈ x y λ ε →
  ∼→B (subst (ι x ∼[ ε ]_) ιx≡ιy (isRefl∼ (ι x) ε))

isEmbeddingι : isEmbedding ι
isEmbeddingι = injEmbedding isSetℭ (isInjectiveι _ _)

ιᴵ : Isometry[ M , ℭPremetricSpace ]
fst ιᴵ = ι
IsIsometry.pres≈ (snd ιᴵ) _ _ _ = invEquiv ∼≃B

ιⁿ : NE[ M , ℭPremetricSpace ]
fst ιⁿ = ι
IsNonExpansive.pres≈ (snd ιⁿ) _ _ _ = ι-ι

ιᶜ : C[ M , ℭPremetricSpace ]
ιᶜ = NE→C ιⁿ

ιᵘᶜ : UC[ M , ℭPremetricSpace ]
ιᵘᶜ = NE→UC ιⁿ

ιᴸ : L[ M , ℭPremetricSpace ]
ιᴸ = NE→L ιⁿ

open PremetricTheory.PremetricReasoning ℭPremetricSpace

isLimitLim : ∀ x xc → isLimit ℭPremetricSpace x (lim x xc)
isLimitLim = λ x xc ε θ → Elimℭ-Prop.go e (x ε) x xc ε θ (isRefl∼ (x ε) θ) where opaque
  open Elimℭ-Prop
  e : Elimℭ-Prop λ u → ∀ x xc ε θ → u ∼[ θ ] (x ε) → u ∼[ ε +₊ θ ] lim x xc
  e .funι   u x xc ε θ = subst∼ (ι u) (lim x xc) (ℚ.+Comm ⟨ θ ⟩₊ ⟨ ε ⟩₊) ∘ ι-lim ε xc
  e .funLim u uc IH x xc ε θ limu∼[θ]xε = proof _ , isProp∼ _ _ _ by do
    (δ , δ<θ , limu∼[δ]xε) ← isRounded∼ (lim u uc) (x ε) θ limu∼[θ]xε
    let
      η = [ θ -₊ δ ]⟨ δ<θ ⟩ ; 3η/4 = η /4₊ +₊ (η /4₊ +₊ η /4₊)
      step = lemma ℚCR ⟨ η /4₊ ⟩₊ _ _
          ∙∙ cong (λ - → ⟨ ε ⟩₊ ℚ.+ (- ℚ.+ _)) (/4+/4+/4+/4≡id ⟨ η ⟩₊)
          ∙∙ cong (⟨ ε ⟩₊ ℚ.+_) (minusPlus₊ θ δ)
    return ((begin≈[ 3η/4 +₊ δ ]⟨⟩
      u (η /4₊) ≈[ 3η/4  ]⟨ IH (η /4₊) u uc _ _ (uc (η /4₊) (η /4₊)) ⟩
      lim u uc  ≈[   δ   ]⟨ limu∼[δ]xε ⟩
      x ε       ≈∎
      :>
      u (η /4₊) ∼[ 3η/4 +₊ δ ] x ε)                       →⟨ lim-lim (η /4₊) ε uc xc ⟩
      lim u uc  ∼[ (3η/4 +₊ δ) +₊ (η /4₊ +₊ ε) ] lim x xc →⟨ subst∼ _ _ step ⟩
      lim u uc  ∼[ ε +₊ θ ] lim x xc                      )
  e .is-prop u = isPropΠ5 λ x xc ε θ _ → isProp∼ u (ε +₊ θ) (lim x xc)

-- Theorem 3.18
isCompleteℭ : isComplete ℭPremetricSpace
fst (isCompleteℭ x xc) = lim x xc
snd (isCompleteℭ x xc) = isLimitLim x xc
