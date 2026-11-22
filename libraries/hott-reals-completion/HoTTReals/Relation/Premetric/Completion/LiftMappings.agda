{-
  Lift of non-expansive and lipschitz mappings from M → N to ℭM → N, where N is complete,
  following Formalising real numbers in homotopy type theory, Gaëtan Gilbert, 2017
-}
module HoTTReals.Relation.Premetric.Completion.LiftMappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals renaming (ℚCommRing to ℚCR)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Function
open import Cubical.Relation.Premetric.Instances.Scaled
open import HoTTReals.Relation.Premetric.Completion
import HoTTReals.Relation.Premetric.Completion.Properties as ℭProperties

open import Cubical.Tactics.CommRingSolver

open 1/2∈ℚ
open PremetricTheory

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

private
  module _ (R : CommRing ℓ-zero) where
    open CommRingStr (snd R) using () renaming (_+_ to _+r_)
    opaque
      lemma : ∀ ε δ η → δ +r (η +r ε) ≡ ε +r (δ +r η)
      lemma _ _ _ = solve! R

module _ (M : PremetricSpace ℓM (ℓ-max ℓM ℓM')) (N : PremetricSpace ℓN' ℓN) where

  private
    ℭM = ℭPremetricSpace ℓM' M
    module M = PremetricStr (snd M)
    module N = PremetricStr (snd N)
    module ℭM where
      open PremetricStr (snd ℭM) public
      open ℭProperties ℓM' M public

  open import HoTTReals.Relation.Premetric.Completion.Elim M
  open Elimℭ-Prop
  open RecℭSym
  open IsContinuousAt
  open IsNonExpansive

  -- Theorem 3.19
  continuous≡ : (f g : C[ ℭM , N ])
              → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  continuous≡ (f , fc) (g , gc) f∘ι≡g∘ι = Elimℭ-Prop.go e where
    open PremetricReasoning N
    e : Elimℭ-Prop λ x → f x ≡ g x
    e .funι           = f∘ι≡g∘ι
    e .funLim x xc IH = N.isSeparated≈ _ _ λ ε → proof _ , N.isProp≈ _ _ ε by do
      (δf , ∼δf→≈ε/2) ← fc (lim x xc) .pres≈ (ε /2₊)
      (δg , ∼δg→≈ε/2) ← gc (lim x xc) .pres≈ (ε /2₊)
      let
        limx≈xδ : ∀ {η} → min₊ δf δg /2₊ <₊ η → lim x xc ℭM.≈[ η ] x (min₊ δf δg /2₊)
        limx≈xδ = ℭM.isSym≈ _ _ _ ∘ isLimit≈< ℭM x _ (ℭM.isLimitLim x xc) _ _

      return (begin≈[ ε ]⟨ /2+/2≡id ⟨ ε ⟩₊ ⟩
        f (lim x xc)             ≈[ ε /2₊ ]⟨     ∼δf→≈ε/2 _ $ limx≈xδ $ min/2₊<L δf δg  ⟩
        f (x (min₊ δf δg /2₊)) ≡→≈⟨ IH (min₊ δf δg /2₊) ⟩
        g (x (min₊ δf δg /2₊))   ≈[ ε /2₊ ]⟨ ≈⁻ (∼δg→≈ε/2 _ $ limx≈xδ $ min/2₊<R δf δg) ⟩
        g (lim x xc)             ≈∎)
    e .is-prop x = N.is-set (f x) (g x)

  uContinuous≡ : (f g : UC[ ℭM , N ])
               → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  uContinuous≡ f g = continuous≡ (UC→C f) (UC→C g)

  lipschitz≡ : (f g : L[ ℭM , N ])
             → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  lipschitz≡ f g = continuous≡ (L→C f) (L→C g)

  nonExpansive≡ : (f g : NE[ ℭM , N ])
                → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  nonExpansive≡ f g = continuous≡ (NE→C f) (NE→C g)

  module Liftⁿ (N-com : isComplete N) where

    private
      limN : ∀ x → isCauchy N x → ⟨ N ⟩
      limN = (fst ∘_) ∘ N-com

      isLimitN : ∀ x xc → isLimit N x (limN x xc)
      isLimitN = (snd ∘_) ∘ N-com

    liftNE : NE[ M , N ] → NE[ ℭM , N ]
    liftNE (f , is-ne) = RecℭSym.go r , isnonexpansive λ _ _ _ → RecℭSym.go∼ r
      module LiftNonExpansive where
      r : RecℭSym ⟨ N ⟩ λ u v ε → u N.≈[ ε ] v
      r .funι     = f
      r .funLim   = (fst ∘_) ∘ N-com
      r .funEq    = N.isSeparated≈
      r .ι︵ι     = pres≈ is-ne
      r .ι︵lim   = λ x y ε δ yc → subst≈ N _ _ (ℚ.+Comm ⟨ δ ⟩₊ ⟨ ε ⟩₊) ∘
        isLim≈+ N (f x) y (fst (N-com y yc)) δ ε (snd (N-com y yc))
      r .lim︵lim = λ x y ε δ η xc yc → subst≈ N _ _ (lemma ℚCR ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ η ⟩₊) ∘
        isLim≈+₂ N x y _ _ ε δ η (snd (N-com x xc)) (snd (N-com y yc))
      r .isSym︵  = N.isSym≈
      r .isProp︵ = N.isProp≈

    liftNE∘ι : (f : NE[ M , N ]) → fst (liftNE f) ∘ ι ≡ fst f
    liftNE∘ι f = refl

    isCauchyliftNE : ∀ f x → isCauchy ℭM x → isCauchy N (fst (liftNE f) ∘ x)
    isCauchyliftNE f x xc ε δ = pres≈ (snd (liftNE f)) _ _ _ (xc ε δ)

    liftNE$lim : ∀ f x xc
      → fst (liftNE f) (lim x xc) ≡ limN (fst (liftNE f) ∘ x) (isCauchyliftNE f x xc)
    liftNE$lim f x xc = refl

    -- Lemma 3.24
    ≈→liftNE≈ : (f g : NE[ M , N ]) → ∀ ε
              → (∀ x δ → fst f x N.≈[ ε +₊ δ ] fst g x)
              →  ∀ x δ → fst (liftNE f) x N.≈[ ε +₊ δ ] fst (liftNE g) x
    ≈→liftNE≈ f g ε f≈g = Elimℭ-Prop.go r module ≈→liftNE≈ where
      r : Elimℭ-Prop λ x → ∀ δ → fst (liftNE f) x N.≈[ ε +₊ δ ] fst (liftNE g) x
      r .funι             = f≈g
      r .funLim x xc IH δ = subst≈ N
        (limN (fst (liftNE f) ∘ x) (isCauchyliftNE f x xc))
        (limN (fst (liftNE g) ∘ x) (isCauchyliftNE g x xc))
        δ/4+δ/4+ε+δ/2≡ε+δ
        (isLim≈+₂ N
          (fst (liftNE f) ∘ x) (fst (liftNE g) ∘ x) _ _ (ε +₊ δ /2₊) (δ /4₊) (δ /4₊)
          (isLimitN _ (isCauchyliftNE f x xc)) (isLimitN _ (isCauchyliftNE g x xc))
          (IH (δ /4₊) (δ /2₊)))
        where
        δ/4+δ/4+ε+δ/2≡ε+δ : ⟨ (δ /4₊) +₊ ((δ /4₊) +₊ (ε +₊ (δ /2₊))) ⟩₊ ≡ ⟨ ε +₊ δ ⟩₊
        δ/4+δ/4+ε+δ/2≡ε+δ =
          ⟨ δ /4₊ +₊ (δ /4₊ +₊ (ε +₊ δ /2₊)) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ δ /4₊ ⟩₊ _ _ ⟩
          ⟨ (δ /4₊ +₊ δ /4₊) +₊ (ε +₊ δ /2₊) ⟩₊ ≡⟨ congL ℚ._+_ (/4+/4≡/2 ⟨ δ ⟩₊) ⟩
          ⟨ δ /2₊ +₊ (ε +₊ δ /2₊) ⟩₊            ≡⟨ ℚ.+Comm ⟨ δ /2₊ ⟩₊ _ ⟩
          ⟨ (ε +₊ δ /2₊) +₊ δ /2₊ ⟩₊            ≡⟨ sym $ ℚ.+Assoc ⟨ ε ⟩₊ ⟨ δ /2₊ ⟩₊ _ ⟩
          ⟨ ε +₊ (δ /2₊ +₊ δ /2₊) ⟩₊            ≡⟨ cong (⟨ ε ⟩₊ ℚ.+_) (/2+/2≡id ⟨ δ ⟩₊) ⟩
          ⟨ ε +₊ δ ⟩₊                           ∎
      r .is-prop = λ _ → isPropΠ λ _ → N.isProp≈ _ _ _

    liftNEⁿ : NE[ NE[ M , N ]PrSpace , NE[ ℭM , N ]PrSpace ]
    fst liftNEⁿ = liftNE
    pres≈ (snd liftNEⁿ) fⁿ@(f , f-ne) gⁿ@(g , g-ne) ε = PT.map proof where
      proof : Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → f x N.≈[ δ ] g x)
            → Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → fst (liftNE fⁿ) x N.≈[ δ ] fst (liftNE gⁿ) x)
      proof (δ , δ<ε , ptwf≈g) .fst      = mean₊ δ ε
      proof (δ , δ<ε , ptwf≈g) .snd .fst = <→mean< ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε
      proof (δ , δ<ε , ptwf≈g) .snd .snd = λ x → subst≈ N _ _
        (ℚ.+Comm ⟨ δ ⟩₊ (⟨ mean₊ δ ε ⟩₊ ℚ.- ⟨ δ ⟩₊) ∙ minusPlus₊ (mean₊ δ ε) δ) $
        ≈→liftNE≈ fⁿ gⁿ δ
          (λ x η → isMonotone≈< N {ε = δ} {δ +₊ η} (<₊SumLeft δ η) (ptwf≈g x))
          x [ mean₊ δ ε -₊ δ ]⟨ <→<mean ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε ⟩

module _ (M : PremetricSpace ℓM (ℓ-max ℓM ℓM')) (N : PremetricSpace ℓN' ℓN) where
  private
    ℭM = ℭPremetricSpace ℓM' M
    module N = PremetricStr (snd N)

  module Liftᴸ (N-com : isComplete N) where
    module _ (L : ℚ₊) where
      open Scaled N L renaming (·PremetricSpace to L·N)
      open Liftⁿ {ℓM' = ℓM'} M L·N (isComplete· N-com)
      open Iso

      liftLipschitzWith : Σ[ f ∈ _ ] IsLipschitzWith (snd M)  f (snd N) L
                        → Σ[ g ∈ _ ] IsLipschitzWith (snd ℭM) g (snd N) L
      liftLipschitzWith = L[,]≅NE[,·] ℭM N L .inv ∘ liftNE ∘ L[,]≅NE[,·] M N L .fun

      liftLipschitzWithᴸ : Σ[ f ∈ _ ] IsLipschitzWith (snd M) f (snd N) L → L[ ℭM , N ]
      liftLipschitzWithᴸ = map-snd (∣_∣₁ ∘ (L ,_)) ∘ liftLipschitzWith

      liftLipschitzWithᴸ∘ι : (f : _) → fst (liftLipschitzWithᴸ f) ∘ ι ≡ fst f
      liftLipschitzWithᴸ∘ι f = refl

      liftLipschitzWithᴸ$lim : ∀ f x xc → let f̂ = fst (liftLipschitzWithᴸ f) in
        f̂ (lim x xc) ≡ fst (N-com (λ ε → f̂ (x (ε ₊/₊ L))) _)
      liftLipschitzWithᴸ$lim f x xc = refl

    isPropΣLiftL : (f : L[ M , N ]) → isProp (Σ[ g ∈ L[ ℭM , N  ] ] (fst g ∘ ι ≡ fst f))
    isPropΣLiftL f (g , g∘ι≡f) (h , h∘ι≡f) = Σ≡Prop (λ _ → isSet→ N.is-set _ _) $
      L≡ $ funExt $ lipschitz≡ _ _ g h $ funExt⁻ $ g∘ι≡f ∙ sym h∘ι≡f

    ΣLiftL : (f : L[ M , N ]) → Σ[ g ∈ L[ ℭM , N ] ] (fst g ∘ ι ≡ fst f)
    ΣLiftL f = PT.rec (isPropΣLiftL f)
      (uncurry λ L L-lip → liftLipschitzWithᴸ L (fst f , L-lip) , refl) (snd f)

    liftL : L[ M , N ] → L[ ℭM , N ]
    liftL = fst ∘ ΣLiftL

    liftL∘ι : (f : L[ M , N ]) → fst (liftL f) ∘ ι ≡ fst f
    liftL∘ι = snd ∘ ΣLiftL
