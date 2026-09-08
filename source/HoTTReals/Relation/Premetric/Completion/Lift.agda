module HoTTReals.Relation.Premetric.Completion.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals as ℚ using ()

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Base using (ι)
open import Cubical.Relation.Premetric.Completion.Properties renaming
  (ℭPremetricSpace to ℭ)
open import Cubical.Relation.Premetric.Completion.Lift using (continuous≡)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals using (ℚ!)

open PositiveRationals
open ℚ₊Inverse
open PremetricTheory using (isComplete)

private
  variable
    ℓA ℓA' ℓB ℓB' ℓM ℓM' ℓN ℓN' : Level

module _
  (A : PremetricSpace ℓA (ℓ-max ℓA ℓA'))
  (B : PremetricSpace ℓB (ℓ-max ℓB ℓB'))
  (N : PremetricSpace ℓN' ℓN) where
  private
    ℭA = ℭ ℓA' A
    ℭB = ℭ ℓB' B

  continuous₂≡ :
    (f g : ⟨ ℭA ⟩ → ⟨ ℭB ⟩ → ⟨ N ⟩) →
    ((u : ⟨ ℭA ⟩) → isContinuous (snd ℭB) (f u) (snd N)) →
    ((v : ⟨ ℭB ⟩) → isContinuous (snd ℭA) (flip f v) (snd N)) →
    ((u : ⟨ ℭA ⟩) → isContinuous (snd ℭB) (g u) (snd N)) →
    ((v : ⟨ ℭB ⟩) → isContinuous (snd ℭA) (flip g v) (snd N)) →
    ((a : ⟨ A ⟩) (b : ⟨ B ⟩) → f (ι a) (ι b) ≡ g (ι a) (ι b)) →
    (u : ⟨ ℭA ⟩) (v : ⟨ ℭB ⟩) → f u v ≡ g u v
  continuous₂≡
    ( f)
    ( g)
    ( fContinuousR)
    ( fContinuousL)
    ( gContinuousR)
    ( gContinuousL)
    ( fιι≡gιι)
    ( u) =
    continuous≡
      ( B)
      ( N)
      ( f u , fContinuousR u)
      ( g u , gContinuousR u)
      ( λ b →
        continuous≡
          ( A)
          ( N)
          ( flip f (ι b) , fContinuousL (ι b))
          ( flip g (ι b) , gContinuousL (ι b))
          ( flip fιι≡gιι b)
          ( u))

module _
  (M : PremetricSpace ℓM (ℓ-max ℓM ℓM'))
  (N : PremetricSpace ℓN' ℓN) where
  private
    ℭM = ℭ ℓM' M
    module N where
      open PremetricStr (snd N) public
      open PremetricTheory N public

  open import Cubical.Relation.Premetric.Completion.Elim M using (RecℭSym)

  module LiftCompleteCodomain (N-com : isComplete N) where

    private
      liftLipschitzWithRec :
        (L : ℚ₊) (f : ⟨ M ⟩ → ⟨ N ⟩) →
        IsLipschitzWith (snd M) f (snd N) L →
        RecℭSym ⟨ N ⟩ (λ s t ε → s N.≈[ L ·₊ ε ] t)
      liftLipschitzWithRec L f fLipschitz = r
        where
        open RecℭSym

        isCauchyReindex :
          (g : ℚ₊ → ⟨ N ⟩) →
          ((ε δ : ℚ₊) → g ε N.≈[ L ·₊ (ε +₊ δ) ] g δ) →
          N.isCauchy (g ∘ (_/ L))
        isCauchyReindex g gCauchy ε δ =
          N.subst≈
            ( g $ ε / L)
            ( g $ δ / L)
            ( distributeCancel)
            ( gCauchy (ε / L) (δ / L))
          where
          distributeCancel : ⟨ L ·₊ (ε / L +₊ δ / L) ⟩₊ ≡ ⟨ ε +₊ δ ⟩₊
          distributeCancel =
            ⟨ L ·₊ (ε / L +₊ δ / L) ⟩₊
              ≡⟨ ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε / L ⟩₊ ⟨ δ / L ⟩₊ ⟩
            ⟨ L ·₊ (ε / L) +₊ L ·₊ (δ / L) ⟩₊
              ≡⟨ cong₂ ℚ._+_ (·/ L ε) (·/ L δ) ⟩
            ⟨ ε +₊ δ ⟩₊ ∎

        limitReindex :
          (g : ℚ₊ → ⟨ N ⟩) →
          ((ε δ : ℚ₊) → g ε N.≈[ L ·₊ (ε +₊ δ) ] g δ) →
          N.limit (g ∘ (_/ L))
        limitReindex g gCauchy = N-com (g ∘ (_/ L)) (isCauchyReindex g gCauchy)

        reindex : (δ : ℚ₊) → ⟨ δ ⟩₊ ≡ ⟨ (L ·₊ δ) / L ⟩₊
        reindex δ = sym (·/ L δ) ∙ ℚ.·Assoc ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ L ⁻¹₊ ⟩₊

        r : RecℭSym ⟨ N ⟩ (λ s t ε → s N.≈[ L ·₊ ε ] t)
        r .ιA = f
        r .limA g gCauchy = fst $ limitReindex g gCauchy
        r .eqA s t h =
          N.isSeparated≈ s t $ λ ε → N.subst≈ s t (·/ L ε) (h $ ε / L)
        r .ι-ι-B = IsLipschitzWith.pres≈ fLipschitz
        r .ι-lim-B a g ε δ gCauchy =
          N.subst≈ (f a) (fst $ limitReindex g gCauchy) factorConstant ∘
          N.isLim≈+
            ( f a)
            ( g ∘ (_/ L))
            ( fst $ limitReindex g gCauchy)
            ( L ·₊ δ)
            ( L ·₊ ε)
            ( snd $ limitReindex g gCauchy) ∘
          N.subst≈R (cong g $ ℚ₊≡ $ reindex δ)
          where
          factorConstant : ⟨ L ·₊ δ +₊ L ·₊ ε ⟩₊ ≡ ⟨ L ·₊ (ε +₊ δ) ⟩₊
          factorConstant = ℚ!
        r .lim-lim-B g h ε δ η gCauchy hCauchy =
          N.subst≈
            ( fst $ limitReindex g gCauchy)
            ( fst $ limitReindex h hCauchy)
            ( factorConstant) ∘
          N.isLim≈+₂
            ( g ∘ (_/ L))
            ( h ∘ (_/ L))
            ( fst $ limitReindex g gCauchy)
            ( fst $ limitReindex h hCauchy)
            ( L ·₊ ε)
            ( L ·₊ δ)
            ( L ·₊ η)
            ( snd $ limitReindex g gCauchy)
            ( snd $ limitReindex h hCauchy) ∘
          N.subst≈L (cong g $ ℚ₊≡ $ reindex δ) ∘
          N.subst≈R (cong h $ ℚ₊≡ $ reindex η)
          where
          factorConstant :
            ⟨ L ·₊ δ +₊ (L ·₊ η +₊ L ·₊ ε) ⟩₊ ≡ ⟨ L ·₊ (ε +₊ (δ +₊ η)) ⟩₊
          factorConstant = ℚ!
        r .isSymB s t ε = N.isSym≈ s t $ L ·₊ ε
        r .isPropB s t ε = N.isProp≈ s t $ L ·₊ ε

    liftLipschitzWith :
      (L : ℚ₊) (f : ⟨ M ⟩ → ⟨ N ⟩) →
      IsLipschitzWith (snd M) f (snd N) L →
      Σ[ f' ∈ (⟨ ℭM ⟩ → ⟨ N ⟩) ] IsLipschitzWith (snd ℭM) f' (snd N) L
    fst (liftLipschitzWith L f fLipschitz) =
      RecℭSym.go $ liftLipschitzWithRec L f fLipschitz
    snd (liftLipschitzWith L f fLipschitz) =
      islipschitzwith
        ( λ _ _ _ → RecℭSym.go∼ $ liftLipschitzWithRec L f fLipschitz)

    liftLipschitzWith∘ι :
      (L : ℚ₊) (f : ⟨ M ⟩ → ⟨ N ⟩)
      (fLipschitz : IsLipschitzWith (snd M) f (snd N) L) →
      fst (liftLipschitzWith L f fLipschitz) ∘ ι ≡ f
    liftLipschitzWith∘ι L f fLipschitz = refl
