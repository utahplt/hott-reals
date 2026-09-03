module HoTTReals.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.Data.Rationals as ℚ using ()

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Product

open PositiveRationals

private
  variable
    ℓM ℓM' ℓN ℓN' ℓX ℓX' : Level

module _
  (M : PremetricSpace ℓM ℓM')
  (N : PremetricSpace ℓN ℓN')
  (X : PremetricSpace ℓX ℓX') where
  private
    module PX where
      open PremetricStr (snd X) public
      open PremetricTheory X public

  uncurryIsLipschitzWith :
    (h : ⟨ M ⟩ → ⟨ N ⟩ → ⟨ X ⟩) (L₁ L₂ : ℚ₊) →
    ((y : ⟨ N ⟩) → IsLipschitzWith (snd M) (flip h y) (snd X) L₁) →
    ((x : ⟨ M ⟩) → IsLipschitzWith (snd N) (h x) (snd X) L₂) →
    IsLipschitzWith (snd (M ×PrSp N)) (uncurry h) (snd X) (L₁ +₊ L₂)
  IsLipschitzWith.pres≈
    (uncurryIsLipschitzWith h L₁ L₂ leftLipschitz rightLipschitz)
    (x , y) (x' , y') ε (x≈x' , y≈y') =
    PX.subst≈ (h x y) (h x' y') (sym (ℚ.·DistR+ ⟨ L₁ ⟩₊ ⟨ L₂ ⟩₊ ⟨ ε ⟩₊)) $
      PX.isTriangular≈
        (h x y)
        (h x' y)
        (h x' y')
        (L₁ ·₊ ε)
        (L₂ ·₊ ε)
        (IsLipschitzWith.pres≈ (leftLipschitz y) x x' ε x≈x')
        (IsLipschitzWith.pres≈ (rightLipschitz x') y y' ε y≈y')

  uncurryNE₂ : NE₂[ M , N , X ] → L[ M ×PrSp N , X ]
  fst (uncurryNE₂ f) = uncurry (NE₂[_,_,_].fun f)
  snd (uncurryNE₂ f) =
    ∣ 1 +₊ 1 ,
      uncurryIsLipschitzWith
        fun
        1
        1
        (isNonExpansive→isLipschitzWith1 _ _ _ ∘ lNE)
        (isNonExpansive→isLipschitzWith1 _ _ _ ∘ rNE) ∣₁
    where open NE₂[_,_,_] f
