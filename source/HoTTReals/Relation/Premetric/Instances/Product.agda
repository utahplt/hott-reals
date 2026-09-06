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
  module _
    {ℓK ℓK'}
    {K : PremetricSpace ℓK ℓK'} where

    composeIsLipschitzWith₂ :
      (f : ⟨ K ⟩ → ⟨ M ⟩)
      (g : ⟨ K ⟩ → ⟨ N ⟩)
      (h : ⟨ M ⟩ → ⟨ N ⟩ → ⟨ X ⟩)
      (L R N₁ N₂ : ℚ₊) →
      IsLipschitzWith (snd K) f (snd M) L →
      IsLipschitzWith (snd K) g (snd N) R →
      ((y : ⟨ N ⟩) →
        IsLipschitzWith (snd M) (flip h y) (snd X) N₁) →
      ((x : ⟨ M ⟩) →
        IsLipschitzWith (snd N) (h x) (snd X) N₂) →
      IsLipschitzWith
        ( snd K)
        ( λ x → h (f x) (g x))
        ( snd X)
        ( N₁ ·₊ L +₊ N₂ ·₊ R)
    composeIsLipschitzWith₂ = {!!}

  uncurryIsLipschitzWith :
    (h : ⟨ M ⟩ → ⟨ N ⟩ → ⟨ X ⟩) (L₁ L₂ : ℚ₊) →
    ((y : ⟨ N ⟩) → IsLipschitzWith (snd M) (flip h y) (snd X) L₁) →
    ((x : ⟨ M ⟩) → IsLipschitzWith (snd N) (h x) (snd X) L₂) →
    IsLipschitzWith (snd (M ×PrSp N)) (uncurry h) (snd X) (L₁ +₊ L₂)
  uncurryIsLipschitzWith h L₁ L₂ leftLipschitz rightLipschitz =
    subst
      ( IsLipschitzWith
        ( snd (M ×PrSp N))
        ( uncurry h)
        ( snd X))
      ( ℚ₊≡
        ( cong₂ ℚ._+_
          (ℚ.·IdR ⟨ L₁ ⟩₊)
          (ℚ.·IdR ⟨ L₂ ⟩₊)))
      ( composeIsLipschitzWith₂
        ( fst)
        ( snd)
        ( h)
        ( 1)
        ( 1)
        ( L₁)
        ( L₂)
        ( isNonExpansive→isLipschitzWith1 _ _ _ (snd (projⁿ₁ M N)))
        ( isNonExpansive→isLipschitzWith1 _ _ _ (snd (projⁿ₂ M N)))
        ( leftLipschitz)
        ( rightLipschitz))

  uncurryNE₂ : NE₂[ M , N , X ] → L[ M ×PrSp N , X ]
  fst (uncurryNE₂ f) = uncurry (NE₂[_,_,_].fun f)
  snd (uncurryNE₂ f) =
    ∣ 1 +₊ 1 ,
      uncurryIsLipschitzWith
        ( fun)
        ( 1)
        ( 1)
        ( isNonExpansive→isLipschitzWith1 _ _ _ ∘ lNE)
        ( isNonExpansive→isLipschitzWith1 _ _ _ ∘ rNE) ∣₁
    where open NE₂[_,_,_] f

  module _
    {ℓK ℓK'}
    {K : PremetricSpace ℓK ℓK'} where

    composeNE₂ :
      NE[ K , M ] →
      NE[ K , N ] →
      NE₂[ M , N , X ] →
      L[ K , X ]
    fst (composeNE₂ f g h) x =
      NE₂[_,_,_].fun h (fst f x) (fst g x)
    snd (composeNE₂ f g h) =
      ∣ 2 ,
        subst
          ( IsLipschitzWith
            ( snd K)
            ( λ x → NE₂[_,_,_].fun h (fst f x) (fst g x))
            ( snd X))
          ( ℚ₊≡ refl)
          ( composeIsLipschitzWith₂
            ( fst f)
            ( fst g)
            ( NE₂[_,_,_].fun h)
            ( 1)
            ( 1)
            ( 1)
            ( 1)
            ( isNonExpansive→isLipschitzWith1 _ _ _ (snd f))
            ( isNonExpansive→isLipschitzWith1 _ _ _ (snd g))
            ( isNonExpansive→isLipschitzWith1 _ _ _ ∘
              NE₂[_,_,_].lNE h)
            ( isNonExpansive→isLipschitzWith1 _ _ _ ∘
              NE₂[_,_,_].rNE h)) ∣₁
