module HoTTReals.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open PositiveRationals
open 1/2∈ℚ using (/2+/2≡id)
open PositiveHalvesℚ using (_/2₊)

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
      (L₁ L₂ R₁ R₂ : ℚ₊) →
      IsLipschitzWith (snd K) f (snd M) L₁ →
      IsLipschitzWith (snd K) g (snd N) L₂ →
      ((y : ⟨ N ⟩) →
        IsLipschitzWith (snd M) (flip h y) (snd X) R₁) →
      ((x : ⟨ M ⟩) →
        IsLipschitzWith (snd N) (h x) (snd X) R₂) →
      IsLipschitzWith
        ( snd K)
        ( λ x → h (f x) (g x))
        ( snd X)
        ( R₁ ·₊ L₁ +₊ R₂ ·₊ L₂)
    IsLipschitzWith.pres≈
      ( composeIsLipschitzWith₂
        ( f)
        ( g)
        ( h)
        ( L₁)
        ( L₂)
        ( R₁)
        ( R₂)
        ( fLipschitz)
        ( gLipschitz)
        ( hLipschitzL)
        ( hLipschitzR))
      x y ε x≈y =
      subst≈
        ( h (f x) (g x))
        ( h (f y) (g y))
        ( combineConstants)
        ( isTriangular≈
          ( h (f x) (g x))
          ( h (f y) (g x))
          ( h (f y) (g y))
          ( R₁ ·₊ (L₁ ·₊ ε))
          ( R₂ ·₊ (L₂ ·₊ ε))
          ( hLipschitzL (g x) .pres≈
            ( f x)
            ( f y)
            ( L₁ ·₊ ε)
            ( fLipschitz .pres≈ x y ε x≈y))
          ( hLipschitzR (f y) .pres≈
            ( g x)
            ( g y)
            ( L₂ ·₊ ε)
            ( gLipschitz .pres≈ x y ε x≈y)))
      where
        open IsLipschitzWith
        open PremetricStr (snd X)
        open PremetricTheory X

        combineConstants :
          ⟨ R₁ ·₊ (L₁ ·₊ ε) +₊ R₂ ·₊ (L₂ ·₊ ε) ⟩₊ ≡
          ⟨ (R₁ ·₊ L₁ +₊ R₂ ·₊ L₂) ·₊ ε ⟩₊
        combineConstants = ℚ!

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
            ( isNonExpansive→isLipschitzWith1 _ _ _ $ snd f)
            ( isNonExpansive→isLipschitzWith1 _ _ _ $ snd g)
            ( isNonExpansive→isLipschitzWith1 _ _ _ ∘
              NE₂[_,_,_].lNE h)
            ( isNonExpansive→isLipschitzWith1 _ _ _ ∘
              NE₂[_,_,_].rNE h)) ∣₁

    composeL₂ :
      L[ K , M ] →
      L[ K , N ] →
      NE₂[ M , N , X ] →
      L[ K , X ]
    fst (composeL₂ f g h) x =
      NE₂[_,_,_].fun h (fst f x) (fst g x)
    snd (composeL₂ f g h) =
      PT.rec2
        ( squash₁)
        ( λ (L₁ , fLipschitz) (L₂ , gLipschitz) →
          ∣ 1 ·₊ L₁ +₊ 1 ·₊ L₂ ,
            composeIsLipschitzWith₂
              ( fst f)
              ( fst g)
              ( NE₂[_,_,_].fun h)
              ( L₁)
              ( L₂)
              ( 1)
              ( 1)
              ( fLipschitz)
              ( gLipschitz)
              ( isNonExpansive→isLipschitzWith1 _ _ _ ∘
                NE₂[_,_,_].lNE h)
              ( isNonExpansive→isLipschitzWith1 _ _ _ ∘
                NE₂[_,_,_].rNE h) ∣₁)
        ( snd f)
        ( snd g)

    composeC₂ :
      C[ K , M ] →
      C[ K , N ] →
      NE₂[ M , N , X ] →
      C[ K , X ]
    fst (composeC₂ f g h) x =
      NE₂[_,_,_].fun h (fst f x) (fst g x)
    IsContinuousAt.pres≈ (snd (composeC₂ f g h) x) ε =
      PT.rec2
        ( squash₁)
        ( λ (δ₁ , fClose) (δ₂ , gClose) →
          ∣ min₊ δ₁ δ₂ ,
            ( λ y x≈y →
              subst≈
                ( fun h (fst f x) (fst g x))
                ( fun h (fst f y) (fst g y))
                ( combineHalves)
                ( isTriangular≈
                  ( fun h (fst f x) (fst g x))
                  ( fun h (fst f y) (fst g x))
                  ( fun h (fst f y) (fst g y))
                  ( ε /2₊)
                  ( ε /2₊)
                  ( IsNonExpansive.pres≈ (lNE h $ fst g x)
                    ( fst f x)
                    ( fst f y)
                    ( ε /2₊)
                    ( fClose y $ PK.isMonotone≈≤ (min₊≤L δ₁ δ₂) x≈y))
                  ( IsNonExpansive.pres≈ (rNE h $ fst f y)
                    ( fst g x)
                    ( fst g y)
                    ( ε /2₊)
                    ( gClose y $ PK.isMonotone≈≤ (min₊≤R δ₁ δ₂) x≈y)))) ∣₁)
        ( IsContinuousAt.pres≈ (snd f x) (ε /2₊))
        ( IsContinuousAt.pres≈ (snd g x) (ε /2₊))
      where
      open NE₂[_,_,_]
      open PremetricStr (snd X)
      open PremetricTheory X
      module PK = PremetricTheory K

      combineHalves : ⟨ ε /2₊ +₊ ε /2₊ ⟩₊ ≡ ⟨ ε ⟩₊
      combineHalves = /2+/2≡id ⟨ ε ⟩₊

  uncurryIsLipschitzWith :
    (h : ⟨ M ⟩ → ⟨ N ⟩ → ⟨ X ⟩) (R₁ R₂ : ℚ₊) →
    ((y : ⟨ N ⟩) → IsLipschitzWith (snd M) (flip h y) (snd X) R₁) →
    ((x : ⟨ M ⟩) → IsLipschitzWith (snd N) (h x) (snd X) R₂) →
    IsLipschitzWith (snd (M ×PrSp N)) (uncurry h) (snd X) (R₁ +₊ R₂)
  uncurryIsLipschitzWith h R₁ R₂ leftLipschitz rightLipschitz =
    subst
      ( IsLipschitzWith
        ( snd $ M ×PrSp N)
        ( uncurry h)
        ( snd X))
      ( ℚ₊≡ dropUnits)
      ( composeIsLipschitzWith₂
        ( fst)
        ( snd)
        ( h)
        ( 1)
        ( 1)
        ( R₁)
        ( R₂)
        ( isNonExpansive→isLipschitzWith1 _ _ _ $ snd $ projⁿ₁ M N)
        ( isNonExpansive→isLipschitzWith1 _ _ _ $ snd $ projⁿ₂ M N)
        ( leftLipschitz)
        ( rightLipschitz))
    where
      dropUnits : ⟨ R₁ ·₊ 1 +₊ R₂ ·₊ 1 ⟩₊ ≡ ⟨ R₁ +₊ R₂ ⟩₊
      dropUnits = ℚ!

  uncurryNE₂ : NE₂[ M , N , X ] → L[ M ×PrSp N , X ]
  fst (uncurryNE₂ f) = uncurry (NE₂[_,_,_].fun f)
  snd (uncurryNE₂ f) =
    ∣ 2 ,
      subst
        ( IsLipschitzWith
          ( snd $ M ×PrSp N)
          ( uncurry fun)
          ( snd X))
        ( ℚ₊≡ refl)
        ( uncurryIsLipschitzWith
          ( fun)
          ( 1)
          ( 1)
          ( isNonExpansive→isLipschitzWith1 _ _ _ ∘ lNE)
          ( isNonExpansive→isLipschitzWith1 _ _ _ ∘ rNE)) ∣₁
    where open NE₂[_,_,_] f
