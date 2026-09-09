module HoTTReals.Data.Real.Algebra.Reciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Properties

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals using
  ( ℚPremetricSpace)
open import Cubical.Relation.Premetric.Completion.Closeness
  ℓ-zero ℚPremetricSpace using (∼≃B)
open import Cubical.Relation.Premetric.Completion.Lift using
  ( continuous≡ ; lipschitz≡)
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals using (ℚ!)

import HoTTReals.Algebra.OrderedCommRing.Properties as
  HoTTRealsOrderedCommRingProperties
open import HoTTReals.Algebra.OrderedCommRing.Instances.Rationals
open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Addition
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Data.Real.Order.Multiplication
open import HoTTReals.Relation.Premetric.Completion.Lift
open import HoTTReals.Relation.Premetric.Mappings

open PositiveRationals
open ℚ₊Inverse
open OrderedCommRingTheory ℚOrderedCommRing using
  ( <SumLeftPos ; abs1 ; 0<→-<0) renaming
  ( ·MonoL≤ to ·MonoL≤ℚ ; ·MonoL< to ·MonoL<ℚ)
open HoTTRealsOrderedCommRingProperties.OrderedCommRingTheory ℚOrderedCommRing
  using () renaming (abs· to abs·ℚ)
open OrderedAbGroupTheory ℝOrderedAbGroup using (abs ; 0≤abs ; abs≤≃)
open OrderedAbGroupTheory ℚOrderedAbGroup using (R≤⊔) renaming
  ( abs to absℚ ; 0≤abs to 0≤absℚ ; 0≤→abs≡id to 0≤→absℚ≡id
  ; abs-Comm to abs-Commℚ ; absΔ⊔≤R to absΔ⊔≤Rℚ)
open RingTheory (CommRing→Ring ℝCommRing) using (-DistL·)
open LiftCompleteCodomain ℚPremetricSpace ℝPremetricSpace isCompleteℝ

clamp₊ : ℚ₊ → ℚ → ℚ₊
fst (clamp₊ δ q) = ℚ.max q ⟨ δ ⟩₊
snd (clamp₊ δ q) =
  ℚ.isTrans<≤ 0 ⟨ δ ⟩₊ (ℚ.max q ⟨ δ ⟩₊) (snd δ) (R≤⊔ {q} {⟨ δ ⟩₊})

boundedRecipℚ : ℚ₊ → ℚ → ℚ
boundedRecipℚ δ q = ⟨ clamp₊ δ q ⁻¹₊ ⟩₊

boundedRecipℚIsLipschitzWith :
  (δ : ℚ₊) →
  IsLipschitzWith
    ( snd ℚPremetricSpace)
    ( rat ∘ boundedRecipℚ δ)
    ( snd ℝPremetricSpace)
    ( (δ ⁻¹₊) ·₊ (δ ⁻¹₊))
IsLipschitzWith.pres≈ (boundedRecipℚIsLipschitzWith δ) q r ε q≈r =
  invEq
    ( ∼≃B { rat recipL} { rat recipR} { (δ ⁻¹₊) ·₊ (δ ⁻¹₊) ·₊ ε})
    ( bound)
  where
  open OrderedCommRingReasoning ℚOrderedCommRing

  clampL : ℚ₊
  clampL = clamp₊ δ q

  clampR : ℚ₊
  clampR = clamp₊ δ r

  recipL : ℚ
  recipL = ⟨ clampL ⁻¹₊ ⟩₊

  recipR : ℚ
  recipR = ⟨ clampR ⁻¹₊ ⟩₊

  regroupFactors :
    (u v a b : ℚ) →
    (u ℚ.· (b ℚ.· v)) ℚ.- ((a ℚ.· u) ℚ.· v) ≡ (b ℚ.- a) ℚ.· (u ℚ.· v)
  regroupFactors u v a b = ℚ!

  recombineDifference :
    (u v a b : ℚ) → a ℚ.· u ≡ 1 → b ℚ.· v ≡ 1 →
    u ℚ.- v ≡ (b ℚ.- a) ℚ.· (u ℚ.· v)
  recombineDifference u v a b a·u≡1 b·v≡1 =
    u ℚ.- v
      ≡⟨ cong₂ ℚ._-_
           ( sym (ℚ.·IdR u) ∙ cong (u ℚ.·_) (sym b·v≡1))
           ( sym (ℚ.·IdL v) ∙ cong (ℚ._· v) (sym a·u≡1)) ⟩
    (u ℚ.· (b ℚ.· v)) ℚ.- ((a ℚ.· u) ℚ.· v)
      ≡⟨ regroupFactors u v a b ⟩
    (b ℚ.- a) ℚ.· (u ℚ.· v) ∎

  0≤recipR : 0 ℚ.≤ recipR
  0≤recipR = ℚ.<Weaken≤ 0 recipR $ snd (clampR ⁻¹₊)

  0≤recipBound : 0 ℚ.≤ ⟨ δ ⁻¹₊ ⟩₊
  0≤recipBound = ℚ.<Weaken≤ 0 ⟨ δ ⁻¹₊ ⟩₊ $ snd (δ ⁻¹₊)

  0≤recipProduct : 0 ℚ.≤ recipL ℚ.· recipR
  0≤recipProduct =
    ℚ.<Weaken≤ 0 (recipL ℚ.· recipR) $ snd ((clampL ⁻¹₊) ·₊ (clampR ⁻¹₊))

  leftBelowRecip : recipL ℚ.≤ ⟨ δ ⁻¹₊ ⟩₊
  leftBelowRecip = ⁻¹₊Flip≤ { δ} { clampL} (R≤⊔ { q} { ⟨ δ ⟩₊})

  rightBelowRecip : recipR ℚ.≤ ⟨ δ ⁻¹₊ ⟩₊
  rightBelowRecip = ⁻¹₊Flip≤ { δ} { clampR} (R≤⊔ { r} { ⟨ δ ⟩₊})

  recipProductBound : recipL ℚ.· recipR ℚ.≤ ⟨ δ ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊
  recipProductBound =
    ℚ.isTrans≤
      ( recipL ℚ.· recipR)
      ( ⟨ δ ⁻¹₊ ⟩₊ ℚ.· recipR)
      ( ⟨ δ ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊)
      ( ℚ.≤-·o recipL ⟨ δ ⁻¹₊ ⟩₊ recipR 0≤recipR leftBelowRecip)
      ( ·MonoL≤ℚ recipR ⟨ δ ⁻¹₊ ⟩₊ ⟨ δ ⁻¹₊ ⟩₊ 0≤recipBound rightBelowRecip)

  clampDifference :
    absℚ (⟨ clampR ⟩₊ ℚ.- ⟨ clampL ⟩₊) ℚ.≤ absℚ (q ℚ.- r)
  clampDifference =
    subst
      ( absℚ (⟨ clampR ⟩₊ ℚ.- ⟨ clampL ⟩₊) ℚ.≤_)
      ( abs-Commℚ r q)
      ( absΔ⊔≤Rℚ r q ⟨ δ ⟩₊)

  bound : absℚ (recipL ℚ.- recipR) ℚ.< ⟨ (δ ⁻¹₊) ·₊ (δ ⁻¹₊) ·₊ ε ⟩₊
  bound = begin<
    absℚ (recipL ℚ.- recipR)
      ≡→≤⟨ cong absℚ $
           recombineDifference recipL recipR ⟨ clampL ⟩₊ ⟨ clampR ⟩₊
             ( ⁻¹inverse clampL)
             ( ⁻¹inverse clampR) ⟩
    absℚ ((⟨ clampR ⟩₊ ℚ.- ⟨ clampL ⟩₊) ℚ.· (recipL ℚ.· recipR))
      ≡→≤⟨ abs·ℚ (⟨ clampR ⟩₊ ℚ.- ⟨ clampL ⟩₊) (recipL ℚ.· recipR) ∙
           cong (absℚ (⟨ clampR ⟩₊ ℚ.- ⟨ clampL ⟩₊) ℚ.·_)
             ( 0≤→absℚ≡id { recipL ℚ.· recipR} 0≤recipProduct) ⟩
    absℚ (⟨ clampR ⟩₊ ℚ.- ⟨ clampL ⟩₊) ℚ.· (recipL ℚ.· recipR)
      ≤⟨ ℚ.≤-·o
           ( absℚ (⟨ clampR ⟩₊ ℚ.- ⟨ clampL ⟩₊))
           ( absℚ (q ℚ.- r))
           ( recipL ℚ.· recipR)
           ( 0≤recipProduct)
           ( clampDifference) ⟩
    absℚ (q ℚ.- r) ℚ.· (recipL ℚ.· recipR)
      ≤⟨ ·MonoL≤ℚ
           ( recipL ℚ.· recipR)
           ( ⟨ δ ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊)
           ( absℚ (q ℚ.- r))
           ( 0≤absℚ (q ℚ.- r))
           ( recipProductBound) ⟩
    absℚ (q ℚ.- r) ℚ.· (⟨ δ ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊)
      <⟨ ℚ.<-·o
           ( absℚ (q ℚ.- r))
           ( ⟨ ε ⟩₊)
           ( ⟨ δ ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊)
           ( snd ((δ ⁻¹₊) ·₊ (δ ⁻¹₊)))
           ( q≈r) ⟩
    ⟨ ε ⟩₊ ℚ.· (⟨ δ ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊)
      ≡→≤⟨ ℚ.·Comm ⟨ ε ⟩₊ (⟨ δ ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊) ⟩
    ⟨ (δ ⁻¹₊) ·₊ (δ ⁻¹₊) ·₊ ε ⟩₊ ◾

private
  boundedRecipLift :
    (δ : ℚ₊) →
    Σ[ f ∈ (ℝ → ℝ) ]
      IsLipschitzWith (snd ℝPremetricSpace) f (snd ℝPremetricSpace)
        ( (δ ⁻¹₊) ·₊ (δ ⁻¹₊))
  boundedRecipLift δ =
    liftLipschitzWith ((δ ⁻¹₊) ·₊ (δ ⁻¹₊)) (rat ∘ boundedRecipℚ δ)
      ( boundedRecipℚIsLipschitzWith δ)

boundedRecip : ℚ₊ → ℝ → ℝ
boundedRecip δ = fst $ boundedRecipLift δ

boundedRecipIsLipschitzWith :
  (δ : ℚ₊) →
  IsLipschitzWith (snd ℝPremetricSpace) (boundedRecip δ) (snd ℝPremetricSpace)
    ( (δ ⁻¹₊) ·₊ (δ ⁻¹₊))
boundedRecipIsLipschitzWith δ = snd $ boundedRecipLift δ

boundedRecipᴸ : ℚ₊ → L[ ℝPremetricSpace , ℝPremetricSpace ]
boundedRecipᴸ δ =
  boundedRecip δ , ∣ (δ ⁻¹₊) ·₊ (δ ⁻¹₊) , boundedRecipIsLipschitzWith δ ∣₁

boundedRecip∘rat :
  (δ : ℚ₊) (q : ℚ) → boundedRecip δ (rat q) ≡ rat (boundedRecipℚ δ q)
boundedRecip∘rat δ q = refl

boundedRecipMax :
  (δ ε : ℚ₊) → δ ≤₊ ε → (x : ℝ) →
  boundedRecip δ (max x (rat ⟨ ε ⟩₊)) ≡ boundedRecip ε x
boundedRecipMax δ ε δ≤ε x =
  lipschitz≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( boundedRecipᴸ δ ∘L NE→L maxⁿ[ rat ⟨ ε ⟩₊ ])
    ( boundedRecipᴸ ε)
    ( λ q → cong rat $ clampTwice q)
    ( x)
  where
  absorbClamp : (q : ℚ) → ℚ.max (ℚ.max q ⟨ ε ⟩₊) ⟨ δ ⟩₊ ≡ ℚ.max q ⟨ ε ⟩₊
  absorbClamp q =
    ℚ.maxComm (ℚ.max q ⟨ ε ⟩₊) ⟨ δ ⟩₊ ∙
    ℚ.≤→max ⟨ δ ⟩₊ (ℚ.max q ⟨ ε ⟩₊)
      ( ℚ.isTrans≤ ⟨ δ ⟩₊ ⟨ ε ⟩₊ (ℚ.max q ⟨ ε ⟩₊) δ≤ε (R≤⊔ {q} {⟨ ε ⟩₊}))

  clampTwice :
    (q : ℚ) → boundedRecipℚ δ (ℚ.max q ⟨ ε ⟩₊) ≡ boundedRecipℚ ε q
  clampTwice q =
    cong (λ p → ⟨ p ⁻¹₊ ⟩₊) $
      ℚ₊≡ { clamp₊ δ (ℚ.max q ⟨ ε ⟩₊)} { clamp₊ ε q} (absorbClamp q)

boundedRecip≡ :
  (δ ε : ℚ₊) (x : ℝ) → rat ⟨ δ ⟩₊ ≤ x → rat ⟨ ε ⟩₊ ≤ x →
  boundedRecip δ x ≡ boundedRecip ε x
boundedRecip≡ δ ε x ratδ≤x ratε≤x =
  boundedRecip δ x
    ≡⟨ sym $ boundedRecipMax (min₊ δ ε) δ (min₊≤L δ ε) x ⟩
  boundedRecip (min₊ δ ε) (max x (rat ⟨ δ ⟩₊))
    ≡⟨ cong (boundedRecip $ min₊ δ ε) $
       maxComm x (rat ⟨ δ ⟩₊) ∙ ratδ≤x ⟩
  boundedRecip (min₊ δ ε) x
    ≡⟨ cong (boundedRecip $ min₊ δ ε) $
       sym $ maxComm x (rat ⟨ ε ⟩₊) ∙ ratε≤x ⟩
  boundedRecip (min₊ δ ε) (max x (rat ⟨ ε ⟩₊))
    ≡⟨ boundedRecipMax (min₊ δ ε) ε (min₊≤R δ ε) x ⟩
  boundedRecip ε x ∎

0<→∃rat≤ : (x : ℝ) → 0 < x → ∃[ δ ∈ ℚ₊ ] (rat ⟨ δ ⟩₊ ≤ x)
0<→∃rat≤ x 0<x =
  PT.map
    ( λ (q , 0<ratq , ratq<x) →
      ( q , invEq (<≃rat< {0} {q}) 0<ratq) , <Weaken≤ {rat q} {x} ratq<x)
    ( isArchimedean< 0 x 0<x)

opaque
  recip : (x : ℝ) → 0 < x → ℝ
  recip x 0<x =
    PT.SetElim.rec→Set
      ( isSetℭ)
      ( λ (δ , ratδ≤x) → boundedRecip δ x)
      ( λ (δ , ratδ≤x) (ε , ratε≤x) → boundedRecip≡ δ ε x ratδ≤x ratε≤x)
      ( 0<→∃rat≤ x 0<x)

opaque
  unfolding recip

  recip≡boundedRecip :
    (δ : ℚ₊) (x : ℝ) (0<x : 0 < x) → rat ⟨ δ ⟩₊ ≤ x →
    recip x 0<x ≡ boundedRecip δ x
  recip≡boundedRecip δ x 0<x ratδ≤x =
    PT.SetElim.helper
      ( isSetℭ)
      ( λ (ε , ratε≤x) → boundedRecip ε x)
      ( λ (ε , ratε≤x) (η , ratη≤x) → boundedRecip≡ ε η x ratε≤x ratη≤x)
      ( 0<→∃rat≤ x 0<x)
      ( ∣ δ , ratδ≤x ∣₁)

boundedRecipInvR :
  (δ : ℚ₊) (x : ℝ) → max x (rat ⟨ δ ⟩₊) · boundedRecip δ x ≡ 1
boundedRecipInvR δ x =
  continuous≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( NE→C maxⁿ[ rat ⟨ δ ⟩₊ ] ·ᶜ L→C (boundedRecipᴸ δ))
    ( constᶜ 1)
    ( rationalCase)
    ( x)
  where
  rationalCase :
    (q : ℚ) → max (rat q) (rat ⟨ δ ⟩₊) · boundedRecip δ (rat q) ≡ 1
  rationalCase q =
    rat·rat (ℚ.max q ⟨ δ ⟩₊) (boundedRecipℚ δ q) ∙
    cong rat (⁻¹inverse $ clamp₊ δ q)

recipInvR : (x : ℝ) (0<x : 0 < x) → x · recip x 0<x ≡ 1
recipInvR x 0<x =
  PT.rec (isSetℭ (x · recip x 0<x) 1) inverse (0<→∃rat≤ x 0<x)
  where
  inverse : Σ[ δ ∈ ℚ₊ ] (rat ⟨ δ ⟩₊ ≤ x) → x · recip x 0<x ≡ 1
  inverse (δ , ratδ≤x) =
    x · recip x 0<x
      ≡⟨ cong (x ·_) $ recip≡boundedRecip δ x 0<x ratδ≤x ⟩
    x · boundedRecip δ x
      ≡⟨ cong (_· boundedRecip δ x) $
         sym $ maxComm x (rat ⟨ δ ⟩₊) ∙ ratδ≤x ⟩
    max x (rat ⟨ δ ⟩₊) · boundedRecip δ x
      ≡⟨ boundedRecipInvR δ x ⟩
    1 ∎

#0→isInv : (x : ℝ) → (x < 0) ⊎ (0 < x) → Σ[ y ∈ ℝ ] x · y ≡ 1
#0→isInv x (inr 0<x) = recip x 0<x , recipInvR x 0<x
#0→isInv x (inl x<0) = - recip (- x) negatePositive , inverse
  where
  negatePositive : 0 < - x
  negatePositive = -Flip< {x} {0} x<0

  inverse : x · (- recip (- x) negatePositive) ≡ 1
  inverse =
    x · (- recip (- x) negatePositive)
      ≡⟨ -DistR· x (recip (- x) negatePositive) ⟩
    - (x · recip (- x) negatePositive)
      ≡⟨ sym $ -DistL· x (recip (- x) negatePositive) ⟩
    (- x) · recip (- x) negatePositive
      ≡⟨ recipInvR (- x) negatePositive ⟩
    1 ∎

isInv→#0 : (x y : ℝ) → x · y ≡ 1 → (x < 0) ⊎ (0 < x)
isInv→#0 x y xy≡1 = PT.rec isPropApart bounded (∃abs≤rat y)
  where
  isPropApart : isProp ((x < 0) ⊎ (0 < x))
  isPropApart =
    IsApartness.is-prop-valued
      ( isStrictOrder→isApartnessSymClosure $
        StrictOrderStr.isStrictOrder (snd ℝ<StrictOrder))
      ( x)
      ( 0)

  bounded : Σ[ M ∈ ℚ₊ ] (abs y ≤ rat ⟨ M ⟩₊) → (x < 0) ⊎ (0 < x)
  bounded (M , ∣y∣≤M) =
    PT.rec2
      ( isPropApart)
      ( cuts)
      ( <→rat<∨<rat { ℚ.- ⟨ ε ⟩₊} { 0} x cutNegateBelow0)
      ( <→rat<∨<rat { 0} { ⟨ ε ⟩₊} x (snd ε))
    where
    open OrderedAbGroupReasoning ℝOrderedAbGroup

    ε : ℚ₊
    ε = (M +₊ M) ⁻¹₊

    cutNegateBelow0 : (ℚ.- ⟨ ε ⟩₊) ℚ.< 0
    cutNegateBelow0 = 0<→-<0 ⟨ ε ⟩₊ (snd ε)

    0≤cut : 0 ≤ rat ⟨ ε ⟩₊
    0≤cut =
      <Weaken≤ { 0} { rat ⟨ ε ⟩₊} $
        equivFun (<≃rat< { 0} { ⟨ ε ⟩₊}) (snd ε)

    cuts :
      (rat (ℚ.- ⟨ ε ⟩₊) < x) ⊎ (x < rat 0) →
      (rat 0 < x) ⊎ (x < rat ⟨ ε ⟩₊) →
      (x < 0) ⊎ (0 < x)
    cuts _ (inl 0<x) = inr 0<x
    cuts (inr x<0) _ = inl x<0
    cuts (inl ratNegCut<x) (inr x<ratCut) =
      ⊥.rec $ isIrrefl< 1 oneBelowItself
      where
      negateBelowCut : (- x) ≤ rat ⟨ ε ⟩₊
      negateBelowCut =
        subst
          ( (- x) ≤_)
          ( cong rat $ ℚ.-Invol ⟨ ε ⟩₊)
          ( <Weaken≤ { - x} { - rat (ℚ.- ⟨ ε ⟩₊)} $
            -Flip< { rat (ℚ.- ⟨ ε ⟩₊)} { x} ratNegCut<x)

      absBelowCut : abs x ≤ rat ⟨ ε ⟩₊
      absBelowCut =
        invEq
          ( abs≤≃ { x} { rat ⟨ ε ⟩₊})
          ( <Weaken≤ { x} { rat ⟨ ε ⟩₊} x<ratCut , negateBelowCut)

      unitIsAbsProduct : abs (x · y) ≡ 1
      unitIsAbsProduct =
        abs (x · y)
          ≡⟨ cong abs xy≡1 ⟩
        abs 1
          ≡⟨ abs∘rat 1 ⟩
        rat (absℚ 1)
          ≡⟨ cong rat abs1 ⟩
        1 ∎

      oneBelowItself : 1 < 1
      oneBelowItself = begin<
        1
          ≡→≤⟨ sym unitIsAbsProduct ⟩
        abs (x · y)
          ≡→≤⟨ abs· x y ⟩
        abs x · abs y
          ≤⟨ ·MonoR≤ { abs x} { rat ⟨ ε ⟩₊} { abs y} (0≤abs y) absBelowCut ⟩
        rat ⟨ ε ⟩₊ · abs y
          ≤⟨ ·MonoL≤ { abs y} { rat ⟨ M ⟩₊} { rat ⟨ ε ⟩₊} 0≤cut ∣y∣≤M ⟩
        rat ⟨ ε ⟩₊ · rat ⟨ M ⟩₊
          ≡→≤⟨ rat·rat ⟨ ε ⟩₊ ⟨ M ⟩₊ ⟩
        rat (⟨ ε ⟩₊ ℚ.· ⟨ M ⟩₊)
          <⟨ equivFun
               ( <≃rat<
                 { ⟨ ε ⟩₊ ℚ.· ⟨ M ⟩₊}
                 { ⟨ ε ⟩₊ ℚ.· ⟨ M +₊ M ⟩₊})
               ( ·MonoL<ℚ ⟨ M ⟩₊ ⟨ M +₊ M ⟩₊ ⟨ ε ⟩₊ (snd ε) $
                 <SumLeftPos ⟨ M ⟩₊ ⟨ M ⟩₊ (snd M)) ⟩
        rat (⟨ ε ⟩₊ ℚ.· ⟨ M +₊ M ⟩₊)
          ≡→≤⟨ cong rat $
               ℚ.·Comm ⟨ ε ⟩₊ ⟨ M +₊ M ⟩₊ ∙ ⁻¹inverse (M +₊ M) ⟩
        1 ◾
