module HoTTReals.Data.Real.Algebra.Reciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

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
  ( <SumLeftPos ; abs1) renaming (·MonoL≤ to ·MonoL≤ℚ ; ·MonoL< to ·MonoL<ℚ)
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
IsLipschitzWith.pres≈ (boundedRecipℚIsLipschitzWith δ) q r ε q≈r = {!!}

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
boundedRecipMax δ ε δ≤ε x = {!!}

boundedRecip≡ :
  (δ ε : ℚ₊) (x : ℝ) → rat ⟨ δ ⟩₊ ≤ x → rat ⟨ ε ⟩₊ ≤ x →
  boundedRecip δ x ≡ boundedRecip ε x
boundedRecip≡ δ ε x ratδ≤x ratε≤x = {!!}

0<→∃rat≤ : (x : ℝ) → 0 < x → ∃[ δ ∈ ℚ₊ ] (rat ⟨ δ ⟩₊ ≤ x)
0<→∃rat≤ x 0<x = {!!}

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
  recip≡boundedRecip δ x 0<x ratδ≤x = {!!}

boundedRecipInvR :
  (δ : ℚ₊) (x : ℝ) → max x (rat ⟨ δ ⟩₊) · boundedRecip δ x ≡ 1
boundedRecipInvR δ x = {!!}

recipInvR : (x : ℝ) (0<x : 0 < x) → x · recip x 0<x ≡ 1
recipInvR x 0<x = {!!}

#0→isInv : (x : ℝ) → (x < 0) ⊎ (0 < x) → Σ[ y ∈ ℝ ] x · y ≡ 1
#0→isInv x x#0 = {!!}

isInv→#0 : (x y : ℝ) → x · y ≡ 1 → (x < 0) ⊎ (0 < x)
isInv→#0 x y xy≡1 = {!!}
