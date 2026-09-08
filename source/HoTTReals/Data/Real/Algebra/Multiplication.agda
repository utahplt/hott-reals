module HoTTReals.Data.Real.Algebra.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Rationals using
  ( ℚPremetricSpace)
open import Cubical.Relation.Premetric.Completion.Lift using
  ( continuous≡ ; lipschitz≡)
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Relation.Premetric.Completion.Lift
open import HoTTReals.Relation.Premetric.Instances.Product

open PositiveRationals
open OrderedAbGroupTheory ℝOrderedAbGroup using (abs)
open OrderedAbGroupTheory ℚOrderedAbGroup using () renaming (abs to absℚ)
open LiftCompleteCodomain ℚPremetricSpace ℝPremetricSpace isCompleteℝ

scaleBound : ℚ → ℚ₊
fst (scaleBound q) = absℚ q ℚ.+ 1
snd (scaleBound q) = {!!}

scaleRatIsLipschitzWith :
  (q : ℚ) →
  IsLipschitzWith
    ( snd ℚPremetricSpace)
    ( rat ∘ (q ℚ.·_))
    ( snd ℝPremetricSpace)
    ( scaleBound q)
scaleRatIsLipschitzWith q = {!!}

private
  scaleLift :
    (q : ℚ) →
    Σ[ f ∈ (ℝ → ℝ) ]
      IsLipschitzWith (snd ℝPremetricSpace) f (snd ℝPremetricSpace) (scaleBound q)
  scaleLift q =
    liftLipschitzWith (scaleBound q) (rat ∘ (q ℚ.·_)) (scaleRatIsLipschitzWith q)

scale : ℚ → ℝ → ℝ
scale q = fst $ scaleLift q

scaleIsLipschitzWith :
  (q : ℚ) →
  IsLipschitzWith (snd ℝPremetricSpace) (scale q) (snd ℝPremetricSpace) (scaleBound q)
scaleIsLipschitzWith q = snd $ scaleLift q

scaleᴸ : ℚ → L[ ℝPremetricSpace , ℝPremetricSpace ]
scaleᴸ q = scale q , ∣ scaleBound q , scaleIsLipschitzWith q ∣₁

scale∘rat : (q r : ℚ) → scale q (rat r) ≡ rat (q ℚ.· r)
scale∘rat q r = refl

scaleDistL- : (q r : ℚ) (u : ℝ) → (scale q u) - (scale r u) ≡ scale (q ℚ.- r) u
scaleDistL- q r u = {!!}

absScale : (q : ℚ) (u : ℝ) → abs (scale q u) ≡ scale (absℚ q) (abs u)
absScale q u = {!!}

scaleDistR- : (q : ℚ) (u w : ℝ) → scale q (u - w) ≡ (scale q u) - (scale q w)
scaleDistR- q u w = {!!}

0≤scale : {q : ℚ} {u : ℝ} → 0 ℚ.≤ q → 0 ≤ u → 0 ≤ scale q u
0≤scale {q} {u} 0≤q 0≤u = {!!}

scaleMono≤ : {q : ℚ} {u w : ℝ} → 0 ℚ.≤ q → u ≤ w → scale q u ≤ scale q w
scaleMono≤ {q} {u} {w} 0≤q u≤w = {!!}

flipScaleIsLipschitzWith :
  (L : ℚ₊) (v : ℝ) →
  abs v ≤ rat ⟨ L ⟩₊ →
  IsLipschitzWith (snd ℚPremetricSpace) (flip scale v) (snd ℝPremetricSpace) L
flipScaleIsLipschitzWith L v ∣v∣≤L = {!!}

private
  boundedMulLift :
    (L : ℚ₊) (v : ℝ) →
    abs v ≤ rat ⟨ L ⟩₊ →
    Σ[ f ∈ (ℝ → ℝ) ] IsLipschitzWith (snd ℝPremetricSpace) f (snd ℝPremetricSpace) L
  boundedMulLift L v ∣v∣≤L =
    liftLipschitzWith L (flip scale v) (flipScaleIsLipschitzWith L v ∣v∣≤L)

boundedMul : (L : ℚ₊) (v : ℝ) → abs v ≤ rat ⟨ L ⟩₊ → ℝ → ℝ
boundedMul L v ∣v∣≤L = fst $ boundedMulLift L v ∣v∣≤L

boundedMulIsLipschitzWith :
  (L : ℚ₊) (v : ℝ) (∣v∣≤L : abs v ≤ rat ⟨ L ⟩₊) →
  IsLipschitzWith
    ( snd ℝPremetricSpace)
    ( boundedMul L v ∣v∣≤L)
    ( snd ℝPremetricSpace)
    ( L)
boundedMulIsLipschitzWith L v ∣v∣≤L = snd $ boundedMulLift L v ∣v∣≤L

boundedMul∘rat :
  (L : ℚ₊) (v : ℝ) (∣v∣≤L : abs v ≤ rat ⟨ L ⟩₊) (q : ℚ) →
  boundedMul L v ∣v∣≤L (rat q) ≡ scale q v
boundedMul∘rat L v ∣v∣≤L q = refl

∃abs≤rat : (x : ℝ) → ∃[ L ∈ ℚ₊ ] (abs x ≤ rat ⟨ L ⟩₊)
∃abs≤rat x = {!!}

boundedMul≡ :
  (L M : ℚ₊) (v : ℝ)
  (∣v∣≤L : abs v ≤ rat ⟨ L ⟩₊) (∣v∣≤M : abs v ≤ rat ⟨ M ⟩₊) (u : ℝ) →
  boundedMul L v ∣v∣≤L u ≡ boundedMul M v ∣v∣≤M u
boundedMul≡ L M v ∣v∣≤L ∣v∣≤M u = {!!}

_·_ : ℝ → ℝ → ℝ
u · v =
  PT.SetElim.rec→Set
    ( isSetℭ)
    ( λ (L , ∣v∣≤L) → boundedMul L v ∣v∣≤L u)
    ( λ (L , ∣v∣≤L) (M , ∣v∣≤M) → boundedMul≡ L M v ∣v∣≤L ∣v∣≤M u)
    ( ∃abs≤rat v)

infixl 7 _·_

·≡boundedMul :
  (L : ℚ₊) (u v : ℝ) (∣v∣≤L : abs v ≤ rat ⟨ L ⟩₊) →
  u · v ≡ boundedMul L v ∣v∣≤L u
·≡boundedMul L u v ∣v∣≤L = {!!}

rat·rat : (q r : ℚ) → rat q · rat r ≡ rat (q ℚ.· r)
rat·rat q r = {!!}

rat·≡scale : (q : ℚ) (x : ℝ) → rat q · x ≡ scale q x
rat·≡scale q x = {!!}

·IsLipschitzWithR :
  (L : ℚ₊) (v : ℝ) →
  abs v ≤ rat ⟨ L ⟩₊ →
  IsLipschitzWith (snd ℝPremetricSpace) (_· v) (snd ℝPremetricSpace) L
·IsLipschitzWithR L v ∣v∣≤L = {!!}

·ᶜ[_] : ℝ → C[ ℝPremetricSpace , ℝPremetricSpace ]
fst ·ᶜ[ v ] = _· v
snd ·ᶜ[ v ] = {!!}

·rat≡scale : (q : ℚ) (x : ℝ) → x · rat q ≡ scale q x
·rat≡scale q x = {!!}

·DistR- : (x y z : ℝ) → x · (y - z) ≡ (x · y) - (x · z)
·DistR- x y z = {!!}

abs· : (x y : ℝ) → abs (x · y) ≡ abs x · abs y
abs· x y = {!!}

0≤· : {x y : ℝ} → 0 ≤ x → 0 ≤ y → 0 ≤ x · y
0≤· {x} {y} 0≤x 0≤y = {!!}

·MonoL≤ : {y z a : ℝ} → 0 ≤ a → y ≤ z → a · y ≤ a · z
·MonoL≤ {y} {z} {a} 0≤a y≤z = {!!}

·IsLipschitzWithL :
  (L : ℚ₊) (u : ℝ) →
  abs u ≤ rat ⟨ L ⟩₊ →
  IsLipschitzWith (snd ℝPremetricSpace) (u ·_) (snd ℝPremetricSpace) L
·IsLipschitzWithL L u ∣u∣≤L = {!!}

[_]·ᶜ : ℝ → C[ ℝPremetricSpace , ℝPremetricSpace ]
fst [ u ]·ᶜ = u ·_
snd [ u ]·ᶜ = {!!}

·Comm : (x y : ℝ) → x · y ≡ y · x
·Comm x y = {!!}

·Assoc : (x y z : ℝ) → x · (y · z) ≡ (x · y) · z
·Assoc x y z = {!!}

·IdR : (x : ℝ) → x · 1 ≡ x
·IdR x = {!!}

·AnnihilR : (x : ℝ) → x · 0 ≡ 0
·AnnihilR x = {!!}

-DistR· : (x y : ℝ) → x · (- y) ≡ - (x · y)
-DistR· x y = {!!}

·DistR+ : (x y z : ℝ) → x · (y + z) ≡ (x · y) + (x · z)
·DistR+ x y z = {!!}

ℝCommRing : CommRing ℓ-zero
fst ℝCommRing = ℝ
CommRingStr.0r (snd ℝCommRing) = 0
CommRingStr.1r (snd ℝCommRing) = 1
CommRingStr._+_ (snd ℝCommRing) = _+_
CommRingStr._·_ (snd ℝCommRing) = _·_
CommRingStr.-_ (snd ℝCommRing) = -_
CommRingStr.isCommRing (snd ℝCommRing) = isCommRingℝ
  where opaque
    isCommRingℝ : IsCommRing 0 1 _+_ _·_ (-_)
    isCommRingℝ =
      makeIsCommRing isSetℭ +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm
