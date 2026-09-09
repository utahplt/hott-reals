module HoTTReals.Data.Real.Algebra.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
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
open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Relation.Premetric.Completion.Lift
open import HoTTReals.Relation.Premetric.Instances.Product

open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing using
  ( ·MonoL< ; ≤SumLeftNonNeg ; <SumLeftPos ; 0≤1)
open HoTTRealsOrderedCommRingProperties.OrderedCommRingTheory ℚOrderedCommRing
  using () renaming (abs· to abs·ℚ)
open RingTheory (OrderedCommRing→Ring ℚOrderedCommRing) using () renaming
  ( ·DistR- to ·DistR-ℚ)
open OrderedAbGroupTheory ℝOrderedAbGroup using
  ( abs ; 0≤abs ; 0≤→abs≡id ; ≤→0≤Δ ; 0≤Δ→≤)
open OrderedAbGroupTheory ℚOrderedAbGroup using () renaming
  ( abs to absℚ ; 0≤abs to 0≤absℚ ; 0≤→abs≡id to 0≤→absℚ≡id)
open GroupTheory (AbGroup→Group ℝAbGroup) using (invInv)
open LiftCompleteCodomain ℚPremetricSpace ℝPremetricSpace isCompleteℝ

private
  variable
    ℓM ℓM' : Level

scaleBound : ℚ → ℚ₊
fst (scaleBound q) = absℚ q ℚ.+ 1
snd (scaleBound q) =
  ℚ.isTrans≤< 0 (absℚ q) (absℚ q ℚ.+ 1)
    ( 0≤absℚ q)
    ( <SumLeftPos (absℚ q) 1 (snd 1₊))

scaleRatIsLipschitzWith :
  (q : ℚ) →
  IsLipschitzWith
    ( snd ℚPremetricSpace)
    ( rat ∘ (q ℚ.·_))
    ( snd ℝPremetricSpace)
    ( scaleBound q)
IsLipschitzWith.pres≈ (scaleRatIsLipschitzWith q) r s ε r≈s =
  invEq
    ( ∼≃B { rat (q ℚ.· r)} { rat (q ℚ.· s)} { scaleBound q ·₊ ε})
    ( bound)
  where
  open OrderedCommRingReasoning ℚOrderedCommRing

  bound : absℚ ((q ℚ.· r) ℚ.- (q ℚ.· s)) ℚ.< ⟨ scaleBound q ·₊ ε ⟩₊
  bound = begin<
    absℚ ((q ℚ.· r) ℚ.- (q ℚ.· s))
      ≡→≤⟨ cong absℚ $ sym $ ·DistR-ℚ q r s ⟩
    absℚ (q ℚ.· (r ℚ.- s))
      ≡→≤⟨ abs·ℚ q (r ℚ.- s) ⟩
    absℚ q ℚ.· absℚ (r ℚ.- s)
      ≤⟨ ℚ.≤-·o (absℚ q) ⟨ scaleBound q ⟩₊ (absℚ $ r ℚ.- s)
           ( 0≤absℚ $ r ℚ.- s)
           ( ≤SumLeftNonNeg (absℚ q) 1 0≤1) ⟩
    ⟨ scaleBound q ⟩₊ ℚ.· absℚ (r ℚ.- s)
      <⟨ ·MonoL< (absℚ $ r ℚ.- s) ⟨ ε ⟩₊ ⟨ scaleBound q ⟩₊
           ( snd $ scaleBound q)
           ( r≈s) ⟩
    ⟨ scaleBound q ⟩₊ ℚ.· ⟨ ε ⟩₊ ◾

private
  scaleLift :
    (q : ℚ) →
    Σ[ f ∈ (ℝ → ℝ) ]
      IsLipschitzWith (snd ℝPremetricSpace) f (snd ℝPremetricSpace)
        ( scaleBound q)
  scaleLift q =
    liftLipschitzWith (scaleBound q) (rat ∘ (q ℚ.·_))
      ( scaleRatIsLipschitzWith q)

scale : ℚ → ℝ → ℝ
scale q = fst $ scaleLift q

scaleIsLipschitzWith :
  (q : ℚ) →
  IsLipschitzWith (snd ℝPremetricSpace) (scale q) (snd ℝPremetricSpace)
    ( scaleBound q)
scaleIsLipschitzWith q = snd $ scaleLift q

scaleᴸ : ℚ → L[ ℝPremetricSpace , ℝPremetricSpace ]
scaleᴸ q = scale q , ∣ scaleBound q , scaleIsLipschitzWith q ∣₁

scale∘rat : (q r : ℚ) → scale q (rat r) ≡ rat (q ℚ.· r)
scale∘rat q r = refl

scaleDistL- : (q r : ℚ) (u : ℝ) → (scale q u) - (scale r u) ≡ scale (q ℚ.- r) u
scaleDistL- q r u =
  lipschitz≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( composeL₂ _ _ _ (scaleᴸ q) (scaleᴸ r) (NE→NE₂ _ _ _ -₂ⁿ))
    ( scaleᴸ (q ℚ.- r))
    ( λ s → cong rat $ distributeScalars s)
    ( u)
  where
  distributeScalars :
    (s : ℚ) → (q ℚ.· s) ℚ.- (r ℚ.· s) ≡ (q ℚ.- r) ℚ.· s
  distributeScalars s = ℚ!

absScale : (q : ℚ) (u : ℝ) → abs (scale q u) ≡ scale (absℚ q) (abs u)
absScale q u =
  lipschitz≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( NE→L absⁿ ∘L scaleᴸ q)
    ( scaleᴸ (absℚ q) ∘L NE→L absⁿ)
    ( λ r → cong rat $ abs·ℚ q r)
    ( u)

scaleDistR- : (q : ℚ) (u w : ℝ) → scale q (u - w) ≡ (scale q u) - (scale q w)
scaleDistR- q u w =
  continuous₂≡
    ( ℚPremetricSpace)
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( λ x y → scale q (x - y))
    ( λ x y → scale q x - scale q y)
    ( λ x → snd $ L→C $ scaleᴸ q ∘L NE→L ([ x ]+ⁿ ∘NE -ⁿ))
    ( λ y → snd $ L→C $ scaleᴸ q ∘L NE→L +ⁿ[ - y ])
    ( λ x → snd $ L→C $ NE→L ([ scale q x ]+ⁿ ∘NE -ⁿ) ∘L scaleᴸ q)
    ( λ y → snd $ L→C $ NE→L +ⁿ[ - scale q y ] ∘L scaleᴸ q)
    ( λ r s → cong rat $ distributeDifference r s)
    ( u)
    ( w)
  where
  distributeDifference :
    (r s : ℚ) → q ℚ.· (r ℚ.- s) ≡ (q ℚ.· r) ℚ.- (q ℚ.· s)
  distributeDifference r s = ℚ!

0≤scale : {q : ℚ} {u : ℝ} → 0 ℚ.≤ q → 0 ≤ u → 0 ≤ scale q u
0≤scale {q} {u} 0≤q 0≤u =
  subst
    ( 0 ≤_)
    ( absScale q u ∙ cong₂ scale (0≤→absℚ≡id 0≤q) (0≤→abs≡id 0≤u))
    ( 0≤abs $ scale q u)

scaleMono≤ : {q : ℚ} {u w : ℝ} → 0 ℚ.≤ q → u ≤ w → scale q u ≤ scale q w
scaleMono≤ {q} {u} {w} 0≤q u≤w =
  0≤Δ→≤ (scale q u) (scale q w) $
    subst (0 ≤_) (scaleDistR- q w u) (0≤scale 0≤q $ ≤→0≤Δ u w u≤w)

flipScaleIsLipschitzWith :
  (L : ℚ₊) (v : ℝ) →
  abs v ≤ rat ⟨ L ⟩₊ →
  IsLipschitzWith (snd ℚPremetricSpace) (flip scale v) (snd ℝPremetricSpace) L
IsLipschitzWith.pres≈ (flipScaleIsLipschitzWith L v ∣v∣≤L) q r ε q≈r =
  invEq
    ( ∼≃abs< { scale q v} { scale r v} { L ·₊ ε})
    ( isTrans≤<
      { abs (scale q v - scale r v)}
      { rat (absℚ (q ℚ.- r) ℚ.· ⟨ L ⟩₊)}
      { rat ⟨ L ·₊ ε ⟩₊}
      ( bound)
      ( strict))
  where
  open OrderedAbGroupReasoning ℝOrderedAbGroup

  bound : abs (scale q v - scale r v) ≤ rat (absℚ (q ℚ.- r) ℚ.· ⟨ L ⟩₊)
  bound = begin≤
    abs (scale q v - scale r v)
      ≡→≤⟨ cong abs $ scaleDistL- q r v ⟩
    abs (scale (q ℚ.- r) v)
      ≡→≤⟨ absScale (q ℚ.- r) v ⟩
    scale (absℚ (q ℚ.- r)) (abs v)
      ≤⟨ scaleMono≤ { absℚ (q ℚ.- r)} { abs v} { rat ⟨ L ⟩₊}
           ( 0≤absℚ $ q ℚ.- r)
           ( ∣v∣≤L) ⟩
    scale (absℚ (q ℚ.- r)) (rat ⟨ L ⟩₊)
      ≡→≤⟨ scale∘rat (absℚ $ q ℚ.- r) ⟨ L ⟩₊ ⟩
    rat (absℚ (q ℚ.- r) ℚ.· ⟨ L ⟩₊) ◾

  strict : rat (absℚ (q ℚ.- r) ℚ.· ⟨ L ⟩₊) < rat ⟨ L ·₊ ε ⟩₊
  strict =
    equivFun
      ( <≃rat< { absℚ (q ℚ.- r) ℚ.· ⟨ L ⟩₊} { ⟨ L ·₊ ε ⟩₊})
      ( subst
        ( absℚ (q ℚ.- r) ℚ.· ⟨ L ⟩₊ ℚ.<_)
        ( ℚ.·Comm ⟨ ε ⟩₊ ⟨ L ⟩₊)
        ( ℚ.<-·o (absℚ $ q ℚ.- r) ⟨ ε ⟩₊ ⟨ L ⟩₊ (snd L) q≈r))

private
  boundedMulLift :
    (L : ℚ₊) (v : ℝ) →
    abs v ≤ rat ⟨ L ⟩₊ →
    Σ[ f ∈ (ℝ → ℝ) ]
      IsLipschitzWith (snd ℝPremetricSpace) f (snd ℝPremetricSpace) L
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
∃abs≤rat x =
  PT.map
    ( λ (q , ∣x∣<ratq) → q , <Weaken≤ { abs x} { rat ⟨ q ⟩₊} ∣x∣<ratq)
    ( ∃abs<rat x)

boundedMul≡ :
  (L M : ℚ₊) (v : ℝ)
  (∣v∣≤L : abs v ≤ rat ⟨ L ⟩₊) (∣v∣≤M : abs v ≤ rat ⟨ M ⟩₊) (u : ℝ) →
  boundedMul L v ∣v∣≤L u ≡ boundedMul M v ∣v∣≤M u
boundedMul≡ L M v ∣v∣≤L ∣v∣≤M u =
  lipschitz≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( boundedMul L v ∣v∣≤L , ∣ L , boundedMulIsLipschitzWith L v ∣v∣≤L ∣₁)
    ( boundedMul M v ∣v∣≤M , ∣ M , boundedMulIsLipschitzWith M v ∣v∣≤M ∣₁)
    ( λ q → refl)
    ( u)

opaque
  _·_ : ℝ → ℝ → ℝ
  u · v =
    PT.SetElim.rec→Set
      ( isSetℭ)
      ( λ (L , ∣v∣≤L) → boundedMul L v ∣v∣≤L u)
      ( λ (L , ∣v∣≤L) (M , ∣v∣≤M) → boundedMul≡ L M v ∣v∣≤L ∣v∣≤M u)
      ( ∃abs≤rat v)

infixl 7 _·_

opaque
  unfolding _·_

  ·≡boundedMul :
    (L : ℚ₊) (u v : ℝ) (∣v∣≤L : abs v ≤ rat ⟨ L ⟩₊) →
    u · v ≡ boundedMul L v ∣v∣≤L u
  ·≡boundedMul L u v ∣v∣≤L =
    PT.SetElim.helper
      ( isSetℭ)
      ( λ (M , ∣v∣≤M) → boundedMul M v ∣v∣≤M u)
      ( λ (M , ∣v∣≤M) (K , ∣v∣≤K) → boundedMul≡ M K v ∣v∣≤M ∣v∣≤K u)
      ( ∃abs≤rat v)
      ( ∣ L , ∣v∣≤L ∣₁)

  rat·rat : (q r : ℚ) → rat q · rat r ≡ rat (q ℚ.· r)
  rat·rat q r = refl

rat·≡scale : (q : ℚ) (x : ℝ) → rat q · x ≡ scale q x
rat·≡scale q x =
  PT.rec
    ( isSetℭ (rat q · x) (scale q x))
    ( λ (L , ∣x∣≤L) → ·≡boundedMul L (rat q) x ∣x∣≤L)
    ( ∃abs≤rat x)

·IsLipschitzWithR :
  (L : ℚ₊) (v : ℝ) →
  abs v ≤ rat ⟨ L ⟩₊ →
  IsLipschitzWith (snd ℝPremetricSpace) (_· v) (snd ℝPremetricSpace) L
·IsLipschitzWithR L v ∣v∣≤L =
  subst
    ( λ f → IsLipschitzWith (snd ℝPremetricSpace) f (snd ℝPremetricSpace) L)
    ( sym $ funExt λ u → ·≡boundedMul L u v ∣v∣≤L)
    ( boundedMulIsLipschitzWith L v ∣v∣≤L)

·ᶜ[_] : ℝ → C[ ℝPremetricSpace , ℝPremetricSpace ]
fst ·ᶜ[ v ] = _· v
snd ·ᶜ[ v ] = isLipschitz→isContinuous _ (_· v) _ $ PT.map
  ( λ (L , ∣v∣≤L) → (L , ·IsLipschitzWithR L v ∣v∣≤L))
  ( ∃abs≤rat v)

·rat≡scale : (q : ℚ) (x : ℝ) → x · rat q ≡ scale q x
·rat≡scale q x =
  continuous≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( ·ᶜ[ rat q ])
    ( L→C $ scaleᴸ q)
    ( λ s → rat·rat s q ∙ cong rat (ℚ.·Comm s q))
    ( x)

·DistR- : (x y z : ℝ) → x · (y - z) ≡ (x · y) - (x · z)
·DistR- x y z =
  continuous≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( ·ᶜ[ y - z ])
    ( composeC₂ _ _ _ ·ᶜ[ y ] ·ᶜ[ z ] (NE→NE₂ _ _ _ -₂ⁿ))
    ( λ q →
      rat q · (y - z)
        ≡⟨ rat·≡scale q (y - z) ⟩
      scale q (y - z)
        ≡⟨ scaleDistR- q y z ⟩
      scale q y - scale q z
        ≡⟨ cong₂ _-_ (sym $ rat·≡scale q y) (sym $ rat·≡scale q z) ⟩
      (rat q · y) - (rat q · z) ∎)
    ( x)

abs· : (x y : ℝ) → abs (x · y) ≡ abs x · abs y
abs· x y =
  continuous≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( NE→C absⁿ ∘C ·ᶜ[ y ])
    ( ·ᶜ[ abs y ] ∘C NE→C absⁿ)
    ( λ q →
      abs (rat q · y)
        ≡⟨ cong abs $ rat·≡scale q y ⟩
      abs (scale q y)
        ≡⟨ absScale q y ⟩
      scale (absℚ q) (abs y)
        ≡⟨ sym $ rat·≡scale (absℚ q) (abs y) ⟩
      abs (rat q) · abs y ∎)
    ( x)

0≤· : {x y : ℝ} → 0 ≤ x → 0 ≤ y → 0 ≤ x · y
0≤· {x} {y} 0≤x 0≤y =
  subst
    ( 0 ≤_)
    ( abs· x y ∙ cong₂ _·_ (0≤→abs≡id 0≤x) (0≤→abs≡id 0≤y))
    ( 0≤abs $ x · y)

·MonoL≤ : {y z a : ℝ} → 0 ≤ a → y ≤ z → a · y ≤ a · z
·MonoL≤ {y} {z} {a} 0≤a y≤z =
  0≤Δ→≤ (a · y) (a · z) $
    subst (0 ≤_) (·DistR- a z y) (0≤· 0≤a $ ≤→0≤Δ y z y≤z)

-- TODO: The fork declares no fixity for _∼[_]_, so it sits at Agda's
-- default infixl 20, tighter than _·_ at 7, and the endpoints of the
-- closeness below need parentheses they would not otherwise take. Declare
-- infix 4 _∼[_]_ on the fork as 16c158d20 did for ℝ's arithmetic, then
-- sweep source/ for the parenthesization artifacts of precedence 20.
·IsLipschitzWithL :
  (L : ℚ₊) (u : ℝ) →
  abs u ≤ rat ⟨ L ⟩₊ →
  IsLipschitzWith (snd ℝPremetricSpace) (u ·_) (snd ℝPremetricSpace) L
IsLipschitzWith.pres≈ (·IsLipschitzWithL L u ∣u∣≤L) v w δ v∼w =
  PT.rec (isProp∼ (u · v) (L ·₊ δ) (u · w)) roundedCase (isRounded∼ v w δ v∼w)
  where
  open OrderedAbGroupReasoning ℝOrderedAbGroup

  roundedCase :
    Σ[ θ ∈ ℚ₊ ] (θ <₊ δ) × (v ∼[ θ ] w) → (u · v) ∼[ L ·₊ δ ] (u · w)
  roundedCase (θ , θ<δ , v∼θw) =
    invEq
      ( ∼≃abs< { u · v} { u · w} { L ·₊ δ})
      ( isTrans≤<
        { abs ((u · v) - (u · w))}
        { rat (⟨ θ ⟩₊ ℚ.· ⟨ L ⟩₊)}
        { rat ⟨ L ·₊ δ ⟩₊}
        ( bound)
        ( strict))
    where
    bound : abs ((u · v) - (u · w)) ≤ rat (⟨ θ ⟩₊ ℚ.· ⟨ L ⟩₊)
    bound = begin≤
      abs ((u · v) - (u · w))
        ≡→≤⟨ cong abs $ sym $ ·DistR- u v w ⟩
      abs (u · (v - w))
        ≡→≤⟨ abs· u (v - w) ⟩
      abs u · abs (v - w)
        ≤⟨ ·MonoL≤ { abs (v - w)} { rat ⟨ θ ⟩₊} { abs u}
             ( 0≤abs u)
             ( <Weaken≤ { abs (v - w)} { rat ⟨ θ ⟩₊} $
               equivFun (∼≃abs< { v} { w} { θ}) v∼θw) ⟩
      abs u · rat ⟨ θ ⟩₊
        ≡→≤⟨ ·rat≡scale ⟨ θ ⟩₊ (abs u) ⟩
      scale ⟨ θ ⟩₊ (abs u)
        ≤⟨ scaleMono≤ { ⟨ θ ⟩₊} { abs u} { rat ⟨ L ⟩₊}
             ( ℚ.<Weaken≤ 0 ⟨ θ ⟩₊ $ snd θ)
             ( ∣u∣≤L) ⟩
      scale ⟨ θ ⟩₊ (rat ⟨ L ⟩₊)
        ≡→≤⟨ scale∘rat ⟨ θ ⟩₊ ⟨ L ⟩₊ ⟩
      rat (⟨ θ ⟩₊ ℚ.· ⟨ L ⟩₊) ◾

    strict : rat (⟨ θ ⟩₊ ℚ.· ⟨ L ⟩₊) < rat ⟨ L ·₊ δ ⟩₊
    strict =
      equivFun
        ( <≃rat< { ⟨ θ ⟩₊ ℚ.· ⟨ L ⟩₊} { ⟨ L ·₊ δ ⟩₊})
        ( subst
          ( ⟨ θ ⟩₊ ℚ.· ⟨ L ⟩₊ ℚ.<_)
          ( ℚ.·Comm ⟨ δ ⟩₊ ⟨ L ⟩₊)
          ( ℚ.<-·o ⟨ θ ⟩₊ ⟨ δ ⟩₊ ⟨ L ⟩₊ (snd L) θ<δ))

[_]·ᶜ : ℝ → C[ ℝPremetricSpace , ℝPremetricSpace ]
fst [ u ]·ᶜ = u ·_
snd [ u ]·ᶜ = isLipschitz→isContinuous _ (u ·_) _ $ PT.map
  ( λ (L , ∣u∣≤L) → (L , ·IsLipschitzWithL L u ∣u∣≤L))
  ( ∃abs≤rat u)

_·ᶜ_ :
  {M : PremetricSpace ℓM ℓM'} →
  C[ M , ℝPremetricSpace ] → C[ M , ℝPremetricSpace ] →
  C[ M , ℝPremetricSpace ]
fst (f ·ᶜ g) a = fst f a · fst g a
snd (f ·ᶜ g) = {!!}

infixl 7 _·ᶜ_

·Comm : (x y : ℝ) → x · y ≡ y · x
·Comm x y =
  continuous≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( ·ᶜ[ y ])
    ( [ y ]·ᶜ)
    ( λ q → rat·≡scale q y ∙ sym (·rat≡scale q y))
    ( x)

·Assoc : (x y z : ℝ) → x · (y · z) ≡ (x · y) · z
·Assoc x y z =
  continuous₃≡
    ( ℚPremetricSpace)
    ( ℚPremetricSpace)
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( λ a b c → a · (b · c))
    ( λ a b c → (a · b) · c)
    ( λ a b → snd $ [ a ]·ᶜ ∘C [ b ]·ᶜ)
    ( λ a c → snd $ [ a ]·ᶜ ∘C ·ᶜ[ c ])
    ( λ b c → snd ·ᶜ[ b · c ])
    ( λ a b → snd [ a · b ]·ᶜ)
    ( λ a c → snd $ ·ᶜ[ c ] ∘C [ a ]·ᶜ)
    ( λ b c → snd $ ·ᶜ[ c ] ∘C ·ᶜ[ b ])
    ( associateRationals)
    ( x)
    ( y)
    ( z)
  where
  associateRationals :
    (q r s : ℚ) → rat q · (rat r · rat s) ≡ (rat q · rat r) · rat s
  associateRationals q r s =
    rat q · (rat r · rat s)
      ≡⟨ cong (rat q ·_) (rat·rat r s) ⟩
    rat q · rat (r ℚ.· s)
      ≡⟨ rat·rat q (r ℚ.· s) ⟩
    rat (q ℚ.· (r ℚ.· s))
      ≡⟨ cong rat (ℚ.·Assoc q r s) ⟩
    rat ((q ℚ.· r) ℚ.· s)
      ≡⟨ sym (rat·rat (q ℚ.· r) s) ⟩
    rat (q ℚ.· r) · rat s
      ≡⟨ cong (_· rat s) (sym (rat·rat q r)) ⟩
    (rat q · rat r) · rat s ∎

·IdR : (x : ℝ) → x · 1 ≡ x
·IdR x =
  continuous≡
    ( ℚPremetricSpace)
    ( ℝPremetricSpace)
    ( ·ᶜ[ 1 ])
    ( idᶜ)
    ( λ q → rat·rat q 1 ∙ cong rat (ℚ.·IdR q))
    ( x)

·AnnihilR : (x : ℝ) → x · 0 ≡ 0
·AnnihilR x =
  x · 0
    ≡⟨ cong (x ·_) (sym (+InvR 0)) ⟩
  x · (0 - 0)
    ≡⟨ ·DistR- x 0 0 ⟩
  (x · 0) - (x · 0)
    ≡⟨ +InvR (x · 0) ⟩
  0 ∎

-DistR· : (x y : ℝ) → x · (- y) ≡ - (x · y)
-DistR· x y =
  x · (- y)
    ≡⟨ cong (x ·_) (sym (+IdL (- y))) ⟩
  x · (0 - y)
    ≡⟨ ·DistR- x 0 y ⟩
  (x · 0) - (x · y)
    ≡⟨ cong (_- (x · y)) (·AnnihilR x) ⟩
  0 - (x · y)
    ≡⟨ +IdL (- (x · y)) ⟩
  - (x · y) ∎

·DistR+ : (x y z : ℝ) → x · (y + z) ≡ (x · y) + (x · z)
·DistR+ x y z =
  x · (y + z)
    ≡⟨ cong (x ·_) (cong (y +_) (sym (invInv z))) ⟩
  x · (y - (- z))
    ≡⟨ ·DistR- x y (- z) ⟩
  (x · y) - (x · (- z))
    ≡⟨ cong (λ w → (x · y) - w) (-DistR· x z) ⟩
  (x · y) - (- (x · z))
    ≡⟨ cong ((x · y) +_) (invInv (x · z)) ⟩
  (x · y) + (x · z) ∎

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
      makeIsCommRing
        ( isSetℭ)
        ( +Assoc)
        ( +IdR)
        ( +InvR)
        ( +Comm)
        ( ·Assoc)
        ( ·IdR)
        ( ·DistR+)
        ( ·Comm)
