module HoTTReals.Data.Real.Order.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.Functions.Logic using (_⊔′_)

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Lift
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.OrderedCommRing.Properties
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Relation.Premetric.Instances.Product
open import HoTTReals.Relation.Premetric.Mappings

open BinaryRelation
open PositiveRationals

-DistMin : (x y : ℝ) → - min x y ≡ max (- x) (- y)
-DistMin =
  nonExpansive₂≡
    ( _)
    ( _)
    ( _)
    ( NE₂[_,_,_].makeNE₂ -minNE₂)
    ( NE₂[_,_,_].makeNE₂ max-NE₂)
    ( λ q r → cong rat (OrderedCommRingTheory.-⊓ ℚOrderedCommRing q r))
  where
  open NE₂[_,_,_]

  -minNE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
  fun -minNE₂ x y = - min x y
  lNE -minNE₂ y   = snd (-ⁿ ∘NE minⁿ[ y ])
  rNE -minNE₂ x   = snd (-ⁿ ∘NE [ x ]minⁿ)

  max-NE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
  fun max-NE₂ x y = max (- x) (- y)
  lNE max-NE₂ y   = snd (maxⁿ[ - y ] ∘NE -ⁿ)
  rNE max-NE₂ x   = snd ([ - x ]maxⁿ ∘NE -ⁿ)

-Flip≤ : {x y : ℝ} → x ≤ y → - y ≤ - x
-Flip≤ {x} {y} x≤y =
  max (- y) (- x)
    ≡⟨ maxComm (- y) (- x) ⟩
  max (- x) (- y)
    ≡⟨ sym (-DistMin x y) ⟩
  - min x y
    ≡⟨ cong -_ (sym (equivFun (≤≃min {x} {y}) x≤y)) ⟩
  - x ∎

+DistRMax :
  (a x y : ℝ) → a + max x y ≡ max (a + x) (a + y)
+DistRMax a =
  nonExpansive₂≡
    ( _)
    ( _)
    ( _)
    ( NE₂[_,_,_].makeNE₂ +maxNE₂)
    ( NE₂[_,_,_].makeNE₂ max+NE₂)
    ( λ q r →
      lipschitz≡
        ( _)
        ( _)
        ( NE→L +ⁿ[ max (rat q) (rat r) ])
        ( composeNE₂ _ _ _ +ⁿ[ rat q ] +ⁿ[ rat r ] maxNE₂)
        ( λ s →
          cong rat
            ( s ℚ.+ ℚ.max q r
                ≡⟨ ℚ.+Comm s (ℚ.max q r) ⟩
              ℚ.max q r ℚ.+ s
                ≡⟨ OrderedCommRingTheory.+DistL⊔ ℚOrderedCommRing q r s ⟩
              ℚ.max (q ℚ.+ s) (r ℚ.+ s)
                ≡⟨ cong₂ ℚ.max (ℚ.+Comm q s) (ℚ.+Comm r s) ⟩
              ℚ.max (s ℚ.+ q) (s ℚ.+ r) ∎))
        ( a))
  where
  open NE₂[_,_,_]

  +maxNE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
  fun +maxNE₂ x y = a + max x y
  lNE +maxNE₂ y   = snd ([ a ]+ⁿ ∘NE maxⁿ[ y ])
  rNE +maxNE₂ x   = snd ([ a ]+ⁿ ∘NE [ x ]maxⁿ)

  max+NE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
  fun max+NE₂ x y = max (a + x) (a + y)
  lNE max+NE₂ y   = snd (maxⁿ[ a + y ] ∘NE [ a ]+ⁿ)
  rNE max+NE₂ x   = snd ([ a + x ]maxⁿ ∘NE [ a ]+ⁿ)

+MonoL≤ : {x y a : ℝ} → x ≤ y → a + x ≤ a + y
+MonoL≤ {x} {y} {a} x≤y = sym (+DistRMax a x y) ∙ cong (a +_) x≤y

+MonoR≤ : {x y a : ℝ} → x ≤ y → x + a ≤ y + a
+MonoR≤ {x} {y} {a} x≤y =
  subst2 _≤_ (+Comm a x) (+Comm a y) (+MonoL≤ {x} {y} {a} x≤y)

-Flip< : {x y : ℝ} → x < y → - y < - x
-Flip< {x} {y} x<y = {!!}

∼→≤+rat : {x y : ℝ} {ε : ℚ₊} → x ∼[ ε ] y → y ≤ x + rat ⟨ ε ⟩₊
∼→≤+rat {x} {y} {ε} x∼y = {!!}

<→∼→<+rat :
  {x y z : ℝ} {ε : ℚ₊} → x < y → x ∼[ ε ] z → z < y + rat ⟨ ε ⟩₊
<→∼→<+rat {x} {y} {z} {ε} x<y x∼z = {!!}

<→∼→-rat< :
  {x y z : ℝ} {ε : ℚ₊} → x < y → y ∼[ ε ] z → x - rat ⟨ ε ⟩₊ < z
<→∼→-rat< {x} {y} {z} {ε} x<y y∼z = {!!}

<→rat<∨<rat : {q r : ℚ} (x : ℝ) → q ℚ.< r → (rat q < x) ⊔′ (x < rat r)
<→rat<∨<rat {q} {r} x q<r = {!!}

isWeaklyLinear< : isWeaklyLinear _<_
isWeaklyLinear< x y z x<y = {!!}

ℝ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
fst ℝ<StrictOrder = ℝ
StrictOrderStr._<_ (snd ℝ<StrictOrder) = _<_
StrictOrderStr.isStrictOrder (snd ℝ<StrictOrder) = {!!}

<+rat : (x : ℝ) (ε : ℚ₊) → x < x + rat ⟨ ε ⟩₊
<+rat x ε = {!!}

<≃∃+rat≤ : {x y : ℝ} → (x < y) ≃ (∃[ ε ∈ ℚ₊ ] (x + rat ⟨ ε ⟩₊ ≤ y))
<≃∃+rat≤ {x} {y} = {!!}

+MonoL< : {x y a : ℝ} → x < y → a + x < a + y
+MonoL< {x} {y} {a} x<y = {!!}

+MonoR< : {x y a : ℝ} → x < y → x + a < y + a
+MonoR< {x} {y} {a} x<y = {!!}

+ReflectL< : {x y a : ℝ} → a + x < a + y → x < y
+ReflectL< {x} {y} {a} a+x<a+y = {!!}

posSum→pos∨pos : {x y : ℝ} → 0 < x + y → (0 < x) ⊔′ (0 < y)
posSum→pos∨pos {x} {y} 0<x+y = {!!}

-rat≤→≤ : {x y : ℝ} → ((ε : ℚ₊) → x - rat ⟨ ε ⟩₊ ≤ y) → x ≤ y
-rat≤→≤ {x} {y} hypothesis = {!!}

≤≃¬> : {x y : ℝ} → (x ≤ y) ≃ (¬ (y < x))
≤≃¬> {x} {y} = {!!}
