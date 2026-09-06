module HoTTReals.Data.Real.Order.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.HITs.PropositionalTruncation using (squash₁)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Quoset

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Data.Real.Algebra.Lattice

open BinaryRelation
open PositiveRationals

_≤_ : ℝ → ℝ → Type ℓ-zero
x ≤ y = max x y ≡ y

infix 4 _≤_

isProp≤ : isPropValued _≤_
isProp≤ x y = isSetℭ (max x y) y

isRefl≤ : isRefl _≤_
isRefl≤ = maxIdem

isAntisym≤ : isAntisym _≤_
isAntisym≤ x y x≤y y≤x =
  x
    ≡⟨ sym y≤x ⟩
  max y x
    ≡⟨ maxComm y x ⟩
  max x y
    ≡⟨ x≤y ⟩
  y ∎

isTrans≤ : isTrans _≤_
isTrans≤ x y z x≤y y≤z =
  max x z
    ≡⟨ cong (max x) (sym y≤z) ⟩
  max x (max y z)
    ≡⟨ maxAssoc x y z ⟩
  max (max x y) z
    ≡⟨ cong (flip max z) x≤y ⟩
  max y z
    ≡⟨ y≤z ⟩
  z ∎

ℝ≤Poset : Poset ℓ-zero ℓ-zero
fst ℝ≤Poset = ℝ
PosetStr._≤_ (snd ℝ≤Poset) = _≤_
PosetStr.isPoset (snd ℝ≤Poset) =
  isposet isSetℭ isProp≤ isRefl≤ isTrans≤ isAntisym≤

≤≃min : {x y : ℝ} → (x ≤ y) ≃ (x ≡ min x y)
≤≃min {x} {y} =
  propBiimpl→Equiv
    ( isProp≤ x y)
    ( isSetℭ x (min x y))
    ( λ x≤y →
      x
        ≡⟨ sym (minAbsorbLMax x y) ⟩
      min x (max x y)
        ≡⟨ cong (min x) x≤y ⟩
      min x y ∎)
    ( λ x≡min →
      max x y
        ≡⟨ cong (flip max y) x≡min ⟩
      max (min x y) y
        ≡⟨ cong (flip max y) (minComm x y) ⟩
      max (min y x) y
        ≡⟨ maxAbsorbRMin y x ⟩
      y ∎)

min≤L : {x y : ℝ} → min x y ≤ x
min≤L {x} {y} = maxAbsorbRMin x y

min≤R : {x y : ℝ} → min x y ≤ y
min≤R {x} {y} = cong (flip max y) (minComm x y) ∙ min≤L

minGLB : {x a b : ℝ} → x ≤ a → x ≤ b → x ≤ min a b
minGLB {x} {a} {b} x≤a x≤b =
  invEq
    ( ≤≃min {x} {min a b})
    ( x
        ≡⟨ equivFun (≤≃min {x} {b}) x≤b ⟩
      min x b
        ≡⟨ cong (flip min b) (equivFun (≤≃min {x} {a}) x≤a) ⟩
      min (min x a) b
        ≡⟨ sym (minAssoc x a b) ⟩
      min x (min a b) ∎)

L≤max : {x y : ℝ} → x ≤ max x y
L≤max {x} {y} = maxAssoc x x y ∙ cong (flip max y) (maxIdem x)

R≤max : {x y : ℝ} → y ≤ max x y
R≤max {x} {y} =
  max y (max x y)
    ≡⟨ cong (max y) (maxComm x y) ⟩
  max y (max y x)
    ≡⟨ L≤max {y} {x} ⟩
  max y x
    ≡⟨ maxComm y x ⟩
  max x y ∎

maxLUB : {x a b : ℝ} → a ≤ x → b ≤ x → max a b ≤ x
maxLUB {x} {a} {b} a≤x b≤x =
  max (max a b) x
    ≡⟨ sym (maxAssoc a b x) ⟩
  max a (max b x)
    ≡⟨ cong (max a) b≤x ⟩
  max a x
    ≡⟨ a≤x ⟩
  x ∎

ℝ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℝ≤Pseudolattice =
  makePseudolatticeFromPoset
    ( ℝ≤Poset)
    ( min)
    ( max)
    ( λ {x} {y} → min≤L {x} {y})
    ( λ {x} {y} → min≤R {x} {y})
    ( λ {a} {b} {x} → minGLB {x} {a} {b})
    ( λ {x} {y} → L≤max {x} {y})
    ( λ {x} {y} → R≤max {x} {y})
    ( λ {a} {b} {x} → maxLUB {x} {a} {b})

_<_ : ℝ → ℝ → Type ℓ-zero
x < y = ∃[ (q , r) ∈ ℚ × ℚ ] (x ≤ rat q) × (q ℚ.< r) × (rat r ≤ y)

infix 4 _<_

isProp< : isPropValued _<_
isProp< = {!!}

≤≃rat≤ : {q r : ℚ} → (q ℚ.≤ r) ≃ (rat q ≤ rat r)
≤≃rat≤ = {!!}

<≃rat< : {q r : ℚ} → (q ℚ.< r) ≃ (rat q < rat r)
<≃rat< = {!!}

<Weaken≤ : {x y : ℝ} → x < y → x ≤ y
<Weaken≤ = {!!}

isIrrefl< : isIrrefl _<_
isIrrefl< = {!!}

isTrans< : isTrans _<_
isTrans< = {!!}

ℝ<Quoset : Quoset ℓ-zero ℓ-zero
fst ℝ<Quoset = ℝ
QuosetStr._<_ (snd ℝ<Quoset) = _<_
QuosetStr.isQuoset (snd ℝ<Quoset) = {!!}

isTrans≤< : {x y z : ℝ} → x ≤ y → y < z → x < z
isTrans≤< = {!!}

isTrans<≤ : {x y z : ℝ} → x < y → y ≤ z → x < z
isTrans<≤ = {!!}

0<1 : 0 < 1
0<1 = {!!}

-- TODO: Define IsArchimedean for any ordered field when we have that definition later, tie to Lorenzo's Archimedean rings
isArchimedean< : (x y : ℝ) → x < y → ∃[ q ∈ ℚ ] (x < rat q) × (rat q < y)
isArchimedean< = {!!}

rat∼→≤rat+ :
  {q : ℚ} {ε : ℚ₊} {w : ℝ} → rat q ∼[ ε ] w → w ≤ rat (q ℚ.+ ⟨ ε ⟩₊)
rat∼→≤rat+ = {!!}

≤rat→∼→≤rat+ :
  {x y : ℝ} {q : ℚ} {ε : ℚ₊} →
  x ≤ rat q →
  x ∼[ ε ] y →
  y ≤ rat (q ℚ.+ ⟨ ε ⟩₊)
≤rat→∼→≤rat+ = {!!}

<rat→∼→<rat+ :
  {x y : ℝ} {q : ℚ} {ε : ℚ₊} →
  x < rat q →
  x ∼[ ε ] y →
  y < rat (q ℚ.+ ⟨ ε ⟩₊)
<rat→∼→<rat+ = {!!}
