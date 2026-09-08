module HoTTReals.Data.Real.Order.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels using (isProp→)

open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Quoset

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals using
  ( ℚPremetricSpace)
open import Cubical.Relation.Premetric.Completion.Elim ℚPremetricSpace using
  ( Elimℭ-Prop)
open import Cubical.Relation.Premetric.Completion.Closeness
  ℓ-zero ℚPremetricSpace using (∼≃B)
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals using (ℚ!)

open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Relation.Premetric.Properties

open BinaryRelation
open PositiveRationals
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedAbGroupTheory ℚOrderedAbGroup using (absΔ<→<+)
open 1/2∈ℚ using (mean ; <→<mean ; <→mean<)
open PremetricTheory ℝPremetricSpace

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
    ( isSetℭ x $ min x y)
    ( λ x≤y →
      x
        ≡⟨ sym $ minAbsorbLMax x y ⟩
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
        ≡⟨ sym $ minAssoc x a b ⟩
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
    ≡⟨ sym $ maxAssoc a b x ⟩
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
isProp< x y = squash₁

≤≃rat≤ : {q r : ℚ} → (q ℚ.≤ r) ≃ (rat q ≤ rat r)
≤≃rat≤ {q} {r} =
  propBiimpl→Equiv
    ( ℚ.isProp≤ q r)
    ( isProp≤ (rat q) (rat r))
    ( cong rat ∘ ℚ.≤→max q r)
    ( λ ratq≤ratr →
      subst (q ℚ.≤_) (isInjectiveι (ℚ.max q r) r ratq≤ratr) (ℚ.≤max q r))

<≃rat< : {q r : ℚ} → (q ℚ.< r) ≃ (rat q < rat r)
<≃rat< {q} {r} =
  propBiimpl→Equiv
    ( ℚ.isProp< q r)
    ( isProp< (rat q) (rat r))
    ( λ q<r → ∣ (q , r) , isRefl≤ (rat q) , q<r , isRefl≤ (rat r) ∣₁)
    ( PT.rec
      ( ℚ.isProp< q r)
      ( λ ((s , t) , ratq≤rats , s<t , ratt≤ratr) →
        ℚ.isTrans≤< q s r
          ( invEq (≤≃rat≤ {q} {s}) ratq≤rats)
          ( ℚ.isTrans<≤ s t r s<t $ invEq (≤≃rat≤ {t} {r}) ratt≤ratr)))

<Weaken≤ : {x y : ℝ} → x < y → x ≤ y
<Weaken≤ {x} {y} =
  PT.rec
    ( isProp≤ x y)
    ( λ ((q , r) , x≤ratq , q<r , ratr≤y) →
      isTrans≤ x (rat r) y
        ( isTrans≤ x (rat q) (rat r)
          ( x≤ratq)
          ( equivFun (≤≃rat≤ {q} {r}) (ℚ.<Weaken≤ q r q<r)))
        ( ratr≤y))

isIrrefl< : isIrrefl _<_
isIrrefl< x =
  PT.rec
    ( isProp⊥)
    ( λ ((q , r) , x≤ratq , q<r , ratr≤x) →
      ℚ.≤→≯ r q
        ( invEq (≤≃rat≤ {r} {q}) (isTrans≤ (rat r) x (rat q) ratr≤x x≤ratq))
        ( q<r))

isTrans< : isTrans _<_
isTrans< x y z x<y =
  PT.rec
    ( isProp< x z)
    ( λ ((s , t) , y≤rats , s<t , ratt≤z) →
      ∣ (s , t) ,
        isTrans≤ x y (rat s) (<Weaken≤ {x} {y} x<y) y≤rats ,
        s<t ,
        ratt≤z ∣₁)

ℝ<Quoset : Quoset ℓ-zero ℓ-zero
fst ℝ<Quoset = ℝ
QuosetStr._<_ (snd ℝ<Quoset) = _<_
QuosetStr.isQuoset (snd ℝ<Quoset) =
  isquoset
    ( isSetℭ)
    ( isProp<)
    ( isIrrefl<)
    ( isTrans<)
    ( isIrrefl×isTrans→isAsym _<_ (isIrrefl< , isTrans<))

isTrans≤< : {x y z : ℝ} → x ≤ y → y < z → x < z
isTrans≤< {x} {y} {z} x≤y =
  PT.rec
    ( isProp< x z)
    ( λ ((q , r) , y≤ratq , q<r , ratr≤z) →
      ∣ (q , r) , isTrans≤ x y (rat q) x≤y y≤ratq , q<r , ratr≤z ∣₁)

isTrans<≤ : {x y z : ℝ} → x < y → y ≤ z → x < z
isTrans<≤ {x} {y} {z} x<y y≤z =
  PT.rec
    ( isProp< x z)
    ( λ ((q , r) , x≤ratq , q<r , ratr≤y) →
      ∣ (q , r) , x≤ratq , q<r , isTrans≤ (rat r) y z ratr≤y y≤z ∣₁)
    ( x<y)

0<1 : 0 < 1
0<1 = ∣ (0 , 1) , refl , ℚ.pos<pos tt , refl ∣₁

-- TODO: Define IsArchimedean for any ordered field when we have that
-- definition later, tie to Lorenzo's Archimedean rings
isArchimedean< : (x y : ℝ) → x < y → ∃[ q ∈ ℚ ] (x < rat q) × (rat q < y)
isArchimedean< x y =
  PT.map
    ( λ ((r , s) , x≤ratr , r<s , rats≤y) →
      mean r s ,
      ∣ (r , mean r s) ,
        x≤ratr ,
        <→<mean r s r<s ,
        isRefl≤ (rat $ mean r s) ∣₁ ,
      ∣ (mean r s , s) ,
        isRefl≤ (rat $ mean r s) ,
        <→mean< r s r<s ,
        rats≤y ∣₁)

rat∼→≤rat+ :
  {q : ℚ} {ε : ℚ₊} {w : ℝ} → rat q ∼[ ε ] w → w ≤ rat (q ℚ.+ ⟨ ε ⟩₊)
rat∼→≤rat+ {q} {ε} {w} = Elimℭ-Prop.go e w
  where
  limitCase :
    (y : ℚ₊ → ℝ) (yIsCauchy : isCauchy∼ y) →
    ((δ : ℚ₊) → rat q ∼[ ε ] y δ → y δ ≤ rat (q ℚ.+ ⟨ ε ⟩₊)) →
    Σ[ θ ∈ ℚ₊ ] (θ <₊ ε) × (rat q ∼[ θ ] lim y yIsCauchy) →
    lim y yIsCauchy ≤ rat (q ℚ.+ ⟨ ε ⟩₊)
  limitCase y yIsCauchy hypothesis (θ , θ<ε , ratq∼limy) =
    isLimit→isEventuallyConstantAt→≡
      ( ℝPremetricSpace)
      ( Δ)
      ( NE→presLim
          ( maxⁿ[ rat $ q ℚ.+ ⟨ ε ⟩₊ ])
          ( y)
          ( lim y yIsCauchy)
          ( isLimitLim y yIsCauchy))
      ( eventuallyConstant)
    where
    Δ : ℚ₊
    Δ = [ ε -₊ θ ]⟨ θ<ε ⟩

    recombineGap : ⟨ θ +₊ Δ ⟩₊ ≡ ⟨ ε ⟩₊
    recombineGap = ℚ!

    eventuallyConstant :
      IsEventuallyConstantAt
        ( ℝPremetricSpace)
        ( flip max (rat $ q ℚ.+ ⟨ ε ⟩₊) ∘ y)
        ( rat $ q ℚ.+ ⟨ ε ⟩₊)
        ( Δ)
    eventuallyConstant δ δ<Δ =
      hypothesis δ
        ( subst∼ (rat q) (y δ) recombineGap
          ( isTriangular∼ (rat q) (lim y yIsCauchy) (y δ) θ Δ
            ( ratq∼limy)
            ( isSym∼ (y δ) (lim y yIsCauchy) Δ
              ( isLimit≈<
                  ( y)
                  ( lim y yIsCauchy)
                  ( isLimitLim y yIsCauchy)
                  ( δ)
                  ( Δ)
                  ( δ<Δ)))))

  e : Elimℭ-Prop (λ w → rat q ∼[ ε ] w → w ≤ rat (q ℚ.+ ⟨ ε ⟩₊))
  Elimℭ-Prop.ιA e s ratq∼rats =
    equivFun
      ( ≤≃rat≤ {s} {q ℚ.+ ⟨ ε ⟩₊})
      ( ℚ.<Weaken≤ s (q ℚ.+ ⟨ ε ⟩₊)
        ( absΔ<→<+ {q} {s} {⟨ ε ⟩₊} $ equivFun ∼≃B ratq∼rats))
  Elimℭ-Prop.limA e y yIsCauchy hypothesis ratq∼limy =
    PT.rec
      ( isProp≤ (lim y yIsCauchy) (rat $ q ℚ.+ ⟨ ε ⟩₊))
      ( limitCase y yIsCauchy hypothesis)
      ( isRounded∼ (rat q) (lim y yIsCauchy) ε ratq∼limy)
  Elimℭ-Prop.isPropA e w = isProp→ $ isProp≤ w $ rat $ q ℚ.+ ⟨ ε ⟩₊

≤rat→∼→≤rat+ :
  {x y : ℝ} {q : ℚ} {ε : ℚ₊} →
  x ≤ rat q →
  x ∼[ ε ] y →
  y ≤ rat (q ℚ.+ ⟨ ε ⟩₊)
≤rat→∼→≤rat+ {x} {y} {q} {ε} x≤ratq x∼y =
  isTrans≤ y (max y $ rat q) (rat $ q ℚ.+ ⟨ ε ⟩₊)
    ( L≤max {y} {rat q})
    ( rat∼→≤rat+ {q} {ε} {max y $ rat q}
      ( subst≈L x≤ratq $ IsNonExpansive.pres≈ (snd maxⁿ[ rat q ]) x y ε x∼y))

<rat→∼→<rat+ :
  {x y : ℝ} {q : ℚ} {ε : ℚ₊} →
  x < rat q →
  x ∼[ ε ] y →
  y < rat (q ℚ.+ ⟨ ε ⟩₊)
<rat→∼→<rat+ {x} {y} {q} {ε} x<ratq x∼y =
  PT.rec
    ( isProp< y $ rat $ q ℚ.+ ⟨ ε ⟩₊)
    ( λ ((r , s) , x≤ratr , r<s , rats≤ratq) →
      ∣ (r ℚ.+ ⟨ ε ⟩₊ , s ℚ.+ ⟨ ε ⟩₊) ,
        ≤rat→∼→≤rat+ {x} {y} {r} {ε} x≤ratr x∼y ,
        ℚ.<-+o r s ⟨ ε ⟩₊ r<s ,
        equivFun
          ( ≤≃rat≤ {s ℚ.+ ⟨ ε ⟩₊} {q ℚ.+ ⟨ ε ⟩₊})
          ( ℚ.≤-+o s q ⟨ ε ⟩₊ $ invEq (≤≃rat≤ {s} {q}) rats≤ratq) ∣₁)
    ( x<ratq)
