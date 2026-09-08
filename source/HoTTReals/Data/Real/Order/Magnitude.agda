module HoTTReals.Data.Real.Order.Magnitude where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels using (isPropΠ3)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_ ; inl ; inr)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

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

import HoTTReals.Algebra.AbGroup.Properties as AbGroupProperties
open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Addition

open PositiveRationals
open PositiveHalvesℚ
open OrderedAbGroupTheory ℝOrderedAbGroup using
  ( abs ; 0≤abs ; abs≤≃ ; absΔabs≤ ; abs<→< ; abs<→-<)
open OrderedAbGroupTheory ℚOrderedAbGroup using () renaming (abs to absℚ)
open AbGroupProperties.AbGroupTheory ℝAbGroup using
  ( addSubCancelLeft ; addSubCancelRight ; negSub ; subAddCancel)
open PremetricTheory ℝPremetricSpace using (isLimit≈<)

abs∘rat : (q : ℚ) → abs (rat q) ≡ rat (absℚ q)
abs∘rat q = refl

∼→Δ≤rat : {x y : ℝ} {ε : ℚ₊} → x ∼[ ε ] y → y - x ≤ rat ⟨ ε ⟩₊
∼→Δ≤rat {x} {y} {ε} x∼y =
  subst
    ( (y - x) ≤_)
    ( addSubCancelLeft x (rat ⟨ ε ⟩₊))
    ( +MonoR≤ {y} {x + rat ⟨ ε ⟩₊} { - x} (∼→≤+rat {x} {y} {ε} x∼y))

-rat<→<rat→∼0 :
  {d : ℝ} {ε : ℚ₊} → - rat ⟨ ε ⟩₊ < d → d < rat ⟨ ε ⟩₊ → d ∼[ ε ] 0
-rat<→<rat→∼0 {d} {ε} = Elimℭ-Prop.go e d ε
  where
  rationalCase :
    (r : ℚ) (ε : ℚ₊) → - rat ⟨ ε ⟩₊ < rat r → rat r < rat ⟨ ε ⟩₊ →
    rat r ∼[ ε ] 0
  rationalCase r ε -ratε<ratr ratr<ratε =
    invEq ∼≃B (subst (ℚ._< ⟨ ε ⟩₊) (cong absℚ (sym dropZero)) absBelowRadius)
    where
    dropZero : r ℚ.- 0 ≡ r
    dropZero = ℚ!

    negNeg : ℚ.- (ℚ.- ⟨ ε ⟩₊) ≡ ⟨ ε ⟩₊
    negNeg = ℚ!

    negRadiusBelow : ℚ.- ⟨ ε ⟩₊ ℚ.< r
    negRadiusBelow = invEq (<≃rat< {ℚ.- ⟨ ε ⟩₊} {r}) -ratε<ratr

    belowRadius : r ℚ.< ⟨ ε ⟩₊
    belowRadius = invEq (<≃rat< {r} {⟨ ε ⟩₊}) ratr<ratε

    negBelowRadius : ℚ.- r ℚ.< ⟨ ε ⟩₊
    negBelowRadius =
      subst
        ( ℚ.- r ℚ.<_)
        ( negNeg)
        ( OrderedAbGroupTheory.-Flip< ℚOrderedAbGroup
            { ℚ.- ⟨ ε ⟩₊}
            { r}
            ( negRadiusBelow))

    joinBelow : (r ℚ.≤ ℚ.- r) ⊎ (ℚ.- r ℚ.≤ r) → absℚ r ℚ.< ⟨ ε ⟩₊
    joinBelow (inl r≤-r) =
      subst (ℚ._< ⟨ ε ⟩₊) (sym (ℚ.≤→max r (ℚ.- r) r≤-r)) negBelowRadius
    joinBelow (inr -r≤r) =
      subst
        ( ℚ._< ⟨ ε ⟩₊)
        ( sym (ℚ.maxComm r (ℚ.- r) ∙ ℚ.≤→max (ℚ.- r) r -r≤r))
        ( belowRadius)

    absBelowRadius : absℚ r ℚ.< ⟨ ε ⟩₊
    absBelowRadius =
      PT.rec (ℚ.isProp< (absℚ r) ⟨ ε ⟩₊) joinBelow (ℚ.isTotal≤ r (ℚ.- r))

  limitCase :
    (y : ℚ₊ → ℝ) (yIsCauchy : isCauchy∼ y) →
    ((δ ε' : ℚ₊) → - rat ⟨ ε' ⟩₊ < y δ → y δ < rat ⟨ ε' ⟩₊ → y δ ∼[ ε' ] 0) →
    (ε : ℚ₊) → - rat ⟨ ε ⟩₊ < lim y yIsCauchy → lim y yIsCauchy < rat ⟨ ε ⟩₊ →
    lim y yIsCauchy ∼[ ε ] 0
  limitCase y yIsCauchy hypothesis ε -ratε<limy limy<ratε =
    PT.rec2
      ( isProp∼ (lim y yIsCauchy) ε 0)
      ( bounded)
      ( equivFun (<≃∃+rat≤ {lim y yIsCauchy} {rat ⟨ ε ⟩₊}) limy<ratε)
      ( equivFun (<≃∃+rat≤ { - rat ⟨ ε ⟩₊} {lim y yIsCauchy}) -ratε<limy)
    where
    bounded :
      Σ[ η₁ ∈ ℚ₊ ] (lim y yIsCauchy + rat ⟨ η₁ ⟩₊ ≤ rat ⟨ ε ⟩₊) →
      Σ[ η₂ ∈ ℚ₊ ] ((- rat ⟨ ε ⟩₊) + rat ⟨ η₂ ⟩₊ ≤ lim y yIsCauchy) →
      lim y yIsCauchy ∼[ ε ] 0
    bounded (η₁ , limy+ratη₁≤ratε) (η₂ , -ratε+ratη₂≤limy) =
      subst∼ (lim y yIsCauchy) 0 (recombine η gapBelowRadius)
        ( isTriangular∼ (lim y yIsCauchy) (y (η /4₊)) 0 δ (θ +₊ δ)
          ( isSym∼ (y (η /4₊)) (lim y yIsCauchy) δ close)
          ( hypothesis
              ( η /4₊)
              ( θ +₊ δ)
              ( negOuterBelowApproximant)
              ( approximantBelowOuter)))
      where
      η : ℚ₊
      η = min₊ (min₊ η₁ η₂) ε /2₊

      gapBelowRadius : η <₊ ε
      gapBelowRadius = min/2₊<R (min₊ η₁ η₂) ε

      gapBelowUpperMargin : η <₊ η₁
      gapBelowUpperMargin =
        ℚ.isTrans<≤ ⟨ η ⟩₊ ⟨ min₊ η₁ η₂ ⟩₊ ⟨ η₁ ⟩₊
          ( min/2₊<L (min₊ η₁ η₂) ε)
          ( min₊≤L η₁ η₂)

      gapBelowLowerMargin : η <₊ η₂
      gapBelowLowerMargin =
        ℚ.isTrans<≤ ⟨ η ⟩₊ ⟨ min₊ η₁ η₂ ⟩₊ ⟨ η₂ ⟩₊
          ( min/2₊<L (min₊ η₁ η₂) ε)
          ( min₊≤R η₁ η₂)

      θ : ℚ₊
      θ = [ ε -₊ η ]⟨ gapBelowRadius ⟩

      δ : ℚ₊
      δ = η /2₊

      limitBelowShifted : lim y yIsCauchy ≤ rat (⟨ ε ⟩₊ ℚ.- ⟨ η₁ ⟩₊)
      limitBelowShifted =
        subst
          ( _≤ rat (⟨ ε ⟩₊ ℚ.- ⟨ η₁ ⟩₊))
          ( addSubCancelRight (lim y yIsCauchy) (rat ⟨ η₁ ⟩₊))
          ( +MonoR≤
              { lim y yIsCauchy + rat ⟨ η₁ ⟩₊}
              { rat ⟨ ε ⟩₊}
              { - rat ⟨ η₁ ⟩₊}
              ( limy+ratη₁≤ratε))

      shiftedBelowInner : ⟨ ε ⟩₊ ℚ.- ⟨ η₁ ⟩₊ ℚ.< ⟨ θ ⟩₊
      shiftedBelowInner =
        ℚ.<-o+ (ℚ.- ⟨ η₁ ⟩₊) (ℚ.- ⟨ η ⟩₊) ⟨ ε ⟩₊
          ( OrderedAbGroupTheory.-Flip< ℚOrderedAbGroup
              { ⟨ η ⟩₊}
              { ⟨ η₁ ⟩₊}
              ( gapBelowUpperMargin))

      limitBelowInner : lim y yIsCauchy < rat ⟨ θ ⟩₊
      limitBelowInner =
        isTrans≤< {lim y yIsCauchy} {rat (⟨ ε ⟩₊ ℚ.- ⟨ η₁ ⟩₊)} {rat ⟨ θ ⟩₊}
          ( limitBelowShifted)
          ( equivFun (<≃rat< {⟨ ε ⟩₊ ℚ.- ⟨ η₁ ⟩₊} {⟨ θ ⟩₊}) shiftedBelowInner)

      negateGap : (a b : ℚ) → ℚ.- (a ℚ.- b) ≡ (ℚ.- a) ℚ.+ b
      negateGap a b = ℚ!

      negInnerBelowShifted : ℚ.- ⟨ θ ⟩₊ ℚ.< (ℚ.- ⟨ ε ⟩₊) ℚ.+ ⟨ η₂ ⟩₊
      negInnerBelowShifted =
        subst
          ( ℚ._< (ℚ.- ⟨ ε ⟩₊) ℚ.+ ⟨ η₂ ⟩₊)
          ( sym (negateGap ⟨ ε ⟩₊ ⟨ η ⟩₊))
          ( ℚ.<-o+ ⟨ η ⟩₊ ⟨ η₂ ⟩₊ (ℚ.- ⟨ ε ⟩₊) gapBelowLowerMargin)

      negInnerBelowLimit : - rat ⟨ θ ⟩₊ < lim y yIsCauchy
      negInnerBelowLimit =
        isTrans<≤
          { - rat ⟨ θ ⟩₊}
          { rat ((ℚ.- ⟨ ε ⟩₊) ℚ.+ ⟨ η₂ ⟩₊)}
          { lim y yIsCauchy}
          ( equivFun
              ( <≃rat< {ℚ.- ⟨ θ ⟩₊} {(ℚ.- ⟨ ε ⟩₊) ℚ.+ ⟨ η₂ ⟩₊})
              ( negInnerBelowShifted))
          ( -ratε+ratη₂≤limy)

      close : y (η /4₊) ∼[ δ ] lim y yIsCauchy
      close =
        isLimit≈< y (lim y yIsCauchy) (isLimitLim y yIsCauchy) (η /4₊) δ
          ( /4₊</2₊ η)

      approximantBelowOuter : y (η /4₊) < rat ⟨ θ +₊ δ ⟩₊
      approximantBelowOuter =
        <rat→∼→<rat+ {lim y yIsCauchy} {y (η /4₊)} {⟨ θ ⟩₊} {δ}
          ( limitBelowInner)
          ( isSym∼ (y (η /4₊)) (lim y yIsCauchy) δ close)

      negateSum : (a b : ℚ) → (ℚ.- a) ℚ.+ (ℚ.- b) ≡ ℚ.- (a ℚ.+ b)
      negateSum a b = ℚ!

      negOuterBelowApproximant : - rat ⟨ θ +₊ δ ⟩₊ < y (η /4₊)
      negOuterBelowApproximant =
        subst
          ( _< y (η /4₊))
          ( cong rat (negateSum ⟨ θ ⟩₊ ⟨ δ ⟩₊))
          ( <→∼→-rat< { - rat ⟨ θ ⟩₊} {lim y yIsCauchy} {y (η /4₊)} {δ}
            ( negInnerBelowLimit)
            ( isSym∼ (y (η /4₊)) (lim y yIsCauchy) δ close))

      recombine :
        (gap : ℚ₊) (gap<ε : gap <₊ ε) →
        ⟨ gap /2₊ +₊ ([ ε -₊ gap ]⟨ gap<ε ⟩ +₊ gap /2₊) ⟩₊ ≡ ⟨ ε ⟩₊
      recombine gap gap<ε = ℚ!

  e :
    Elimℭ-Prop
      ( λ d → (ε : ℚ₊) → - rat ⟨ ε ⟩₊ < d → d < rat ⟨ ε ⟩₊ → d ∼[ ε ] 0)
  Elimℭ-Prop.ιA e = rationalCase
  Elimℭ-Prop.limA e = limitCase
  Elimℭ-Prop.isPropA e d = isPropΠ3 (λ ε _ _ → isProp∼ d ε 0)

∼≃abs< : {x y : ℝ} {ε : ℚ₊} → (x ∼[ ε ] y) ≃ (abs (x - y) < rat ⟨ ε ⟩₊)
∼≃abs< {x} {y} {ε} =
  propBiimpl→Equiv
    ( isProp∼ x ε y)
    ( isProp< (abs (x - y)) (rat ⟨ ε ⟩₊))
    ( λ x∼y →
      PT.rec
        ( isProp< (abs (x - y)) (rat ⟨ ε ⟩₊))
        ( forward)
        ( isRounded∼ x y ε x∼y))
    ( backward)
  where
  forward :
    Σ[ θ ∈ ℚ₊ ] (θ <₊ ε) × (x ∼[ θ ] y) → abs (x - y) < rat ⟨ ε ⟩₊
  forward (θ , θ<ε , x∼y) =
    isTrans≤< {abs (x - y)} {rat ⟨ θ ⟩₊} {rat ⟨ ε ⟩₊}
      ( invEq
        ( abs≤≃ {x - y} {rat ⟨ θ ⟩₊})
        ( ∼→Δ≤rat {y} {x} {θ} (isSym∼ x y θ x∼y) ,
          subst (_≤ rat ⟨ θ ⟩₊) (sym (negSub x y))
            ( ∼→Δ≤rat {x} {y} {θ} x∼y)))
      ( equivFun (<≃rat< {⟨ θ ⟩₊} {⟨ ε ⟩₊}) θ<ε)

  backward : abs (x - y) < rat ⟨ ε ⟩₊ → x ∼[ ε ] y
  backward ∣x-y∣<ratε =
    subst2 (_∼[ ε ]_) (subAddCancel x y) (+IdL y)
      ( IsNonExpansive.pres≈ (snd +ⁿ[ y ]) (x - y) 0 ε
        ( -rat<→<rat→∼0 {x - y} {ε}
          ( abs<→-< {x - y} {rat ⟨ ε ⟩₊} ∣x-y∣<ratε)
          ( abs<→< {x - y} {rat ⟨ ε ⟩₊} ∣x-y∣<ratε)))

absⁿ : NE[ ℝPremetricSpace , ℝPremetricSpace ]
fst absⁿ = abs
IsNonExpansive.pres≈ (snd absⁿ) x y ε x∼y =
  invEq
    ( ∼≃abs< {abs x} {abs y} {ε})
    ( isTrans≤< {abs (abs x - abs y)} {abs (x - y)} {rat ⟨ ε ⟩₊}
      ( absΔabs≤ x y)
      ( equivFun (∼≃abs< {x} {y} {ε}) x∼y))

∃abs<rat : (x : ℝ) → ∃[ q ∈ ℚ₊ ] (abs x < rat ⟨ q ⟩₊)
∃abs<rat x =
  PT.map
    ( λ (q , ∣x∣<ratq , ratq<∣x∣+1) →
      ( q ,
        invEq
          ( <≃rat< {0} {q})
          ( isTrans≤< {0} {abs x} {rat q} (0≤abs x) ∣x∣<ratq)) ,
      ∣x∣<ratq)
    ( isArchimedean< (abs x) (abs x + rat 1) (<+rat (abs x) 1))
