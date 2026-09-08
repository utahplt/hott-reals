module HoTTReals.Data.Real.Order.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels using (isPropΠ ; isPropΠ3)

open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using ()
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.Functions.Logic using (_⊔′_)

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Relation.Nullary using (¬_ ; isProp¬)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals using
  ( ℚPremetricSpace)
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Lift
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
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Relation.Premetric.Instances.Product
open import HoTTReals.Relation.Premetric.Mappings

open BinaryRelation
open PositiveRationals
open PositiveHalvesℚ
open OrderedCommRingTheory ℚOrderedCommRing using (<→0<Δ ; 0<Δ→<)
open OrderedAbGroupTheory ℚOrderedAbGroup using (-⊓ ; +DistL⊔ ; 0≤→abs≡id)
  renaming (abs to absℚ)
open AbGroupProperties.AbGroupTheory ℝAbGroup using
  ( negAdd ; negAddCancelLeft ; subAddCancel)
open GroupTheory (AbGroup→Group ℝAbGroup) using (invInv)
open PremetricTheory ℝPremetricSpace using (isLimit≈<)

-DistMin : (x y : ℝ) → - min x y ≡ max (- x) (- y)
-DistMin =
  nonExpansive₂≡
    ( _)
    ( _)
    ( _)
    ( NE₂[_,_,_].makeNE₂ -minNE₂)
    ( NE₂[_,_,_].makeNE₂ max-NE₂)
    ( λ q r → cong rat (-⊓ q r))
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
                ≡⟨ +DistL⊔ q r s ⟩
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
-Flip< {x} {y} x<y =
  PT.rec
    ( isProp< (- y) (- x))
    ( λ ((q , r) , x≤ratq , q<r , ratr≤y) →
      ∣ (ℚ.- r , ℚ.- q) ,
        -Flip≤ {rat r} {y} ratr≤y ,
        OrderedCommRingTheory.-Flip< ℚOrderedCommRing q r q<r ,
        -Flip≤ {x} {rat q} x≤ratq ∣₁)
    ( x<y)

∼→≤+rat : {x y : ℝ} {ε : ℚ₊} → x ∼[ ε ] y → y ≤ x + rat ⟨ ε ⟩₊
∼→≤+rat {x} {y} {ε} x∼y =
  subst2 _≤_ (subAddCancel y x) commuteTranslation
    ( +MonoR≤ {y - x} {rat (0 ℚ.+ ⟨ ε ⟩₊)} {x}
      ( rat∼→≤rat+ {0} {ε} {y - x}
        ( subst
          ( _∼[ ε ] (y - x))
          ( +InvR x)
          ( IsNonExpansive.pres≈ (snd +ⁿ[ - x ]) x y ε x∼y))))
  where
  commuteTranslation : rat (0 ℚ.+ ⟨ ε ⟩₊) + x ≡ x + rat ⟨ ε ⟩₊
  commuteTranslation =
    +Comm (rat (0 ℚ.+ ⟨ ε ⟩₊)) x ∙ cong (λ q → x + rat q) (ℚ.+IdL ⟨ ε ⟩₊)

<→∼→<+rat :
  {x y z : ℝ} {ε : ℚ₊} → x < y → x ∼[ ε ] z → z < y + rat ⟨ ε ⟩₊
<→∼→<+rat {x} {y} {z} {ε} x<y x∼z =
  PT.rec
    ( isProp< z (y + rat ⟨ ε ⟩₊))
    ( λ (q , x<ratq , ratq<y) →
      isTrans<≤ {z} {rat q + rat ⟨ ε ⟩₊} {y + rat ⟨ ε ⟩₊}
        ( <rat→∼→<rat+ {x} {z} {q} {ε} x<ratq x∼z)
        ( +MonoR≤ {rat q} {y} {rat ⟨ ε ⟩₊} (<Weaken≤ {rat q} {y} ratq<y)))
    ( isArchimedean< x y x<y)

<→∼→-rat< :
  {x y z : ℝ} {ε : ℚ₊} → x < y → y ∼[ ε ] z → x - rat ⟨ ε ⟩₊ < z
<→∼→-rat< {x} {y} {z} {ε} x<y y∼z =
  subst2 _<_ negateTranslation (invInv z)
    ( -Flip< { - z} {(- x) + rat ⟨ ε ⟩₊}
      ( <→∼→<+rat { - y} { - x} { - z} {ε}
        ( -Flip< {x} {y} x<y)
        ( IsNonExpansive.pres≈ (snd -ⁿ) y z ε y∼z)))
  where
  negateTranslation : - ((- x) + rat ⟨ ε ⟩₊) ≡ x - rat ⟨ ε ⟩₊
  negateTranslation =
    negAdd (- x) (rat ⟨ ε ⟩₊) ∙
      cong (_+ (- rat ⟨ ε ⟩₊)) (invInv x)

<→rat<∨<rat : {q r : ℚ} (x : ℝ) → q ℚ.< r → (rat q < x) ⊔′ (x < rat r)
<→rat<∨<rat {q} {r} x q<r = Elimℭ-Prop.go e x q r q<r
  where
  limitCase :
    (y : ℚ₊ → ℝ) (yIsCauchy : isCauchy∼ y) →
    ((δ : ℚ₊) (s t : ℚ) → s ℚ.< t → (rat s < y δ) ⊔′ (y δ < rat t)) →
    (q r : ℚ) → q ℚ.< r →
    (rat q < lim y yIsCauchy) ⊔′ (lim y yIsCauchy < rat r)
  limitCase y yIsCauchy hypothesis q r q<r =
    PT.map (⊎.map leftCase rightCase) (hypothesis δ s t s<t)
    where
    η : ℚ₊
    η = [ 1 / 3 ]₊ ·₊ (r ℚ.- q , <→0<Δ q r q<r)

    s : ℚ
    s = q ℚ.+ ⟨ η ⟩₊

    t : ℚ
    t = r ℚ.- ⟨ η ⟩₊

    gap : t ℚ.- s ≡ ⟨ η ⟩₊
    gap = ℚ!

    s<t : s ℚ.< t
    s<t = 0<Δ→< s t (subst (0 ℚ.<_) (sym gap) (snd η))

    δ : ℚ₊
    δ = η /2₊

    close : y δ ∼[ η ] lim y yIsCauchy
    close =
      isLimit≈< y (lim y yIsCauchy) (isLimitLim y yIsCauchy) δ η (/2₊<id η)

    shiftDown : s ℚ.- ⟨ η ⟩₊ ≡ q
    shiftDown = ℚ!

    shiftUp : t ℚ.+ ⟨ η ⟩₊ ≡ r
    shiftUp = ℚ!

    leftCase : rat s < y δ → rat q < lim y yIsCauchy
    leftCase rats<yδ =
      subst
        ( _< lim y yIsCauchy)
        ( cong rat shiftDown)
        ( <→∼→-rat< {rat s} {y δ} {lim y yIsCauchy} {η} rats<yδ close)

    rightCase : y δ < rat t → lim y yIsCauchy < rat r
    rightCase yδ<ratt =
      subst
        ( lim y yIsCauchy <_)
        ( cong rat shiftUp)
        ( <→∼→<+rat {y δ} {rat t} {lim y yIsCauchy} {η} yδ<ratt close)

  e : Elimℭ-Prop (λ x → (q r : ℚ) → q ℚ.< r → (rat q < x) ⊔′ (x < rat r))
  Elimℭ-Prop.ιA e s q r q<r =
    PT.map
      ( ⊎.map (equivFun (<≃rat< {q} {s})) (equivFun (<≃rat< {s} {r})))
      ( ℚ.isWeaklyLinear< q r s q<r)
  Elimℭ-Prop.limA e = limitCase
  Elimℭ-Prop.isPropA e x = isPropΠ3 (λ q r q<r → squash₁)

isWeaklyLinear< : isWeaklyLinear _<_
isWeaklyLinear< x y z x<y =
  PT.rec
    ( squash₁)
    ( λ ((q , r) , x≤ratq , q<r , ratr≤y) →
      PT.map
        ( ⊎.map
          ( isTrans≤< {x} {rat q} {z} x≤ratq)
          ( λ z<ratr → isTrans<≤ {z} {rat r} {y} z<ratr ratr≤y))
        ( <→rat<∨<rat {q} {r} z q<r))
    ( x<y)

ℝ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
fst ℝ<StrictOrder = ℝ
StrictOrderStr._<_ (snd ℝ<StrictOrder) = _<_
StrictOrderStr.isStrictOrder (snd ℝ<StrictOrder) =
  isstrictorder
    ( isSetℭ)
    ( isProp<)
    ( isIrrefl<)
    ( isTrans<)
    ( isIrrefl×isTrans→isAsym _<_ (isIrrefl< , isTrans<))
    ( isWeaklyLinear<)

<+rat : (x : ℝ) (ε : ℚ₊) → x < x + rat ⟨ ε ⟩₊
<+rat x ε = Elimℭ-Prop.go e x ε
  where
  limitCase :
    (y : ℚ₊ → ℝ) (yIsCauchy : isCauchy∼ y) →
    ((η θ : ℚ₊) → y η < y η + rat ⟨ θ ⟩₊) →
    (ε : ℚ₊) → lim y yIsCauchy < lim y yIsCauchy + rat ⟨ ε ⟩₊
  limitCase y yIsCauchy hypothesis ε =
    PT.rec
      ( isProp< (lim y yIsCauchy) (lim y yIsCauchy + rat ⟨ ε ⟩₊))
      ( ⊎.rec
        ( idfun (lim y yIsCauchy < lim y yIsCauchy + rat ⟨ ε ⟩₊))
        ( ⊥.rec ∘ contradiction))
      ( isWeaklyLinear<
          ( lim y yIsCauchy)
          ( y δ + rat (3 ℚ.· ⟨ δ ⟩₊))
          ( lim y yIsCauchy + rat ⟨ ε ⟩₊)
          ( limitBelow))
    where
    δ : ℚ₊
    δ = [ 1 / 5 ]₊ ·₊ ε

    close : y δ ∼[ δ +₊ δ ] lim y yIsCauchy
    close =
      isLimit≈< y (lim y yIsCauchy) (isLimitLim y yIsCauchy) δ (δ +₊ δ)
        ( <₊SumLeft δ δ)

    sumThree : ⟨ δ ⟩₊ ℚ.+ ⟨ δ +₊ δ ⟩₊ ≡ 3 ℚ.· ⟨ δ ⟩₊
    sumThree = ℚ!

    collectPerturbations :
      (y δ + rat ⟨ δ ⟩₊) + rat ⟨ δ +₊ δ ⟩₊ ≡ y δ + rat (3 ℚ.· ⟨ δ ⟩₊)
    collectPerturbations =
      (y δ + rat ⟨ δ ⟩₊) + rat ⟨ δ +₊ δ ⟩₊
        ≡⟨ sym (+Assoc (y δ) (rat ⟨ δ ⟩₊) (rat ⟨ δ +₊ δ ⟩₊)) ⟩
      y δ + rat (⟨ δ ⟩₊ ℚ.+ ⟨ δ +₊ δ ⟩₊)
        ≡⟨ cong (λ p → y δ + rat p) sumThree ⟩
      y δ + rat (3 ℚ.· ⟨ δ ⟩₊) ∎

    limitBelow : lim y yIsCauchy < y δ + rat (3 ℚ.· ⟨ δ ⟩₊)
    limitBelow =
      subst
        ( lim y yIsCauchy <_)
        ( collectPerturbations)
        ( <→∼→<+rat {y δ} {y δ + rat ⟨ δ ⟩₊} {lim y yIsCauchy} {δ +₊ δ}
          ( hypothesis δ δ)
          ( close))

    sumFive : ⟨ δ +₊ δ ⟩₊ ℚ.+ 3 ℚ.· ⟨ δ ⟩₊ ≡ ⟨ ε ⟩₊
    sumFive = ℚ!

    recombinePerturbations :
      (lim y yIsCauchy + rat ⟨ δ +₊ δ ⟩₊) + rat (3 ℚ.· ⟨ δ ⟩₊) ≡
      lim y yIsCauchy + rat ⟨ ε ⟩₊
    recombinePerturbations =
      (lim y yIsCauchy + rat ⟨ δ +₊ δ ⟩₊) + rat (3 ℚ.· ⟨ δ ⟩₊)
        ≡⟨ sym $
          +Assoc (lim y yIsCauchy) (rat ⟨ δ +₊ δ ⟩₊) (rat (3 ℚ.· ⟨ δ ⟩₊)) ⟩
      lim y yIsCauchy + rat (⟨ δ +₊ δ ⟩₊ ℚ.+ 3 ℚ.· ⟨ δ ⟩₊)
        ≡⟨ cong (λ p → lim y yIsCauchy + rat p) sumFive ⟩
      lim y yIsCauchy + rat ⟨ ε ⟩₊ ∎

    approximantBelow : y δ + rat (3 ℚ.· ⟨ δ ⟩₊) ≤ lim y yIsCauchy + rat ⟨ ε ⟩₊
    approximantBelow =
      subst
        ( y δ + rat (3 ℚ.· ⟨ δ ⟩₊) ≤_)
        ( recombinePerturbations)
        ( +MonoR≤ {y δ} {lim y yIsCauchy + rat ⟨ δ +₊ δ ⟩₊} {rat (3 ℚ.· ⟨ δ ⟩₊)}
          ( ∼→≤+rat {lim y yIsCauchy} {y δ} {δ +₊ δ}
            ( isSym∼ (y δ) (lim y yIsCauchy) (δ +₊ δ) close)))

    contradiction :
      ¬ (lim y yIsCauchy + rat ⟨ ε ⟩₊ < y δ + rat (3 ℚ.· ⟨ δ ⟩₊))
    contradiction lim+ratε<yδ+rat3δ =
      isIrrefl< (y δ + rat (3 ℚ.· ⟨ δ ⟩₊))
        ( isTrans≤<
            { y δ + rat (3 ℚ.· ⟨ δ ⟩₊)}
            { lim y yIsCauchy + rat ⟨ ε ⟩₊}
            { y δ + rat (3 ℚ.· ⟨ δ ⟩₊)}
            ( approximantBelow)
            ( lim+ratε<yδ+rat3δ))

  e : Elimℭ-Prop (λ x → (ε : ℚ₊) → x < x + rat ⟨ ε ⟩₊)
  Elimℭ-Prop.ιA e q ε =
    equivFun
      ( <≃rat< {q} {q ℚ.+ ⟨ ε ⟩₊})
      ( subst (ℚ._< q ℚ.+ ⟨ ε ⟩₊) (ℚ.+IdR q) (ℚ.<-o+ 0 ⟨ ε ⟩₊ q (snd ε)))
  Elimℭ-Prop.limA e = limitCase
  Elimℭ-Prop.isPropA e x = isPropΠ (λ ε → isProp< x (x + rat ⟨ ε ⟩₊))

<≃∃+rat≤ : {x y : ℝ} → (x < y) ≃ (∃[ ε ∈ ℚ₊ ] (x + rat ⟨ ε ⟩₊ ≤ y))
<≃∃+rat≤ {x} {y} =
  propBiimpl→Equiv
    ( isProp< x y)
    ( squash₁)
    ( PT.map
      ( λ ((q , r) , x≤ratq , q<r , ratr≤y) →
        (r ℚ.- q , <→0<Δ q r q<r) ,
        isTrans≤ (x + rat (r ℚ.- q)) (rat r) y
          ( subst
            ( x + rat (r ℚ.- q) ≤_)
            ( cong rat (closeGap q r))
            ( +MonoR≤ {x} {rat q} {rat (r ℚ.- q)} x≤ratq))
          ( ratr≤y)))
    ( PT.rec
      ( isProp< x y)
      ( λ (ε , x+ratε≤y) →
        isTrans<≤ {x} {x + rat ⟨ ε ⟩₊} {y} (<+rat x ε) x+ratε≤y))
  where
  closeGap : (q r : ℚ) → q ℚ.+ (r ℚ.- q) ≡ r
  closeGap q r = ℚ!

+MonoL< : {x y a : ℝ} → x < y → a + x < a + y
+MonoL< {x} {y} {a} x<y =
  PT.rec
    ( isProp< (a + x) (a + y))
    ( λ (ε , x+ratε≤y) →
      invEq
        ( <≃∃+rat≤ {a + x} {a + y})
        ( ∣ ε ,
            subst
              ( _≤ a + y)
              ( +Assoc a x (rat ⟨ ε ⟩₊))
              ( +MonoL≤ {x + rat ⟨ ε ⟩₊} {y} {a} x+ratε≤y) ∣₁))
    ( equivFun (<≃∃+rat≤ {x} {y}) x<y)

+MonoR< : {x y a : ℝ} → x < y → x + a < y + a
+MonoR< {x} {y} {a} x<y =
  subst2 _<_ (+Comm a x) (+Comm a y) (+MonoL< {x} {y} {a} x<y)

+ReflectL< : {x y a : ℝ} → a + x < a + y → x < y
+ReflectL< {x} {y} {a} a+x<a+y =
  subst2 _<_
    ( negAddCancelLeft a x)
    ( negAddCancelLeft a y)
    ( +MonoL< {a + x} {a + y} { - a} a+x<a+y)

posSum→pos∨pos : {x y : ℝ} → 0 < x + y → (0 < x) ⊔′ (0 < y)
posSum→pos∨pos {x} {y} 0<x+y =
  PT.map
    ( ⊎.map
      ( idfun (0 < x))
      ( λ x<x+y →
        +ReflectL< {0} {y} {x} (subst (_< x + y) (sym (+IdR x)) x<x+y)))
    ( isWeaklyLinear< 0 (x + y) x 0<x+y)

-rat≤→≤ : {x y : ℝ} → ((ε : ℚ₊) → x - rat ⟨ ε ⟩₊ ≤ y) → x ≤ y
-rat≤→≤ {x} {y} hypothesis = eqℝ (max x y) y close
  where
  close : (ε : ℚ₊) → max x y ∼[ ε ] y
  close ε =
    subst
      ( max x y ∼[ ε ]_)
      ( hypothesis η)
      ( IsNonExpansive.pres≈ (snd maxⁿ[ y ]) x (x - rat ⟨ η ⟩₊) ε shift)
    where
    η : ℚ₊
    η = ε /2₊

    dropZero : 0 ℚ.- (ℚ.- ⟨ η ⟩₊) ≡ ⟨ η ⟩₊
    dropZero = ℚ!

    radius : absℚ (0 ℚ.- (ℚ.- ⟨ η ⟩₊)) ≡ ⟨ η ⟩₊
    radius =
      cong absℚ dropZero ∙ 0≤→abs≡id (ℚ.<Weaken≤ 0 ⟨ η ⟩₊ (snd η))

    ballBelow : absℚ (0 ℚ.- (ℚ.- ⟨ η ⟩₊)) ℚ.< ⟨ ε ⟩₊
    ballBelow = subst (ℚ._< ⟨ ε ⟩₊) (sym radius) (/2₊<id ε)

    shift : x ∼[ ε ] (x - rat ⟨ η ⟩₊)
    shift =
      subst
        ( _∼[ ε ] (x - rat ⟨ η ⟩₊))
        ( +IdR x)
        ( IsNonExpansive.pres≈ (snd [ x ]+ⁿ) (rat 0) (rat (ℚ.- ⟨ η ⟩₊)) ε
          ( invEq ∼≃B ballBelow))

≤≃¬> : {x y : ℝ} → (x ≤ y) ≃ (¬ (y < x))
≤≃¬> {x} {y} =
  propBiimpl→Equiv
    ( isProp≤ x y)
    ( isProp¬ (y < x))
    ( λ x≤y y<x → isIrrefl< y (isTrans<≤ {y} {x} {y} y<x x≤y))
    ( λ ¬y<x →
      -rat≤→≤ {x} {y}
        ( λ ε →
          <Weaken≤ {x - rat ⟨ ε ⟩₊} {y}
            ( PT.rec
              ( isProp< (x - rat ⟨ ε ⟩₊) y)
              ( ⊎.rec (idfun (x - rat ⟨ ε ⟩₊ < y)) (⊥.rec ∘ ¬y<x))
              ( isWeaklyLinear< (x - rat ⟨ ε ⟩₊) x y (below ε)))))
  where
  below : (ε : ℚ₊) → x - rat ⟨ ε ⟩₊ < x
  below ε =
    subst (x - rat ⟨ ε ⟩₊ <_) (subAddCancel x (rat ⟨ ε ⟩₊))
      ( <+rat (x - rat ⟨ ε ⟩₊) ε)
