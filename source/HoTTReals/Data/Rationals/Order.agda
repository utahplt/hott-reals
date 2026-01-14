module HoTTReals.Data.Rationals.Order where

import Cubical.Data.Bool as Bool
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Int.Base as ℤ using (ℤ)
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Int.Properties as ℤ using ()
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.HITs.SetQuotients as SetQuotients using ()
open import Cubical.Relation.Binary.Order
open import Cubical.Relation.Nullary

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic
open import HoTTReals.Data.Rationals.Properties

0<+' : {x y : ℚ} → 0 < x → 0 < y → 0 < x + y
0<+' {x} {y} p q = r
 -- Don't need `subst` because the path is refl
  where
  r : 0 + 0 < x + y
  r = <Monotone+ 0 x 0 y p q

0≤+ : {x y : ℚ} → 0 ≤ x → 0 ≤ y → 0 ≤ x + y
0≤+ {x} {y} p q = r
  where
  r : 0 + 0 ≤ x + y
  r = ≤Monotone+ 0 x 0 y p q

0<· : {x y : ℚ} → 0 < x → 0 < y → 0 < x · y
0<· {x} {y} p q = subst (λ ?x → ?x < x · y) (·AnnihilL y) r
  where
  r : 0 · y < x · y
  r = <-·o 0 x y q p

-- TODO: Rename to -Dist≤
≤antitone- : {x y : ℚ} → x ≤ y → - y ≤ - x
≤antitone- {x} {y} = SetQuotients.elimProp2 {P = λ x y → x ≤ y → (- y) ≤ (- x)} p q x y
  where
  p : (x y : ℚ) → isProp (x ≤ y → (- y) ≤ (- x))
  p x y = isProp→ (isProp≤ (- y) (- x))

  q : (u v : ℤ × ℕ₊₁) → [ u ] ≤ [ v ] → (- [ v ]) ≤ (- [ u ])
  q (a , b) (c , d) p = t
    where
    r : ℤ.- (c ℤ.· (ℕ₊₁→ℤ b)) ℤ.≤ ℤ.- (a ℤ.· (ℕ₊₁→ℤ d))
    r = ℤ.-Dist≤ p

    s : (c : ℤ) (b : ℕ₊₁) →
        ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ b) ≡ ℤ.- (c ℤ.· (ℕ₊₁→ℤ b))
    s c b =
      ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ b)
        ≡⟨ cong (λ ?x → (-1 ℤ.· c) ℤ.· ℕ₊₁→ℤ ?x) (·₊₁-identityˡ b) ⟩
      ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ b
        ≡⟨ refl ⟩
      (ℤ.- c) ℤ.· ℕ₊₁→ℤ b
        ≡⟨ sym $ ℤ.-DistL· c (ℕ₊₁→ℤ b) ⟩
      ℤ.- (c ℤ.· (ℕ₊₁→ℤ b)) ∎

    t : ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ b) ℤ.≤ ((-1) ℤ.· a) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ d)
    t = subst2 (λ ?x ?y → ?x ℤ.≤ ?y) (sym $ s c b) (sym $ s a d) r

<antitone- : {x y : ℚ} → x < y → - y < - x
<antitone- {x} {y} = SetQuotients.elimProp2 {P = λ x y → x < y → - y < - x} p q x y 
  where
  p : (x y : ℚ) → isProp (x < y → (- y) < (- x))
  p x y = isProp→ (isProp< (- y) (- x))

  q : (u v : ℤ × ℕ₊₁) → [ u ] < [ v ] → (- [ v ]) < (- [ u ])
  q (a , b) (c , d) p = t
    where
    r : ℤ.- (c ℤ.· (ℕ₊₁→ℤ b)) ℤ.< ℤ.- (a ℤ.· (ℕ₊₁→ℤ d))
    r = ℤ.-Dist< p

    -- TODO: Copypasta from above
    s : (c : ℤ) (b : ℕ₊₁) →
        ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ b) ≡ ℤ.- (c ℤ.· (ℕ₊₁→ℤ b))
    s c b =
      ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ b)
        ≡⟨ cong (λ ?x → (-1 ℤ.· c) ℤ.· ℕ₊₁→ℤ ?x) (·₊₁-identityˡ b) ⟩
      ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ b
        ≡⟨ refl ⟩
      (ℤ.- c) ℤ.· ℕ₊₁→ℤ b
        ≡⟨ sym $ ℤ.-DistL· c (ℕ₊₁→ℤ b) ⟩
      ℤ.- (c ℤ.· (ℕ₊₁→ℤ b)) ∎

    t : ((-1) ℤ.· c) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ b) ℤ.< ((-1) ℤ.· a) ℤ.· ℕ₊₁→ℤ (1 ·₊₁ d)
    t = subst2 (λ ?x ?y → ?x ℤ.< ?y) (sym $ s c b) (sym $ s a d) r

<→≠ : {x y : ℚ} → x < y → ¬ x ≡ y
<→≠ {x} {y} p q = isIrrefl< y (subst (λ ?z → ?z < y) q p)

0<⁻¹ : {x : ℚ} (p : 0 < x) → 0 < x [ ≠-symmetric (<→≠ p) ]⁻¹
0<⁻¹ {x} =
  SetQuotients.elimProp
    {P = λ x → (p : 0 < x) → 0 < x [ ≠-symmetric (<→≠ p) ]⁻¹}
    (λ x → isPropΠ (λ p → isProp< 0 (x [ ≠-symmetric (<→≠ p) ]⁻¹)))
    q x
  where
  q : (u : ℤ × ℕ₊₁) (p : 0 < [ u ]) → 0 < ([ u ] [ ≠-symmetric (<→≠ p) ]⁻¹)
  q (ℤ.pos zero , (1+ m)) p = Empty.rec (isIrrefl< 0 r)
    where
    p' : 0 ℤ.· (ℕ₊₁→ℤ (1+ m)) ℤ.< 0 ℤ.· 1
    p' = p

    r : 0 < 0
    -- TODO: Why are annihilator laws not working?
    r = subst2 ℤ._≤_ refl refl p'
  q (ℤ.pos (suc n) , (1+ m)) p = s
    where
    r : 0 ℤ.< ℕ₊₁→ℤ (1+ m)
    r = m , s
      where
      s : (ℤ.sucℤ 0) ℤ.+pos m ≡ ℕ₊₁→ℤ (1+ m)
      s = (ℤ.sucℤ 0) ℤ.+pos m
            ≡⟨ refl ⟩
          1 ℤ.+ (ℤ.pos m)
            ≡⟨ ℤ.+Comm 1 (ℤ.pos m) ⟩
          (ℤ.pos m) ℤ.+ 1
            ≡⟨ refl ⟩
          ℕ₊₁→ℤ (1+ m) ∎

    s : 0 ℤ.· (ℤ.pos (suc n)) ℤ.< (ℕ₊₁→ℤ (1+ m)) ℤ.· 1
    s = subst2 (λ ?x ?y → ?x ℤ.< ?y)
               (sym (ℤ.·AnnihilL (ℤ.pos (suc n))))
               (sym (ℤ.·IdR (ℕ₊₁→ℤ (1+ m))))
               r
  q (ℤ.negsuc n , (1+ m)) p = Empty.rec (ℤ.¬pos≤negsuc r)
    where
    p' : 0 ℤ.· (ℤ.pos (suc m)) ℤ.< ℤ.negsuc n ℤ.· 1
    p' = p

    r : ℤ.pos (suc 0) ℤ.≤ ℤ.negsuc n
    r = subst2 ℤ._≤_ refl (ℤ.·IdR (ℤ.negsuc n)) p' 

⁻¹-positiveAntitone :
  {x y : ℚ} (p : 0 < x) →
  (q : x ≤ y) →
  let r : ¬ x ≡ 0
      r = ≠-symmetric (<→≠ p)

      s : ¬ y ≡ 0
      s = ≠-symmetric (<→≠ (isTrans<≤ 0 x y p q))
  in (y [ s ]⁻¹) ≤ (x [ r ]⁻¹)
⁻¹-positiveAntitone {x} {y} p q = subst2 _≤_ w α β
  where
  r : ¬ x ≡ 0
  r = ≠-symmetric (<→≠ p)

  s : ¬ y ≡ 0
  s = ≠-symmetric (<→≠ (isTrans<≤ 0 x y p q))

  t : 0 < x · y
  t = 0<· {x = x} {y = y} p (isTrans<≤ 0 x y p q)

  u : ¬ x · y ≡ 0
  u = ≠-symmetric (<→≠ t)

  v : 0 < ((x · y) [ u ]⁻¹)
  v = 0<⁻¹ {x = x · y} t

  w : x · ((x · y) [ u ]⁻¹) ≡ y [ s ]⁻¹
  w = x · ((x · y) [ u ]⁻¹)
         ≡⟨ cong (_·_ x) (·⁻¹' x y r s u) ⟩
       x · ((x [ r ]⁻¹) · (y [ s ]⁻¹))
         ≡⟨ ·Assoc x (x [ r ]⁻¹) (y [ s ]⁻¹) ⟩
       (x · (x [ r ]⁻¹)) · (y [ s ]⁻¹)
         ≡⟨ cong (flip _·_ (y [ s ]⁻¹)) (⁻¹-inverse x r) ⟩
       1 · (y [ s ]⁻¹)
         ≡⟨ ·IdL (y [ s ]⁻¹) ⟩
       y [ s ]⁻¹ ∎

  α : y · ((x · y) [ u ]⁻¹) ≡ x [ r ]⁻¹ 
  α = y · ((x · y) [ u ]⁻¹)
         ≡⟨ cong (_·_ y) (·⁻¹ x y r s u) ⟩
       y · ((y [ s ]⁻¹) · (x [ r ]⁻¹))
         ≡⟨ ·Assoc y (y [ s ]⁻¹) (x [ r ]⁻¹) ⟩
       (y · (y [ s ]⁻¹)) · (x [ r ]⁻¹)
         ≡⟨ cong (flip _·_ (x [ r ]⁻¹)) (⁻¹-inverse y s) ⟩
       1 · (x [ r ]⁻¹)
         ≡⟨ ·IdL (x [ r ]⁻¹) ⟩
       x [ r ]⁻¹ ∎

  β : x · ((x · y) [ u ]⁻¹) ≤ y · ((x · y) [ u ]⁻¹)
  β = ≤-·o x y ((x · y) [ u ]⁻¹) (<Weaken≤ 0 ((x · y) [ u ]⁻¹) v) q

⁻¹-positiveStrictAntitone :
  {x y : ℚ} (p : 0 < x) →
  (q : x < y) →
  let r : ¬ x ≡ 0
      r = ≠-symmetric (<→≠ p)

      s : ¬ y ≡ 0
      s = ≠-symmetric (<→≠ (isTrans< 0 x y p q))
  in (y [ s ]⁻¹) < (x [ r ]⁻¹)
⁻¹-positiveStrictAntitone {x} {y} p q = subst2 _<_ w α β
  where
  r : ¬ x ≡ 0
  r = ≠-symmetric (<→≠ p)

  s : ¬ y ≡ 0
  s = ≠-symmetric (<→≠ ((isTrans< 0 x y p q)))

  t : 0 < x · y
  t = 0<· {x = x} {y = y} p ((isTrans< 0 x y p q))

  u : ¬ x · y ≡ 0
  u = ≠-symmetric (<→≠ t)

  v : 0 < ((x · y) [ u ]⁻¹)
  v = 0<⁻¹ {x = x · y} t

  w : x · ((x · y) [ u ]⁻¹) ≡ y [ s ]⁻¹
  w = x · ((x · y) [ u ]⁻¹)
         ≡⟨ cong (_·_ x) (·⁻¹' x y r s u) ⟩
       x · ((x [ r ]⁻¹) · (y [ s ]⁻¹))
         ≡⟨ ·Assoc x (x [ r ]⁻¹) (y [ s ]⁻¹) ⟩
       (x · (x [ r ]⁻¹)) · (y [ s ]⁻¹)
         ≡⟨ cong (flip _·_ (y [ s ]⁻¹)) (⁻¹-inverse x r) ⟩
       1 · (y [ s ]⁻¹)
         ≡⟨ ·IdL (y [ s ]⁻¹) ⟩
       y [ s ]⁻¹ ∎

  α : y · ((x · y) [ u ]⁻¹) ≡ x [ r ]⁻¹ 
  α = y · ((x · y) [ u ]⁻¹)
         ≡⟨ cong (_·_ y) (·⁻¹ x y r s u) ⟩
       y · ((y [ s ]⁻¹) · (x [ r ]⁻¹))
         ≡⟨ ·Assoc y (y [ s ]⁻¹) (x [ r ]⁻¹) ⟩
       (y · (y [ s ]⁻¹)) · (x [ r ]⁻¹)
         ≡⟨ cong (flip _·_ (x [ r ]⁻¹)) (⁻¹-inverse y s) ⟩
       1 · (x [ r ]⁻¹)
         ≡⟨ ·IdL (x [ r ]⁻¹) ⟩
       x [ r ]⁻¹ ∎

  β : x · ((x · y) [ u ]⁻¹) < y · ((x · y) [ u ]⁻¹)
  β = <-·o x y ((x · y) [ u ]⁻¹) (0<⁻¹ {x = x · y} t) q

0</ : {x y : ℚ} (p : 0 < x) (q : 0 < y) → 0 < x / y [ ≠-symmetric $ <→≠ q ]
0</ {x} {y} p q =
  0<· {x = x} {y = y [ ≠-symmetric (<→≠ q) ]⁻¹} p (0<⁻¹ {x = y} q)

<→0<- : {x y : ℚ} → x < y → 0 < y - x
<→0<- {x} {y} p = subst (flip _<_ (y - x)) q r
  where
  q : x + (- x) ≡ 0
  q = +InvR x

  r : x + (- x) < y + (- x)
  r = <-+o x y (- x) p

0<-→< : {x y : ℚ} → 0 < y - x → x < y
0<-→< {x} {y} p = subst2 _<_ q r (<-+o 0 (y - x) x p)
  where
  q : 0 + x ≡ x
  q = +IdL x

  r : (y - x) + x ≡ y
  r = subtractAddRightCancel x y

≤max' : (x y : ℚ) → y ≤ max x y
≤max' x y = subst (λ ?x → y ≤ ?x) (maxComm y x) (≤max y x)

≤→max' : {x y : ℚ} → y ≤ x → max x y ≡ x
≤→max' {x} {y} p = maxComm x y ∙ ≤→max y x p

≤→≠→< : {x y : ℚ} → x ≤ y → ¬ x ≡ y → x < y
≤→≠→< {x} {y} p q with x ≟ y
... | lt r = r
... | eq r = Empty.rec $ q r
... | gt r = Empty.rec $ ≤→≯ x y p r

≡max→≤₁ : {x y : ℚ} → max x y ≡ x → y ≤ x
≡max→≤₁ {x} {y} p = subst (_≤_ y) p (≤max' x y)

≡max→≤₂ : {x y : ℚ} → max x y ≡ y → x ≤ y
≡max→≤₂ {x} {y} p = subst (_≤_ x) p (≤max x y)

maxLeastUpperBound : {x y z : ℚ} →
                     x ≤ z → y ≤ z → max x y ≤ z
maxLeastUpperBound {x} {y} {z} p q = ≡max→≤₂ {x = max x y} {y = z} r
  where
  p' : max x z ≡ z
  p' = ≤→max x z p

  q' : max y z ≡ z
  q' = ≤→max y z q

  r : max (max x y) z ≡ z
  r = max (max x y) z
        ≡⟨ (sym $ maxAssoc x y z) ⟩
      max x (max y z)
        ≡⟨ cong (max x) q' ⟩
      max x z
        ≡⟨ p' ⟩
      z ∎

maxLeastUpperBound< : {x y z : ℚ} →
                      x < z → y < z → max x y < z
maxLeastUpperBound< {x} {y} {z} p q =
  ≤→≠→<
    {x = max x y} {y = z}
    (maxLeastUpperBound {x = x} {y = y} {z = z}
                        (<Weaken≤ x z p) (<Weaken≤ y z q))
    r'
  where
  r : max x y ≡ z → (x ≤ y) ⊎ (y ≤ x) → ⊥
  r s (inl t) = Empty.rec $ <→≠ q u
    where
    t' : max x y ≡ y
    t' = ≤→max x y t

    u : y ≡ z
    u = sym t' ∙ s 
  r s (inr t) = Empty.rec $ <→≠ p u
    where
    t' : max x y ≡ x
    t' = ≤→max' t

    u : x ≡ z
    u = sym t' ∙ s

  r' : ¬ max x y ≡ z
  r' s = PropositionalTruncation.rec Empty.isProp⊥ (r s) (isTotal≤ x y)

min≤' : (x y : ℚ) → min x y ≤ y
min≤' x y = subst (λ ?x → ?x ≤ y) (minComm y x) (min≤ y x)

≤→min' : (x y : ℚ) → y ≤ x → min x y ≡ y
≤→min' x y p = minComm x y ∙ ≤→min y x p

≡min→≤₁ : {x y : ℚ} → min x y ≡ x → x ≤ y
≡min→≤₁ {x} {y} p = subst (λ ?x → ?x ≤ y) p (min≤' x y) 

≡min→≤₂ : {x y : ℚ} → min x y ≡ y → y ≤ x
≡min→≤₂ {x} {y} p = subst (λ ?x → ?x ≤ x) p (min≤ x y)

minGreatestLowerBound : {x y z : ℚ} →
                        z ≤ x → z ≤ y → z ≤ min x y
minGreatestLowerBound {x} {y} {z} p q = ≡min→≤₁ r
  where
  p' : min z x ≡ z
  p' = ≤→min z x p

  q' : min z y ≡ z
  q' = ≤→min z y q

  r : min z (min x y) ≡ z
  r = min z (min x y)
        ≡⟨ minAssoc z x y ⟩
      min (min z x) y
        ≡⟨ cong (flip min y) p' ⟩
      min z y
        ≡⟨ q' ⟩
      z ∎

minGreatestLowerBound< : {x y z : ℚ} →
                         z < x → z < y → z < min x y
minGreatestLowerBound< {x} {y} {z} p q =
  ≤→≠→< {x = z} {y = min x y}
        (minGreatestLowerBound {x} {y} {z} (<Weaken≤ z x p) (<Weaken≤ z y q))
        r'
  where
  r : z ≡ min x y → (x ≤ y) ⊎ (y ≤ x) → ⊥
  r s (inl t) = Empty.rec $ <→≠ p u
    where
    t' : min x y ≡ x
    t' = ≤→min x y t

    u : z ≡ x
    u = s ∙ t'
  r s (inr t) = Empty.rec $ <→≠ q u
    where
    t' : min x y ≡ y
    t' = ≤→min' x y t

    u : z ≡ y
    u = s ∙ t'

  r' : ¬ z ≡ min x y
  r' s = PropositionalTruncation.rec Empty.isProp⊥ (r s) (isTotal≤ x y)

∣∣≤→≤₁ : {x ε : ℚ} → ∣ x ∣ ≤ ε → x ≤ ε
∣∣≤→≤₁ {x} {ε} p = isTrans≤ x ∣ x ∣ ε (≤max x (- x)) p

∣∣≤→≤₂ : {x ε : ℚ} → ∣ x ∣ ≤ ε → - ε ≤ x
∣∣≤→≤₂ {x} {ε} p = isTrans≤ (- ε) (- ∣ x ∣) x q r''
  where
  q : - ε ≤ - ∣ x ∣
  q = ≤antitone- {x = ∣ x ∣} {y = ε} p

  r : - x ≤ ∣ x ∣
  r = ≤max' x (- x)

  r' : - ∣ x ∣ ≤ - - x
  r' = ≤antitone- {x = - x} {y = ∣ x ∣} r

  r'' : - ∣ x ∣ ≤ x
  r'' = subst (_≤_ (- ∣ x ∣)) (-Invol x) r'

≤→∣∣≤ : {x ε : ℚ} → x ≤ ε → - ε ≤ x → ∣ x ∣ ≤ ε
≤→∣∣≤ {x} {ε} p q = maxLeastUpperBound {x = x} {y = - x} {z = ε} p q'
  where
  r : - x ≤ - - ε
  r = ≤antitone- {x = - ε} {y = x} q

  q' : - x ≤ ε
  q' = subst (_≤_ (- x)) (-Invol ε) r

∣∣<→<₁ : {x ε : ℚ} → ∣ x ∣ < ε → x < ε
∣∣<→<₁ {x} {ε} p = isTrans≤< x (∣ x ∣) ε (≤max x (- x)) p

∣∣<→<₂ : {x ε : ℚ} → ∣ x ∣ < ε → - ε < x
∣∣<→<₂ {x} {ε} p = isTrans<≤ (- ε) (- ∣ x ∣) x q r''
  where
  q : - ε < - ∣ x ∣
  q = <antitone- {x = ∣ x ∣} {y = ε} p

  r : - x ≤ ∣ x ∣
  r = ≤max' x (- x)

  r' : - ∣ x ∣ ≤ - - x
  r' = ≤antitone- {x = - x} {y = ∣ x ∣} r

  r'' : - ∣ x ∣ ≤ x
  r'' = subst (_≤_ (- ∣ x ∣)) (-Invol x) r'

<→∣∣< : {x ε : ℚ} → x < ε → - ε < x → ∣ x ∣ < ε
<→∣∣< {x} {ε} p q = maxLeastUpperBound< {x = x} {y = - x} {z = ε} p q'
  where
  r : - x < - - ε
  r = <antitone- {x = - ε} {y = x} q

  q' : - x < ε
  q' = subst (_<_ (- x)) (-Invol ε) r

0≤∣∣ : (x : ℚ) → 0 ≤ ∣ x ∣
0≤∣∣ x = PropositionalTruncation.rec (isProp≤ 0 (∣ x ∣)) p (isTotal≤ 0 x)
  where
  p : (0 ≤ x) ⊎ (x ≤ 0) → 0 ≤ ∣ x ∣
  p (inl q) = isTrans≤ 0 x (∣ x ∣) q (≤max x (- x))
  p (inr q) = isTrans≤ 0 (- x) (∣ x ∣) (≤antitone- {x = x} q) (≤max' x (- x))

∣-∣≡∣∣ : (x : ℚ) → ∣ - x ∣ ≡ ∣ x ∣
∣-∣≡∣∣ x =
  ∣ - x ∣
    ≡⟨ refl ⟩
  max (- x) (- (- x))
    ≡⟨ cong (max (- x)) (-Invol x) ⟩
  max (- x) x
    ≡⟨ maxComm (- x) x ⟩
  max x (- x)
    ≡⟨ refl ⟩
  ∣ x ∣ ∎

-∣∣≤self : (x : ℚ) → - ∣ x ∣ ≤ x
-∣∣≤self x = subst (_≤_ (- ∣ x ∣)) (-Invol x) q
  where
  p : - x ≤ ∣ x ∣
  p = ≤max' x (- x)

  q : - ∣ x ∣ ≤ - - x
  q = ≤antitone- {x = - x} {y = ∣ x ∣} p

subtract<→negate<subtract : (x y ε : ℚ) → x - y < ε → - ε < y - x
subtract<→negate<subtract x y ε p =
  subst (_<_ (- ε)) (negateSubtract' x y) (<antitone- {x = x - y} {y = ε} p)

negate<subtract→subtract< : (x y ε : ℚ) → - ε < y - x → x - y < ε
negate<subtract→subtract< x y ε p =
  subst2 _<_ (negateSubtract' y x)
             (-Invol ε)
             (<antitone- {x = - ε} {y = y - x} p)

≤-o· : {x y z : ℚ} → 0 ≤ x → y ≤ z → x · y ≤ x · z
≤-o· {x} {y} {z} p q =
  subst2 (λ ?a ?b → ?a ≤ ?b)
         (·Comm y x) (·Comm z x)
         (≤-·o y z x p q)

<-o· : {x y z : ℚ} → 0 < x → y < z → x · y < x · z
<-o· {x} {y} {z} p q =
  subst2 (λ ?a ?b → ?a < ?b)
         (·Comm y x) (·Comm z x)
         (<-·o y z x p q)

+≤+ : {x y z w : ℚ} → x ≤ y → z ≤ w → x + z ≤ y + w
+≤+ {x} {y} {z} {w} p q =
  isTrans≤ (x + z) (y + z) (y + w)
           (≤-+o x y z p)
           (≤-o+ z w y q)

+<+ : {x y z w : ℚ} → x < y → z < w → x + z < y + w
+<+ {x} {y} {z} {w} p q =
  isTrans< (x + z) (y + z) (y + w)
           (<-+o x y z p)
           (<-o+ z w y q)

·≤· : {x y z w : ℚ} → x ≤ z → y ≤ w → 0 ≤ z → 0 ≤ y → x · y ≤ z · w
·≤· {x} {y} {z} {w} p q r s =
  isTrans≤ (x · y) (z · y) (z · w)
           (≤-·o x z y s p)
           (≤-o· {x = z} {y = y} {z = w} r q)

<→≤→·<· : {x y z w : ℚ} → x < z → y ≤ w → 0 ≤ z → 0 < y → x · y < z · w
<→≤→·<· {x} {y} {z} {w} p q r s =
  isTrans<≤ (x · y) (z · y) (z · w)
            (<-·o x z y s p)
            (≤-o· {x = z} {y = y} {z = w} r q)

≤→<→·<· : {x y z w : ℚ} → x ≤ z → y < w → 0 < z → 0 ≤ y → x · y < z · w
≤→<→·<· {x} {y} {z} {w} p q r s =
  isTrans≤< (x · y) (z · y) (z · w)
            (≤-·o x z y s p)
            (<-o· {x = z} {y = y} {z = w} r q)

magntidueTriangleInequality : (x y : ℚ) → ∣ x + y ∣ ≤ ∣ x ∣ + ∣ y ∣
magntidueTriangleInequality x y = ≤→∣∣≤ {x = x + y} {ε = ∣ x ∣ + ∣ y ∣} p q
  where
  p : x + y ≤ ∣ x ∣ + ∣ y ∣
  p = +≤+ {x = x} {y = ∣ x ∣} {z = y} {w = ∣ y ∣} (≤max x (- x)) (≤max y (- y))

  q : (- (∣ x ∣ + ∣ y ∣)) ≤ x + y
  q = subst (flip _≤_ (x + y))
            (sym $ negateAdd ∣ x ∣ ∣ y ∣)
            (+≤+ {x = - ∣ x ∣} {y = x} {z = - ∣ y ∣} {w = y}
                 (-∣∣≤self x) (-∣∣≤self y))

distanceCommutative : (x y : ℚ) → distance x y ≡ distance y x
distanceCommutative x y =
  distance x y
    ≡⟨ sym $ ∣-∣≡∣∣ (x - y) ⟩
  ∣ - (x - y) ∣
    ≡⟨ cong ∣_∣ (negateSubtract' x y) ⟩
  ∣ y - x ∣
    ≡⟨ refl ⟩
  distance y x ∎

distanceTriangleInequality :
  (x y z : ℚ) → distance x z ≤ distance x y + distance y z
distanceTriangleInequality x y z =
  subst (flip _≤_ (∣ x - y ∣ + ∣ y - z ∣))
        (cong ∣_∣ p)
        (magntidueTriangleInequality (x - y) (y - z))
  where
  p : (x - y) + (y - z) ≡ x - z
  p = (x - y) + (y - z)
        ≡⟨ +Assoc (x - y) y (- z) ⟩
      ((x - y) + y) - z
        ≡⟨ cong (flip _-_ z) (subtractAddRightCancel y x) ⟩
      x - z ∎

∣∣<-open :
  (x : ℚ) (ε : ℚ) (φ : 0 < ε) →
  ∣ x ∣ < ε →
  ∃ ℚ (λ θ → (0 < θ) ×
           Σ (0 < ε - θ)
           (λ ψ → ∣ x ∣ < ε - θ))
∣∣<-open x ε φ ψ = ∣ θ , χ' , τ , σ'' ∣₁
  where
  ω : ¬ 2 ≡ 0
  ω = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt
  
  ω' : 0 < 2 [ ω ]⁻¹
  ω' = Bool.toWitness {Q = <Dec 0 (2 [ ω ]⁻¹)} tt
  
  ω'' : 0 < 2
  ω'' = Bool.toWitness {Q = <Dec 0 2} tt
  
  θ : ℚ
  θ = (ε - ∣ x ∣) / 2 [ ω ]
  
  χ : 0 < ε - ∣ x ∣
  χ = <→0<- {x = ∣ x ∣} {y = ε} ψ
  
  χ' : 0 < θ
  χ' = 0</ {x = ε - ∣ x ∣} {y = 2} χ ω''
  
  π : 2 [ ω ]⁻¹ · ∣ x ∣ + 2 [ ω ]⁻¹ · ∣ x ∣ ≡ ∣ x ∣
  π = 2⁻¹+≡self ∣ x ∣
  
  ρ : ε - θ ≡ 2 [ ω ]⁻¹ · ε + 2 [ ω ]⁻¹ · ∣ x ∣
  ρ =
    ε - ((ε - ∣ x ∣) / 2 [ ω ])
      ≡⟨ cong (_-_ ε) (·DistR+ ε (- ∣ x ∣) (2 [ ω ]⁻¹)) ⟩
    ε - (ε / 2 [ ω ] + (- ∣ x ∣) / 2 [ ω ])
      ≡⟨ cong (_+_ ε) (negateAdd (ε / 2 [ ω ]) ((- ∣ x ∣) / 2 [ ω ])) ⟩
    ε + (- (ε / 2 [ ω ]) + - ((- ∣ x ∣) / 2 [ ω ]))
      ≡⟨ +Assoc ε (- (ε / 2 [ ω ])) (- ((- ∣ x ∣) / 2 [ ω ])) ⟩
    (ε - (ε / 2 [ ω ])) + - ((- ∣ x ∣) / 2 [ ω ])
       ≡⟨ cong (flip _+_ _) (self-self/2≡self/2 ε) ⟩
    (ε / 2 [ ω ]) + - ((- ∣ x ∣) / 2 [ ω ])
       ≡⟨ cong (_+_ (ε / 2 [ ω ])) (-·≡-· (- ∣ x ∣) (2 [ ω ]⁻¹)) ⟩
    (ε / 2 [ ω ]) + (- - ∣ x ∣) / 2 [ ω ]
       ≡⟨ cong (λ ?x → (ε / 2 [ ω ]) + (?x / 2 [ ω ])) (-Invol ∣ x ∣) ⟩
    (ε / 2 [ ω ]) + (∣ x ∣) / 2 [ ω ]
       ≡⟨ cong₂ _+_ (·Comm ε (2 [ ω ]⁻¹)) (·Comm ∣ x ∣ (2 [ ω ]⁻¹)) ⟩
    2 [ ω ]⁻¹ · ε + 2 [ ω ]⁻¹ · ∣ x ∣ ∎
  
  σ : 2 [ ω ]⁻¹ · ∣ x ∣ < 2 [ ω ]⁻¹ · ε
  σ = <-o· {x = 2 [ ω ]⁻¹} {y = ∣ x ∣} {z = ε} ω' ψ
    
  σ' : 2 [ ω ]⁻¹ · ∣ x ∣ + 2 [ ω ]⁻¹ · ∣ x ∣ <
     2 [ ω ]⁻¹ · ε + 2 [ ω ]⁻¹ · ∣ x ∣
  σ' = <-+o (2 [ ω ]⁻¹ · ∣ x ∣)
               (2 [ ω ]⁻¹ · ε)
               (2 [ ω ]⁻¹ · ∣ x ∣)
               σ
                   
  σ'' : ∣ x ∣ < ε - θ
  σ'' = subst2 _<_ π (sym ρ) σ'

  τ : 0 < ε - θ
  τ = isTrans≤< 0 ∣ x ∣ (ε - θ) (0≤∣∣ (x)) σ''

-distance : (x y : ℚ) → distance (- x) (- y) ≡ distance x y
-distance x y =
  ∣ (- x) - (- y) ∣
    ≡⟨ cong ∣_∣ (sym $ negateAdd x (- y)) ⟩
  ∣ - (x - y) ∣
    ≡⟨ ∣-∣≡∣∣ (x - y) ⟩
  ∣ x - y ∣ ∎

+distanceᵣ : (x y z : ℚ) →
             distance (x + z) (y + z) ≡ distance x y
+distanceᵣ x y z = cong ∣_∣ φ
  where
  φ = (x + z) - (y + z)
        ≡⟨ cong (_+_ (x + z)) (negateAdd y z) ⟩
      (x + z) + (- y + - z)
        ≡⟨ sym $ +Assoc x z (- y + - z) ⟩
      x + (z + (- y + - z))
        ≡⟨ cong (_+_ x) (+Assoc z (- y) (- z)) ⟩
      x + ((z + - y) + - z)
        ≡⟨ cong (λ ?x → (x + (?x + - z))) (+Comm z (- y)) ⟩
      x + ((- y + z) + - z)
        ≡⟨ (cong (_+_ x) $ sym (+Assoc (- y) z (- z))) ⟩
      x + (- y + (z + - z))
        ≡⟨ cong (λ ?x → x + (- y + ?x)) (+InvR z) ⟩
      x + (- y + 0)
        ≡⟨ cong (_+_ x) (+IdR $ - y) ⟩
      x + - y ∎

+distanceₗ : (x y z : ℚ) →
             distance (x + y) (x + z) ≡ distance y z
+distanceₗ x y z =
  distance (x + y) (x + z)
    ≡⟨ cong₂ distance (+Comm x y) (+Comm x z) ⟩
  distance (y + x) (z + x)
    ≡⟨ +distanceᵣ y z x ⟩
  distance y z ∎

ℚ-isPoset : IsPoset _≤_
ℚ-isPoset = isposet isSetℚ isProp≤ isRefl≤ isTrans≤ isAntisym≤

ℚ-posetStructure : PosetStr ℓ-zero ℚ
ℚ-posetStructure = posetstr _≤_ ℚ-isPoset

ℚ-isQuoset : IsQuoset _<_
ℚ-isQuoset = isquoset isSetℚ isProp< isIrrefl< isTrans< isAsym<

ℚ-quosetStructure : QuosetStr ℓ-zero ℚ
ℚ-quosetStructure = quosetstr _<_ ℚ-isQuoset

0<1 : 0 < 1
0<1 = Bool.toWitness {Q = <Dec 0 1} tt

0<2 : 0 < 2
0<2 = Bool.toWitness {Q = <Dec 0 2} tt
