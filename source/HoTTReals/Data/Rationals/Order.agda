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

0<1 : 0 < 1
0<1 = Bool.toWitness {Q = <Dec 0 1} tt

0<2 : 0 < 2
0<2 = Bool.toWitness {Q = <Dec 0 2} tt

0≤2 : 0 ≤ 2
0≤2 = Bool.toWitness {Q = ≤Dec 0 2} tt

0≤2⁻¹ : 0 ≤ 2 [ 2≠0 ]⁻¹
0≤2⁻¹ = Bool.toWitness {Q = ≤Dec 0 (2 [ 2≠0 ]⁻¹)} tt

-2⁻¹≤0 : - (2 [ 2≠0 ]⁻¹) ≤ 0
-2⁻¹≤0 = Bool.toWitness {Q = ≤Dec (- (2 [ 2≠0 ]⁻¹)) 0} tt

-2⁻¹≤2⁻¹ : - (2 [ 2≠0 ]⁻¹)  ≤ 2 [ 2≠0 ]⁻¹
-2⁻¹≤2⁻¹ = Bool.toWitness {Q = ≤Dec (- (2 [ 2≠0 ]⁻¹)) (2 [ 2≠0 ]⁻¹)} tt 

0<2⁻¹ : 0 < 2 [ 2≠0 ]⁻¹
0<2⁻¹ = Bool.toWitness {Q = <Dec 0 (2 [ 2≠0 ]⁻¹)} tt

0<4 : 0 ℚ.< 4
0<4 = Bool.toWitness {Q = <Dec 0 4} tt

0<8 : 0 ℚ.< 8
0<8 = Bool.toWitness {Q = <Dec 0 8} tt

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

≤→0≤- : {x y : ℚ} → x ≤ y → 0 ≤ y - x
≤→0≤- {x} {y} p =
  subst (flip _≤_ $ (y - x)) r q
  where
  q : x - x ≤ y - x
  q = ≤-+o x y (- x) p

  r : x - x ≡ 0
  r = +InvR x

≤→-≤0 : {x y : ℚ} → x ≤ y → x - y ≤ 0
≤→-≤0 {x} {y} p =
  subst (_≤_ $ x - y) r q
  where
  q : x - y ≤ y - y
  q = ≤-+o x y (- y) p

  r : y - y ≡ 0
  r = +InvR y

0≤-→≤ : {x y : ℚ} → 0 ≤ y - x → x ≤ y
0≤-→≤ {x} {y} p =
  subst2 _≤_ r s q
  where
  q : 0 + x ≤ (y - x) + x
  q = ≤-+o 0 (y - x) x p

  r : 0 + x ≡ x
  r = +IdL x

  s : (y - x) + x ≡ y
  s = subtractAddRightCancel x y

≤+→-≤ : {x y z : ℚ} → x ≤ y + z → x - z ≤ y
≤+→-≤ {x} {y} {z} φ = ψ'
  where
  ψ : x - z ≤ (y + z) - z
  ψ = ≤-+o x (y + z) (- z) φ

  ψ' : x - z ≤ y
  ψ' = subst (_≤_ $ x - z) (addSubtractRightCancel y z) ψ

+≤→≤- : {x y z : ℚ} → x + y ≤ z → x ≤ z - y
+≤→≤- {x} {y} {z} φ = ψ'
  where
  ψ : (x + y) - y ≤ z - y
  ψ = ≤-+o (x + y) z (- y) φ

  ψ' : x ≤ z - y
  ψ' = subst (flip _≤_ $ z - y) (addSubtractRightCancel x y) ψ

≤max' : (x y : ℚ) → y ≤ max x y
≤max' x y = subst (λ ?x → y ≤ ?x) (maxComm y x) (≤max y x)

≤→max' : {x y : ℚ} → y ≤ x → max x y ≡ x
≤→max' {x} {y} p = maxComm x y ∙ ≤→max y x p

-- TODO: This is a more fundamental one from below composed with negation
-- resolution
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

0≤→∣∣≡self : (x : ℚ) → 0 ≤ x → ∣ x ∣ ≡ x
0≤→∣∣≡self x φ = ≤→max' ψ
  where
  ψ : - x ≤ x
  ψ = isTrans≤ (- x) 0 x (≤antitone- {x = 0} {y = x} φ) φ

0≤-→∣∣≡negateSelf : (x : ℚ) → 0 ≤ - x → ∣ x ∣ ≡ - x
0≤-→∣∣≡negateSelf x φ = ≤→max x (- x) ψ
  where
  ψ : x ≤ - x
  ψ = isTrans≤ x 0 (- x)
        (isTrans≤ x (- - x) 0
          (≡Weaken≤ x (- - x) (sym $ -Invol x))
          (≤antitone- {x = 0} {y = - x} φ))
        φ

≤0→∣∣≡negateSelf : (x : ℚ) → x ≤ 0 → ∣ x ∣ ≡ - x
≤0→∣∣≡negateSelf x φ = ≤→max x (- x) ψ
  where
  ψ : x ≤ - x
  ψ = isTrans≤ x 0 (- x) φ (≤antitone- {x = x} {y = 0} φ)

maxMultiplyLeftNonnegative :
  (a x y : ℚ) →
  0 ≤ a →
  max (a · x) (a · y) ≡ a · max x y
maxMultiplyLeftNonnegative a x y φ =
  PropositionalTruncation.rec (isSetℚ _ _) ψ' (isTotal≤ x y)
  where
  ψ' : (x ≤ y) ⊎ (y ≤ x) → max (a · x) (a · y) ≡ a · max x y
  ψ' (inl ω) = ρ
    where
    χ : max (a · x) (a · y) ≡ a · y
    χ = ≤→max (a · x) (a · y) (≤-o· {x = a} {y = x} {z = y} φ ω)

    π : max x y ≡ y
    π = ≤→max x y ω

    ρ : max (a · x) (a · y) ≡ a · max x y
    ρ = χ ∙ cong (_·_ a) (sym π)
  ψ' (inr ω) = ρ
    where
    χ : max (a · x) (a · y) ≡ a · x
    χ = ≤→max' (≤-o· {x = a} {y = y} {z = x} φ ω)

    π : max x y ≡ x
    π = ≤→max' ω

    ρ : max (a · x) (a · y) ≡ a · max x y
    ρ = χ ∙ cong (_·_ a) (sym π)

maxMultiplyRightNonnegative :
  (a x y : ℚ) →
  0 ≤ a →
  max (x · a) (y · a) ≡ a · max x y
maxMultiplyRightNonnegative a x y φ = ψ ∙ ω
  where
  ψ : max (x · a) (y · a) ≡ max (a · x) (a · y)
  ψ = cong₂ max (·Comm x a) (·Comm y a)

  ω : max (a · x) (a · y) ≡ a · max x y
  ω = maxMultiplyLeftNonnegative a x y φ

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

subtract≤→negate≤subtract : (x y ε : ℚ) → x - y ≤ ε → - ε ≤ y - x
subtract≤→negate≤subtract x y ε p =
  subst (_≤_ (- ε)) (negateSubtract' x y) (≤antitone- {x = x - y} {y = ε} p)

negate≤subtract→subtract≤ : (x y ε : ℚ) → - ε ≤ y - x → x - y ≤ ε
negate≤subtract→subtract≤ x y ε p =
  subst2 _≤_ (negateSubtract' y x)
             (-Invol ε)
             (≤antitone- {x = - ε} {y = y - x} p)

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

0≤→0≤· : (x y : ℚ) → 0 ≤ x → 0 ≤ y → 0 ≤ x · y
0≤→0≤· x y φ ψ = ·≤· {x = 0} {y = 0} {z = x} {w = y} φ ψ φ (isRefl≤ 0)

≤0→0≤· : (x y : ℚ) → x ≤ 0 → y ≤ 0 → 0 ≤ x · y
≤0→0≤· x y φ ψ = ω'
  where
  ω : 0 ≤ (- x) · (- y)
  ω = 0≤→0≤· (- x) (- y)
    (≤antitone- {x = x} {y = 0} φ) (≤antitone- {x = y} {y = 0} ψ)

  χ : (- x) · (- y) ≡ x · y
  χ = -·-≡· x y

  ω' : 0 ≤ x · y
  ω' = subst (_≤_ 0) χ ω

magnitudeMultiply≡multiplyMagnitude :
  (x y : ℚ) →
  ∣ x · y ∣ ≡ ∣ x ∣ · ∣ y ∣
magnitudeMultiply≡multiplyMagnitude x y =
  rec2 (isSetℚ _ _) φ (isTotal≤ 0 x) (isTotal≤ 0 y)
  where
  φ : (0 ≤ x) ⊎ (x ≤ 0) → (0 ≤ y) ⊎ (y ≤ 0) → ∣ x · y ∣ ≡ ∣ x ∣ · ∣ y ∣
  φ (inl ψ) (inl ω) = τ
    where
    χ : 0 ≤ x · y
    χ = 0≤→0≤· x y ψ ω

    π : ∣ x · y ∣ ≡ x · y
    π = 0≤→∣∣≡self (x · y) χ

    ρ : ∣ x ∣ ≡ x
    ρ = 0≤→∣∣≡self x ψ

    σ : ∣ y ∣ ≡ y
    σ = 0≤→∣∣≡self y ω

    τ : ∣ x · y ∣ ≡ ∣ x ∣ · ∣ y ∣
    τ = π ∙ cong₂ _·_ (sym ρ) (sym σ)
  φ (inl ψ) (inr ω') = υ
    where
    χ : - (x · y) ≡ x · (- y)
    χ = -·≡·- x y

    π : 0 ≤ x · (- y)
    π = 0≤→0≤· x (- y) ψ (≤antitone- {x = y} {y = 0} ω')

    π' : 0 ≤ - (x · y)
    π' = isTrans≤ 0 (x · (- y)) (- (x · y))
                  π (≡Weaken≤ (x · (- y)) (- (x · y)) (sym χ))

    ρ : ∣ x · y ∣ ≡ - (x · y)
    ρ = 0≤-→∣∣≡negateSelf (x · y) π'

    σ : ∣ x ∣ ≡ x
    σ = 0≤→∣∣≡self x ψ

    τ : ∣ y ∣ ≡ - y
    τ = ≤0→∣∣≡negateSelf y ω'

    υ : ∣ x · y ∣ ≡ ∣ x ∣ · ∣ y ∣
    υ = ∣ x · y ∣
          ≡⟨ ρ ⟩
        - (x · y)
          ≡⟨ χ ⟩
        x · (- y)
          ≡⟨ cong₂ _·_ (sym σ) (sym τ) ⟩
        ∣ x ∣ · ∣ y ∣ ∎
  φ (inr ψ') (inl ω) = υ
    where
    χ : - (x · y) ≡ (- x) · y
    χ = -·≡-· x y

    π : 0 ≤ (- x) · y
    π = 0≤→0≤· (- x) y (≤antitone- {x = x} {y = 0} ψ') ω

    π' : 0 ≤ - (x · y)
    π' = isTrans≤ 0 ((- x) · y) (- (x · y))
                  π (≡Weaken≤ ((- x) · y) (- (x · y)) (sym χ))

    ρ : ∣ x · y ∣ ≡ - (x · y)
    ρ = 0≤-→∣∣≡negateSelf (x · y) π'

    σ : ∣ x ∣ ≡ - x
    σ = ≤0→∣∣≡negateSelf x ψ'

    τ : ∣ y ∣ ≡ y
    τ = 0≤→∣∣≡self y ω

    υ : ∣ x · y ∣ ≡ ∣ x ∣ · ∣ y ∣
    υ = ∣ x · y ∣
          ≡⟨ ρ ⟩
        - (x · y)
          ≡⟨ χ ⟩
        (- x) · y
          ≡⟨ cong₂ _·_ (sym σ) (sym τ) ⟩
        ∣ x ∣ · ∣ y ∣ ∎
  φ (inr ψ') (inr ω') = υ
    where
    χ : 0 ≤ x · y
    χ = ≤0→0≤· x y ψ' ω'

    π : ∣ x · y ∣ ≡ x · y
    π = 0≤→∣∣≡self (x · y) χ

    ρ : ∣ x ∣ ≡ - x
    ρ = ≤0→∣∣≡negateSelf x ψ'

    σ : ∣ y ∣ ≡ - y
    σ = ≤0→∣∣≡negateSelf y ω'

    τ : (- x) · (- y) ≡ x · y
    τ = -·-≡· x y

    υ : ∣ x · y ∣ ≡ ∣ x ∣ · ∣ y ∣
    υ = π ∙ sym τ ∙ cong₂ _·_ (sym ρ) (sym σ)

magnitudeTriangleInequality : (x y : ℚ) → ∣ x + y ∣ ≤ ∣ x ∣ + ∣ y ∣
magnitudeTriangleInequality x y = ≤→∣∣≤ {x = x + y} {ε = ∣ x ∣ + ∣ y ∣} p q
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
        (magnitudeTriangleInequality (x - y) (y - z))
  where
  p : (x - y) + (y - z) ≡ x - z
  p = (x - y) + (y - z)
        ≡⟨ +Assoc (x - y) y (- z) ⟩
      ((x - y) + y) - z
        ≡⟨ cong (flip _-_ z) (subtractAddRightCancel y x) ⟩
      x - z ∎

magnitudeReverseTriangleInequality :
  (x y : ℚ) → 
  ∣ ∣ x ∣ - ∣ y ∣ ∣ ≤ ∣ x - y ∣
magnitudeReverseTriangleInequality x y =
  ≤→∣∣≤ {x = ∣ x ∣ - ∣ y ∣} {ε = ∣ x - y ∣} ω σ
  where
  φ : ∣ x ∣ ≡ ∣ (x - y) + y ∣
  φ = cong ∣_∣ (sym $ subtractAddRightCancel y x)

  ψ : ∣ (x - y) + y ∣ ≤ ∣ x - y ∣ + ∣ y ∣
  ψ = magnitudeTriangleInequality (x - y) y

  ψ' : ∣ x ∣ ≤ ∣ x - y ∣ + ∣ y ∣
  ψ' = subst (flip _≤_ $ ∣ x - y ∣ + ∣ y ∣) (sym φ) ψ

  ω : ∣ x ∣ - ∣ y ∣ ≤ ∣ x - y ∣
  ω = ≤+→-≤ {x = ∣ x ∣} {y = ∣ x - y ∣} {z = ∣ y ∣} ψ'

  χ : ∣ y ∣ ≡ ∣ (y - x) + x ∣
  χ = cong ∣_∣ (sym $ subtractAddRightCancel x y)

  π : ∣ (y - x) + x ∣ ≤ ∣ y - x ∣ + ∣ x ∣
  π = magnitudeTriangleInequality (y - x) x

  π' : ∣ y ∣ ≤ ∣ x - y ∣ + ∣ x ∣
  π' = subst2 (λ ?x ?y → ?x ≤ ?y + ∣ x ∣) (sym χ) (distanceCommutative y x) π

  ρ : ∣ y ∣ - ∣ x ∣ ≤ ∣ x - y ∣
  ρ = ≤+→-≤ {x = ∣ y ∣} {y = ∣ x - y ∣} {z = ∣ x ∣} π'

  σ : - ∣ x - y ∣ ≤ ∣ x ∣ - ∣ y ∣
  σ = subtract≤→negate≤subtract (∣ y ∣) (∣ x ∣) (∣ x - y ∣) ρ

<→<-midpoint : {x y : ℚ} → x < y → x < (x + y) / 2 [ 2≠0 ]
<→<-midpoint {x} {y} φ = ω'
  where
  ψ : x + x < x + y
  ψ = <-o+ x y x φ

  ψ' : 2 · x < x + y
  ψ' = subst (flip _<_ $ x + y) (self+≡2· x) ψ

  ω : (2 · x) / 2 [ 2≠0 ] < (x + y) / 2 [ 2≠0 ]
  ω = <-·o (2 · x) (x + y) (2 [ 2≠0 ]⁻¹) 0<2⁻¹ ψ'

  ω' : x < (x + y) / 2 [ 2≠0 ]
  ω' = subst (flip _<_ $ (x + y) / 2 [ 2≠0 ]) (·/' 2 x 2≠0) ω

<→midpoint-< : {x y : ℚ} → x < y → (x + y) / 2 [ 2≠0 ] < y
<→midpoint-< {x} {y} φ = ω'
  where
  ψ : x + y < y + y
  ψ = <-+o x y y φ

  ψ' : x + y < 2 · y
  ψ' = subst (_<_ $ x + y) (self+≡2· y) ψ

  ω : (x + y) / 2 [ 2≠0 ] < (2 · y) / 2 [ 2≠0 ]
  ω = <-·o (x + y) (2 · y) (2 [ 2≠0 ]⁻¹) 0<2⁻¹ ψ'

  ω' : (x + y) / 2 [ 2≠0 ] < y
  ω' = subst (_<_ $ (x + y) / 2 [ 2≠0 ]) (·/' 2 y 2≠0) ω

self/2<self : (θ : ℚ) (φ : 0 < θ) → θ / 2 [ 2≠0 ] < θ
self/2<self θ φ = ω
  where
  ψ : (0 + θ) / 2 [ 2≠0 ] < θ
  ψ = <→midpoint-< {x = 0} {y = θ} φ

  ω : θ / 2 [ 2≠0 ] < θ
  ω = subst (λ ?x → ?x / 2 [ 2≠0 ] < θ) (+IdL θ) ψ

-- TODO: Probably use these new midpoint lemmas above but I don't want to write
-- this
∣∣<-open :
  (x : ℚ) (ε : ℚ) (φ : 0 < ε) →
  ∣ x ∣ < ε →
  Σ ℚ (λ θ → (0 < θ) ×
           Σ (0 < ε - θ)
           (λ ψ → ∣ x ∣ < ε - θ))
∣∣<-open x ε φ ψ = θ , χ' , τ , σ''
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

≤→distance≡LeftSubtractRight :
  (x y : ℚ) →
  y ≤ x → distance x y ≡ x - y
≤→distance≡LeftSubtractRight x y φ = χ
  where
  ψ : 0 ≤ x - y
  ψ = ≤→0≤- {x = y} {y = x} φ

  ψ' : - (x - y) ≤ 0
  ψ' = ≤antitone- {x = 0} {y = x - y} ψ

  ω : - (x - y) ≤ x - y
  ω = isTrans≤ (- (x - y)) 0 (x - y) ψ' ψ

  χ : distance x y ≡ x - y
  χ = ≤→max' ω

≤→distance≡RightSubtractLeft :
  (x y : ℚ) →
  x ≤ y → distance x y ≡ y - x
≤→distance≡RightSubtractLeft x y φ = χ ∙ π
  where
  ψ : x - y ≤ 0
  ψ = (≤→-≤0 {x = x} {y = y} φ)

  ψ' : 0 ≤ - (x - y)
  ψ' = ≤antitone- {x = x - y} {y = 0} ψ

  ω : x - y ≤ - (x - y)
  ω = isTrans≤ (x - y) 0 (- (x - y)) ψ ψ'

  χ : distance x y ≡ - (x - y)
  χ = ≤→max (x - y) (- (x - y)) ω

  π : - (x - y) ≡ y - x
  π = negateSubtract' x y

ℚ-isPoset : IsPoset _≤_
ℚ-isPoset = isposet isSetℚ isProp≤ isRefl≤ isTrans≤ isAntisym≤

ℚ-posetStructure : PosetStr ℓ-zero ℚ
ℚ-posetStructure = posetstr _≤_ ℚ-isPoset

ℚ-isQuoset : IsQuoset _<_
ℚ-isQuoset = isquoset isSetℚ isProp< isIrrefl< isTrans< isAsym<

ℚ-quosetStructure : QuosetStr ℓ-zero ℚ
ℚ-quosetStructure = quosetstr _<_ ℚ-isQuoset

-- The max is equal to the midpoint + half the distance
max≡midpoint+halfDistance :
  (x y : ℚ) →
  max x y ≡ ((x + y) + distance x y) / 2 [ 2≠0 ]
max≡midpoint+halfDistance x y =
  PropositionalTruncation.rec (isSetℚ _ _) φ (isTotal≤ x y)
  where
  φ : (x ≤ y) ⊎ (y ≤ x) → max x y ≡ ((x + y + distance x y) / 2 [ 2≠0 ])
  φ (inl ψ) = σ
    where
    ω : max x y ≡ y
    ω = ≤→max x y ψ

    χ : distance x y ≡ y - x
    χ = ≤→distance≡RightSubtractLeft x y ψ

    π : (x + y) + (y - x) ≡ y + y
    π = (x + y) + (y - x)
          ≡⟨ cong (flip _+_ $ y - x) (+Comm x y) ⟩
        (y + x) + (y - x)
          ≡⟨ sym $ +Assoc y x (y - x) ⟩
        y + (x + (y - x))
          ≡⟨ cong (_+_ y) (addLeftSubtractCancel x y) ⟩
        y + y ∎

    ρ : (x + y + distance x y) / 2 [ 2≠0 ] ≡ y
    ρ = (x + y + distance x y) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → (x + y + ?x) / 2 [ 2≠0 ]) χ ⟩
        (x + y + (y - x)) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) π ⟩
        (y + y) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) (self+≡2· y) ⟩
        (2 · y) / 2 [ 2≠0 ]
          ≡⟨ ·/' 2 y 2≠0 ⟩
        y ∎

    σ : max x y ≡ ((x + y + distance x y) / 2 [ 2≠0 ])
    σ = ω ∙ sym ρ
  φ (inr ψ) = σ
    where
    ω : max x y ≡ x
    ω = ≤→max' ψ

    χ : distance x y ≡ x - y
    χ = ≤→distance≡LeftSubtractRight x y ψ

    π : (x + y) + (x - y) ≡ x + x
    π = (x + y) + (x - y)
          ≡⟨ (sym $ +Assoc x y (x - y)) ⟩
        x + (y + (x - y))
          ≡⟨ cong (_+_ x) (addLeftSubtractCancel y x) ⟩
        x + x ∎

    ρ : (x + y + distance x y) / 2 [ 2≠0 ] ≡ x
    ρ = (x + y + distance x y) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → (x + y + ?x) / 2 [ 2≠0 ]) χ ⟩
        (x + y + (x - y)) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) π ⟩
        (x + x) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) (self+≡2· x) ⟩
        (2 · x) / 2 [ 2≠0 ]
          ≡⟨ ·/' 2 x 2≠0 ⟩
        x ∎

    σ : max x y ≡ ((x + y + distance x y) / 2 [ 2≠0 ])
    σ = ω ∙ sym ρ

min≡midpoint-halfDistance :
  (x y : ℚ) →
  min x y ≡ ((x + y) - distance x y) / 2 [ 2≠0 ]
min≡midpoint-halfDistance x y =
  PropositionalTruncation.rec (isSetℚ _ _) φ (isTotal≤ x y)
  where
  φ : (x ≤ y) ⊎ (y ≤ x) →
      min x y ≡ (((x + y) - distance x y) / 2 [ 2≠0 ])
  φ (inl ψ) = σ
    where
    ω : min x y ≡ x
    ω = ≤→min x y ψ

    χ : distance x y ≡ y - x
    χ = ≤→distance≡RightSubtractLeft x y ψ

    π : (x + y) - (y - x) ≡ x + x
    π = (x + y) - (y - x)
          ≡⟨ (sym $ +Assoc x y (- (y - x))) ⟩
        x + (y - (y - x))
          ≡⟨ cong (_+_ x) (leftSubtractSubtractCancel y x) ⟩
        x + x ∎

    ρ : ((x + y) - distance x y) / 2 [ 2≠0 ] ≡ x
    ρ = ((x + y) - distance x y) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ((x + y) - ?x) / 2 [ 2≠0 ]) χ ⟩
        ((x + y) - (y - x)) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) π ⟩
        (x + x) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) (self+≡2· x) ⟩
        (2 · x) / 2 [ 2≠0 ]
          ≡⟨ ·/' 2 x 2≠0 ⟩
        x ∎

    σ : min x y ≡ ((x + y) - distance x y) / 2 [ 2≠0 ]
    σ = ω ∙ sym ρ
  φ (inr ψ) = σ
    where
    ω : min x y ≡ y
    ω = ≤→min' x y ψ

    χ : distance x y ≡ x - y
    χ = ≤→distance≡LeftSubtractRight x y ψ

    -- TODO: Replace
    π : (x + y) - (x - y) ≡ y + y
    π = (x + y) - (x - y)
          ≡⟨ cong (_+_ (x + y)) (negateSubtract x y) ⟩
        (x + y) + (- x + y)
          ≡⟨ +Assoc (x + y) (- x) y ⟩
        ((x + y) + - x) + y
          ≡⟨ cong (flip _+_ y) (addSubtractLeftCancel x y) ⟩
        y + y ∎

    ρ : ((x + y) - distance x y) / 2 [ 2≠0 ] ≡ y
    ρ = ((x + y) - distance x y) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ((x + y) - ?x) / 2 [ 2≠0 ]) χ ⟩
        ((x + y) - (x - y)) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) π ⟩
        (y + y) / 2 [ 2≠0 ]
          ≡⟨ cong (λ ?x → ?x / 2 [ 2≠0 ]) (self+≡2· y) ⟩
        (2 · y) / 2 [ 2≠0 ]
          ≡⟨ ·/' 2 y 2≠0 ⟩
        y ∎

    σ : min x y ≡ ((x + y) - distance x y) / 2 [ 2≠0 ]
    σ = ω ∙ sym ρ

maxNonexpandingˡ : 
  (q r s : ℚ.ℚ) → distance (max q s) (max r s) ≤ distance q r
maxNonexpandingˡ q r s = τ
  where
  -- TODO: Replace
  φ : (q + s + ∣ q - s ∣) - (r + s + ∣ r - s ∣) ≡
      (q - r) + (∣ q - s ∣ - ∣ r - s ∣)
  φ = (q + s + ∣ q - s ∣) - (r + s + ∣ r - s ∣)
         ≡⟨ cong (_+_ (q + s + ∣ q - s ∣)) (negateAdd (r + s) ∣ r - s ∣) ⟩
      (q + s + ∣ q - s ∣) + (- (r + s) + - ∣ r - s ∣)
         ≡⟨ cong (λ ?x → ((q + s + ∣ q - s ∣)+ (?x + - ∣ r - s ∣)))
                 (negateAdd r s) ⟩
      (q + s + ∣ q - s ∣) + (((- r) + (- s)) + - ∣ r - s ∣)
         ≡⟨ cong (λ ?x → ((q + s + ∣ q - s ∣) + (?x + - ∣ r - s ∣)))
                 (+Comm (- r) (- s)) ⟩
      ((q + s) + ∣ q - s ∣) + (((- s) + (- r)) + - ∣ r - s ∣)
         ≡⟨ cong (flip _+_ _) (+Comm (q + s) ∣ q - s ∣) ⟩
      (∣ q - s ∣ + (q + s)) + (((- s) + (- r)) + - ∣ r - s ∣)
         ≡⟨ (sym $ +Assoc ∣ q - s ∣ (q + s) _) ⟩
      ∣ q - s ∣ + ((q + s) + (((- s) + (- r)) + - ∣ r - s ∣))
         ≡⟨ cong (_+_ ∣ q - s ∣) (+Assoc (q + s) ((- s) + (- r)) _) ⟩
      ∣ q - s ∣ + (((q + s) + ((- s) + (- r))) + - ∣ r - s ∣)
         ≡⟨ cong (λ ?x → ∣ q - s ∣ + (?x + - ∣ r - s ∣))
                 (sym $ +Assoc q s ((- s) + (- r))) ⟩
      ∣ q - s ∣ + ((q + (s + ((- s) + (- r)))) + - ∣ r - s ∣)
         ≡⟨ cong (λ ?x → ∣ q - s ∣ + ((q + ?x) + - ∣ r - s ∣))
                 (+Assoc s (- s) (- r)) ⟩
      ∣ q - s ∣ + ((q + ((s + (- s)) + (- r))) + - ∣ r - s ∣)
         ≡⟨ cong (λ ?x → ∣ q - s ∣ + ((q + (?x + (- r))) + - ∣ r - s ∣))
                 (+InvR s) ⟩
      ∣ q - s ∣ + ((q + (0 + (- r))) + - ∣ r - s ∣)
         ≡⟨ cong (λ ?x → ∣ q - s ∣ + ((q + ?x) + - ∣ r - s ∣))
                 (+IdL (- r)) ⟩
      ∣ q - s ∣ + ((q + (- r)) + - ∣ r - s ∣)
         ≡⟨ addRightSwap ∣ q - s ∣ (q - r) (- ∣ r - s ∣) ⟩
      (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∎

  ψ : ∣ max q s - max r s ∣ ≡
      ∣ (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∣ / 2 [ 2≠0 ]
  ψ = ∣ max q s - max r s ∣
        ≡⟨ cong₂ distance (max≡midpoint+halfDistance q s)
                          (max≡midpoint+halfDistance r s) ⟩
      ∣ ((q + s + ∣ q - s ∣) / 2 [ 2≠0 ]) - ((r + s + ∣ r - s ∣) / 2 [ 2≠0 ]) ∣
        ≡⟨ cong (λ ?x → ∣ ((q + s + ∣ q - s ∣) / 2 [ 2≠0 ]) + ?x ∣)
                (-·≡-· ((r + s + ∣ r - s ∣)) (2 [ 2≠0 ]⁻¹)) ⟩
      ∣ ((q + s + ∣ q - s ∣) / 2 [ 2≠0 ]) +
        ((- (r + s + ∣ r - s ∣)) / 2 [ 2≠0 ]) ∣
        ≡⟨ cong ∣_∣ (sym $ ·DistR+ (q + s + ∣ q - s ∣) _ (2 [ 2≠0 ]⁻¹)) ⟩
      ∣ ((q + s + ∣ q - s ∣) - (r + s + ∣ r - s ∣)) / 2 [ 2≠0 ] ∣
        ≡⟨ magnitudeMultiply≡multiplyMagnitude
             ((q + s + ∣ q - s ∣) - (r + s + ∣ r - s ∣))
             (2 [ 2≠0 ]⁻¹) ⟩
      ∣ (q + s + ∣ q - s ∣) - (r + s + ∣ r - s ∣) ∣ · ∣ 2 [ 2≠0 ]⁻¹ ∣
        ≡⟨ cong (_·_ ∣ (q + s + ∣ q - s ∣) - (r + s + ∣ r - s ∣) ∣)
                (0≤→∣∣≡self (2 [ 2≠0 ]⁻¹) 0≤2⁻¹) ⟩
      ∣ (q + s + ∣ q - s ∣) - (r + s + ∣ r - s ∣) ∣ · 2 [ 2≠0 ]⁻¹
        ≡⟨ cong (λ ?x → ∣ ?x ∣ / 2 [ 2≠0 ]) φ ⟩
      ∣ (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∣ / 2 [ 2≠0 ] ∎

  ω : ∣ (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∣ ≤
      ∣ q - r ∣ + ∣ ∣ q - s ∣ - ∣ r - s ∣ ∣
  ω = magnitudeTriangleInequality (q - r) (∣ q - s ∣ - ∣ r - s ∣)

  χ : ∣ ∣ q - s ∣ - ∣ r - s ∣ ∣ ≤ ∣ (q - s) - (r - s) ∣
  χ = magnitudeReverseTriangleInequality (q - s) (r - s)

  -- TODO: Replace
  π : (q - s) - (r - s) ≡ q - r
  π = (q - s) - (r - s)
        ≡⟨ cong (_+_ (q - s)) (negateSubtract' r s) ⟩
      (q - s) + (s - r)
        ≡⟨ sym $ +Assoc q (- s) (s - r) ⟩
      q + ((- s) + (s - r))
        ≡⟨ cong (_+_ q) $ +Assoc (- s) s (- r) ⟩
      q + (((- s) + s) - r)
        ≡⟨ cong (λ ?x → q + (?x - r)) (+InvL s) ⟩
      q + (0 - r)
        ≡⟨ cong (_+_ q) (+IdL $ - r) ⟩
      q - r ∎

  χ' : ∣ ∣ q - s ∣ - ∣ r - s ∣ ∣ ≤ ∣ q - r ∣
  χ' = subst (_≤_ ∣ ∣ q - s ∣ - ∣ r - s ∣ ∣) (cong ∣_∣ π) χ

  ρ : ∣ (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∣ ≤ 
      ∣ q - r ∣ + ∣ q - r ∣
  ρ = isTrans≤
        ∣ (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∣
        (∣ q - r ∣ + ∣ ∣ q - s ∣ - ∣ r - s ∣ ∣)
        (∣ q - r ∣ + ∣ q - r ∣)
        ω (≤-o+ _ _ ∣ q - r ∣ χ')

  ρ' : ∣ (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∣ / 2 [ 2≠0 ] ≤
       (∣ q - r ∣ + ∣ q - r ∣) / 2 [ 2≠0 ]
  ρ' = ≤-·o ∣ (q - r) + (∣ q - s ∣ - ∣ r - s ∣) ∣
            (∣ q - r ∣ + ∣ q - r ∣)
            (2 [ 2≠0 ]⁻¹)
            0≤2⁻¹ ρ

  σ : (∣ q - r ∣ + ∣ q - r ∣) / 2 [ 2≠0 ] ≡ ∣ q - r ∣
  σ = self+self/2≡self ∣ q - r ∣ 2≠0

  τ : ∣ max q s - max r s ∣ ≤ ∣ q - r ∣
  τ = subst2 _≤_ (sym ψ) σ ρ'

maxNonexpandingʳ : 
  (q r s : ℚ.ℚ) → distance (max q r) (max q s) ≤ distance r s
maxNonexpandingʳ q r s =
  subst (flip _≤_ $ distance r s) φ (maxNonexpandingˡ r s q)
  where
  φ : distance (max r q) (max s q) ≡ distance (max q r) (max q s)
  φ = cong₂ distance (maxComm r q) (maxComm s q)

minNonexpandingˡ : 
  (q r s : ℚ.ℚ) → distance (min q s) (min r s) ≤ distance q r
minNonexpandingˡ q r s = τ
  where
  φ : ((q + s) - ∣ q - s ∣) + (- (r + s) + ∣ r - s ∣) ≡
      (q - r) + (∣ r - s ∣ - ∣ q - s ∣)
  φ = ((q + s) - ∣ q - s ∣) + (- (r + s) + ∣ r - s ∣)
        ≡⟨ +Assoc ((q + s) - ∣ q - s ∣) (- (r + s)) ∣ r - s ∣ ⟩
      (((q + s) - ∣ q - s ∣) + - (r + s)) + ∣ r - s ∣
        ≡⟨ cong (flip _+_ ∣ r - s ∣)
                (addLeftSwap (q + s) (- ∣ q - s ∣) (- (r + s))) ⟩
      (((q + s) - (r + s)) + - ∣ q - s ∣) + ∣ r - s ∣
        ≡⟨ cong (λ ?x → (?x - ∣ q - s ∣) + ∣ r - s ∣)
                (sym $ +Assoc q s (- (r + s))) ⟩
      ((q + (s - (r + s))) + - ∣ q - s ∣) + ∣ r - s ∣
        ≡⟨ cong (λ ?x → ((q + ?x) - ∣ q - s ∣) + ∣ r - s ∣)
                (leftSubtractAddCancel s r) ⟩
      ((q + - r) + - ∣ q - s ∣) + ∣ r - s ∣
        ≡⟨ ( sym $ +Assoc (q - r) (- ∣ q - s ∣) ∣ r - s ∣) ⟩
      (q - r) + (- ∣ q - s ∣ + ∣ r - s ∣)
        ≡⟨ cong (_+_ (q - r)) (+Comm (- ∣ q - s ∣) ∣ r - s ∣) ⟩
      (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∎

  ψ : ∣ min q s - min r s ∣ ≡
      ∣ (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∣ · 2 [ 2≠0 ]⁻¹
  ψ = ∣ min q s - min r s ∣
        ≡⟨ cong₂ distance (min≡midpoint-halfDistance q s)
                          (min≡midpoint-halfDistance r s) ⟩
      ∣ (((q + s) - ∣ q - s ∣) / 2 [ 2≠0 ]) -
        (((r + s) - ∣ r - s ∣) / 2 [ 2≠0 ]) ∣
        ≡⟨ cong (λ ?x → ∣ (((q + s) - ∣ q - s ∣) / 2 [ 2≠0 ]) + ?x ∣)
                (-·≡-· ((r + s) - ∣ r - s ∣) (2 [ 2≠0 ]⁻¹)) ⟩
      ∣ (((q + s) - ∣ q - s ∣) / 2 [ 2≠0 ]) +
        ((- ((r + s) - ∣ r - s ∣)) / 2 [ 2≠0 ]) ∣
        ≡⟨ cong (λ ?x → ∣ (((q + s) - ∣ q - s ∣) / 2 [ 2≠0 ]) +
                          (?x / 2 [ 2≠0 ]) ∣)
                (negateSubtract (r + s) ∣ r - s ∣) ⟩
      ∣ (((q + s) - ∣ q - s ∣) / 2 [ 2≠0 ]) +
        ((- (r + s) + ∣ r - s ∣) / 2 [ 2≠0 ]) ∣
        ≡⟨ cong ∣_∣ (sym $ ·DistR+ ((q + s) - ∣ q - s ∣)
                                   (- (r + s) + ∣ r - s ∣)
                                   (2 [ 2≠0 ]⁻¹)) ⟩
      ∣ (((q + s) - ∣ q - s ∣) + (- (r + s) + ∣ r - s ∣)) / 2 [ 2≠0 ] ∣
        ≡⟨ magnitudeMultiply≡multiplyMagnitude
             (((q + s) - ∣ q - s ∣) + (- (r + s) + ∣ r - s ∣))
             (2 [ 2≠0 ]⁻¹) ⟩
      ∣ ((q + s) - ∣ q - s ∣) + (- (r + s) + ∣ r - s ∣) ∣ · ∣ 2 [ 2≠0 ]⁻¹ ∣
        ≡⟨ cong (λ ?x → ∣ ((q + s) - ∣ q - s ∣) +
                          (- (r + s) + ∣ r - s ∣) ∣ · ?x)
                (≤→max' {x = 2 [ 2≠0 ]⁻¹} {y = - (2 [ 2≠0 ]⁻¹)} -2⁻¹≤2⁻¹) ⟩
      ∣ ((q + s) - ∣ q - s ∣) + (- (r + s) + ∣ r - s ∣) ∣ · 2 [ 2≠0 ]⁻¹
        ≡⟨ cong (λ ?x → ∣ ?x ∣ · 2 [ 2≠0 ]⁻¹) φ ⟩
      ∣ (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∣ · 2 [ 2≠0 ]⁻¹ ∎

  ω : ∣ (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∣ ≤
      ∣ q - r ∣ + ∣ ∣ r - s ∣ - ∣ q - s ∣ ∣
  ω = magnitudeTriangleInequality (q - r) (∣ r - s ∣ - ∣ q - s ∣)

  χ : ∣ ∣ r - s ∣ - ∣ q - s ∣ ∣ ≤ ∣ (r - s) - (q - s) ∣
  χ = magnitudeReverseTriangleInequality (r - s) (q - s)

  -- TODO: Remove
  π : (r - s) - (q - s) ≡ r - q
  π = (r - s) - (q - s)
        ≡⟨ cong (_+_ (r - s)) (negateSubtract q s) ⟩
      (r - s) + ((- q) + s)
        ≡⟨ (sym $ +Assoc r (- s) ((- q) + s)) ⟩
      r + ((- s) + ((- q) + s))
        ≡⟨ cong (_+_ r) (addRightSwap (- s) (- q) s) ⟩
      r + ((- q) + ((- s) + s))
        ≡⟨ cong (λ ?x → r + ((- q) + ?x)) (+InvL s) ⟩
      r + ((- q) + 0)
        ≡⟨ cong (_+_ r) (+IdR (- q)) ⟩
      r + (- q) ∎

  χ' : ∣ ∣ r - s ∣ - ∣ q - s ∣ ∣ ≤ ∣ q - r ∣
  χ' = subst (_≤_ ∣ ∣ r - s ∣ - ∣ q - s ∣ ∣)
             (cong ∣_∣ π ∙ distanceCommutative r q)
             χ

  ρ : ∣ (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∣ ≤ 
      ∣ q - r ∣ + ∣ q - r ∣
  ρ = isTrans≤ ∣ (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∣
               (∣ q - r ∣ + ∣ ∣ r - s ∣ - ∣ q - s ∣ ∣)
               (∣ q - r ∣ + ∣ q - r ∣)
               ω (≤-o+ (∣ ∣ r - s ∣ - ∣ q - s ∣ ∣) ∣ q - r ∣ ∣ q - r ∣ χ')

  ρ' : ∣ (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∣ / 2 [ 2≠0 ] ≤ 
       (∣ q - r ∣ + ∣ q - r ∣) / 2 [ 2≠0 ]
  ρ' = ≤-·o ∣ (q - r) + (∣ r - s ∣ - ∣ q - s ∣) ∣
            (∣ q - r ∣ + ∣ q - r ∣)
            (2 [ 2≠0 ]⁻¹)
            0≤2⁻¹ ρ

  σ : (∣ q - r ∣ + ∣ q - r ∣) / 2 [ 2≠0 ] ≡ ∣ q - r ∣
  σ = self+self/2≡self ∣ q - r ∣ 2≠0

  τ : ∣ min q s - min r s ∣ ≤ ∣ q - r ∣
  τ = subst2 _≤_ (sym ψ) σ ρ'

minNonexpandingʳ : 
  (q r s : ℚ.ℚ) → distance (min q r) (min q s) ≤ distance r s
minNonexpandingʳ q r s =
  subst (flip _≤_ $ distance r s) φ (minNonexpandingˡ r s q)
  where
  φ : distance (min r q) (min s q) ≡ distance (min q r) (min q s)
  φ = cong₂ distance (minComm r q) (minComm s q)

magntiude≡0→≡0 : {x : ℚ} → ∣ x ∣ ≡ 0 → x ≡ 0
magntiude≡0→≡0 {x} φ =
  PropositionalTruncation.rec (isSetℚ x 0) ψ (isTotal≤ x (- x))
  where
  ψ : (x ≤ - x) ⊎ (- x ≤ x) → x ≡ 0
  ψ (inl ω) = π'
    where
    χ : max x (- x) ≡ (- x)
    χ = ≤→max x (- x) ω

    π : - x ≡ 0
    π = sym χ ∙ φ

    π' : x ≡ 0
    π' = sym (-Invol x) ∙ cong -_ π
  ψ (inr ω) = π
    where
    χ : max x (- x) ≡ x
    χ = ≤→max' ω

    π : x ≡ 0
    π = sym χ ∙ φ

≤→≡⊎< : {x y : ℚ} → x ≤ y → (x ≡ y) ⊎ (x < y)
≤→≡⊎< {x} {y} φ with x ≟ y
... | lt ψ = inr ψ
... | eq ψ = inl ψ
... | gt ψ = Empty.rec (≤→≯ x y φ ψ)

distance≡0→≡ : {x y : ℚ} → distance x y ≡ 0 → x ≡ y
distance≡0→≡ {x} {y} φ = ψ'
  where
  ψ : x - y ≡ 0
  ψ = magntiude≡0→≡0 {x = x - y} φ

  ψ' : x ≡ y
  ψ' = -≡0→≡ ψ

∣∣<ε→∣∣≡0 : {x : ℚ} → ((ε : ℚ) → 0 < ε → ∣ x ∣ < ε) → ∣ x ∣ ≡ 0
∣∣<ε→∣∣≡0 {x} φ with ≤→≡⊎< {x = 0} {y = ∣ x ∣} (0≤∣∣ x)
... | inl ψ = sym ψ
... | inr ψ = Empty.rec (isIrrefl< ∣ x ∣ (φ ∣ x ∣ ψ))

distance<ε→≡ : {x y : ℚ} → ((ε : ℚ) → 0 < ε → distance x y < ε) → x ≡ y
distance<ε→≡ {x} {y} φ = ω
  where
  ψ : distance x y ≡ 0
  ψ = ∣∣<ε→∣∣≡0 {x = x - y} φ

  ω : x ≡ y
  ω = distance≡0→≡ ψ

-- Just the reverse triangle inequality!
magnitudeNonexpanding : (x y : ℚ) →
  distance ∣ x ∣ ∣ y ∣ ≤ distance x y
magnitudeNonexpanding = magnitudeReverseTriangleInequality

min+max≡+ : (x y : ℚ) → min x y + max x y ≡ x + y
min+max≡+ x y =
  PropositionalTruncation.rec
    (isSetℚ (min x y + max x y) (x + y))
    φ
    (isTotal≤ x y)
  where
  φ : (x ≤ y) ⊎ (y ≤ x) → min x y + max x y ≡ x + y
  φ (inl ψ) = π
    where
    ω : min x y ≡ x
    ω = ≤→min x y ψ

    χ : max x y ≡ y
    χ = ≤→max x y ψ

    π : min x y + max x y ≡ x + y
    π = cong₂ _+_ ω χ 
  φ (inr ψ) = π
    where
    ω : min x y ≡ y
    ω = ≤→min' x y ψ

    χ : max x y ≡ x
    χ = ≤→max' ψ

    π : min x y + max x y ≡ x + y
    π = cong₂ _+_ ω χ ∙ +Comm y x

negateMaxNegateNegate≡min : (x y : ℚ) → - max (- x) (- y) ≡ min x y
negateMaxNegateNegate≡min x y =
  isAntisym≤ (- max (- x) (- y)) (min x y) ω ρ'
  where
  φ : - x ≤ max (- x) (- y)
  φ = ≤max (- x) (- y)

  ψ : - y ≤ max (- x) (- y)
  ψ = ≤max' (- x) (- y)

  φ' : - max (- x) (- y) ≤ x
  φ' = subst (_≤_ $ - max (- x) (- y))
             (-Invol x)
             (≤antitone- {x = - x} {y = max (- x) (- y)} φ)

  ψ' : - max (- x) (- y) ≤ y
  ψ' = subst (_≤_ $ - max (- x) (- y))
             (-Invol y)
             (≤antitone- {x = - y} {y = max (- x) (- y)} ψ)

  ω : - max (- x) (- y) ≤ min x y
  ω = minGreatestLowerBound {x = x} {y = y} {z = - max (- x) (- y)} φ' ψ'

  χ : min x y ≤ x
  χ = min≤ x y

  π : min x y ≤ y
  π = min≤' x y

  χ' : - x ≤ - min x y
  χ' = ≤antitone- {x = min x y} {y = x} χ

  π' : - y ≤ - min x y
  π' = ≤antitone- {x = min x y} {y = y} π

  ρ : max (- x) (- y) ≤ - min x y
  ρ = maxLeastUpperBound {x = - x} {y = - y} {z = - min x y} χ' π'

  ρ' : min x y ≤ - max (- x) (- y)
  ρ' = subst (flip _≤_ $ - max (- x) (- y))
             (-Invol $ min x y)
             (≤antitone- {x = max (- x) (- y)} {y = - min x y} ρ)

negateMinNegateNegate≡max : (x y : ℚ) → - min (- x) (- y) ≡ max x y
negateMinNegateNegate≡max x y =
  ψ
  where
  φ : - max (- - x) (- - y) ≡ min (- x) (- y)
  φ = negateMaxNegateNegate≡min (- x) (- y)

  φ' : max (- - x) (- - y) ≡ - min (- x) (- y)
  φ' = sym (-Invol _) ∙ cong -_ φ

  ψ : - min (- x) (- y) ≡ max x y
  ψ = sym φ' ∙ cong₂ max (-Invol x) (-Invol y)
