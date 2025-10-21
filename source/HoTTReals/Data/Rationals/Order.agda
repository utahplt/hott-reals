module HoTTReals.Data.Rationals.Order where

open import Cubical.Data.Empty as Empty using (rec)
open import Cubical.Data.Int.Base as ℤ using (ℤ)
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Int.Properties as ℤ using ()
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic
open import HoTTReals.Data.Rationals.Properties

+0< : {x y : ℚ} → 0 < x → 0 < y → 0 < x + y
+0< {x} {y} p q = r
 -- Don't need `subst` because the path is refl
  where
  r : 0 + 0 < x + y
  r = <Monotone+ 0 x 0 y p q

·0< : {x y : ℚ} → 0 < x → 0 < y → 0 < x · y
·0< {x} {y} p q = subst (λ ?x → ?x < x · y) (·AnnihilL y) r
  where
  r : 0 · y < x · y
  r = <-·o 0 x y q p

-- TODO: Rename to -Dist≤
≤antitone- : {x y : ℚ} → x ≤ y → - y ≤ - x
≤antitone- {x} {y} = elimProp2 {P = λ x y → x ≤ y → (- y) ≤ (- x)} p q x y
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
<antitone- {x} {y} = elimProp2 {P = λ x y → x < y → - y < - x} p q x y 
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
  elimProp {P = λ x → (p : 0 < x) → 0 < x [ ≠-symmetric (<→≠ p) ]⁻¹}
           (λ x → isPropΠ (λ p → isProp< 0 (x [ ≠-symmetric (<→≠ p) ]⁻¹)))
           q
           x
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
  t = ·0< {x = x} {y = y} p (isTrans<≤ 0 x y p q)

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
  t = ·0< {x = x} {y = y} p ((isTrans< 0 x y p q))

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

-- absLessThan→absLessThan₁ : (x y ε : ℚ) → ∣ x ∣ < ε → x < ε
-- absLessThan→absLessThan₁ x y ε p = ?

-- absLessThan→absLessThan₂ : (x y ε : ℚ) → ∣ x ∣ < ε → - ε < x
-- absLessThan→absLessThan₂ x y ε p = ?
