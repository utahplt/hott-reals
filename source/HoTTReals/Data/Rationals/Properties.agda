module HoTTReals.Data.Rationals.Properties where

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field.Base
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ

2·≡self+ : (x : ℚ) → x + x ≡ 2 · x
2·≡self+ x =
  x + x
    ≡⟨ cong (λ ?x → ?x + ?x) (sym (·IdL x)) ⟩
  1 · x + 1 · x
    ≡⟨ sym (·DistR+ 1 1 x) ⟩
  2 · x ∎

+≡0→≡- : {x y : ℚ} → x + y ≡ 0 → x ≡ - y
+≡0→≡- {x} {y} p =
  x
    ≡⟨ sym (+IdR x) ⟩
  x + 0
    ≡⟨ cong (λ ?x → x + ?x) (sym (+InvR y)) ⟩
  x + (y + (- y))
    ≡⟨ +Assoc x y (- y) ⟩
  (x + y) + (- y)
    ≡⟨ cong (λ ?x → ?x + (- y)) p ⟩
  0 + (- y)
    ≡⟨ +IdL (- y) ⟩
  - y ∎

negateAdd : (x y : ℚ) → - (x + y) ≡ - x + - y
negateAdd x y = sym $ +≡0→≡- p
  where
  p = (- x + - y) + (x + y)
        ≡⟨ +Assoc (- x + - y) x y ⟩
      ((- x + - y) + x) + y
        ≡⟨ cong (flip _+_ y) (sym $ +Assoc (- x) (- y) x) ⟩
      (- x + (- y + x)) + y
        ≡⟨ cong (λ ?x → (- x + ?x) + y) (+Comm (- y) x) ⟩
      (- x + (x + - y)) + y
        ≡⟨ cong (flip _+_ y) (+Assoc (- x) x (- y)) ⟩
      ((- x + x) + - y) + y
        ≡⟨ cong (λ ?x → (?x + - y) + y) (+InvL x) ⟩
      (0 + - y) + y
        ≡⟨ cong (flip _+_ y) (+IdL (- y)) ⟩
      - y + y
        ≡⟨ +InvL y ⟩
      0 ∎

negateSubtract : (x y : ℚ) → - (x - y) ≡ - x + y
negateSubtract x y =
  - (x - y)
    ≡⟨ negateAdd x (- y) ⟩
  - x + (- - y)
    ≡⟨ cong (_+_ $ - x) (-Invol y) ⟩
  - x + y ∎

-·≡-· : (x y : ℚ) → - (x · y) ≡ (- x) · y
-·≡-· x y = sym (+≡0→≡- p)
  where
  p =
     ((- x) · y) + (x · y)
      ≡⟨ sym (·DistR+ (- x) x y) ⟩
    ((- x) + x) · y
      ≡⟨ cong (λ ?x → ?x · y) (+InvL x) ⟩
    0 · y
      ≡⟨ ·AnnihilL y ⟩
    0 ∎

-·≡·- : (x y : ℚ) → - (x · y) ≡ x · (- y)
-·≡·- x y =
          - (x · y)
            ≡⟨ cong -_ (·Comm x y) ⟩
          - (y · x)
            ≡⟨ -·≡-· y x ⟩
          (- y) · x
            ≡⟨ ·Comm (- y) x ⟩
          x · (- y) ∎

∣_∣ : ℚ → ℚ
∣ x ∣ = max x (- x)

-- TODO: Use some argument from cubical library instead
inverseUnique : {x y z : ℚ} → x · y ≡ 1 → x · z ≡ 1 → y ≡ z
inverseUnique {x} {y} {z} p q =
  y
    ≡⟨ sym (·IdR y) ⟩
  y · 1
    ≡⟨ cong (_·_ y) (sym q) ⟩
  y · (x · z)
    ≡⟨ ·Assoc y x z ⟩
  (y · x) · z
    ≡⟨ cong (flip _·_ z) (·Comm y x) ⟩
  (x · y) · z
    ≡⟨ cong (flip _·_ z) p ⟩
  1 · z
    ≡⟨ ·IdL z ⟩
  z ∎

-- TODO: Make a version which passes r for you, needs integral domain lemma
·⁻¹ : (x y : ℚ)
      (p : ¬ x ≡ 0) (q : ¬ y ≡ 0) (r : ¬ x · y ≡ 0) →
      (x · y) [ r ]⁻¹ ≡ (y [ q ]⁻¹) · (x [ p ]⁻¹)
·⁻¹ x y p q r =
  inverseUnique
    {x = x · y} {y = (x · y) [ r ]⁻¹} {z = (y [ q ]⁻¹) · (x [ p ]⁻¹)}
    s t
  where
  s : (x · y) · ((x · y) [ r ]⁻¹) ≡ 1
  s = ⁻¹-inverse (x · y) r

  t : (x · y) · ((y [ q ]⁻¹) · (x [ p ]⁻¹)) ≡ 1
  t = (x · y) · ((y [ q ]⁻¹) · (x [ p ]⁻¹))
          ≡⟨ ·Assoc (x · y) (y [ q ]⁻¹) (x [ p ]⁻¹) ⟩
        ((x · y) · (y [ q ]⁻¹)) · (x [ p ]⁻¹)
          ≡⟨ cong (flip _·_ (x [ p ]⁻¹)) (sym (·Assoc x y (y [ q ]⁻¹))) ⟩
        (x · (y · (y [ q ]⁻¹))) · (x [ p ]⁻¹)
          ≡⟨ cong (λ ?z → (x · ?z) · (x [ p ]⁻¹)) (⁻¹-inverse y q) ⟩
        (x · 1) · (x [ p ]⁻¹)
          ≡⟨ cong (flip _·_ (x [ p ]⁻¹)) (·IdR x) ⟩
        x · (x [ p ]⁻¹)
          ≡⟨ ⁻¹-inverse x p ⟩
        1 ∎

·⁻¹' : (x y : ℚ)
       (p : ¬ x ≡ 0) (q : ¬ y ≡ 0) (r : ¬ x · y ≡ 0) →
       (x · y) [ r ]⁻¹ ≡ (x [ p ]⁻¹) · (y [ q ]⁻¹)
·⁻¹' x y p q r =
  subst (λ ?x → (x · y) [ r ]⁻¹ ≡ ?x)
        (·Comm (y [ q ]⁻¹) (x [ p ]⁻¹))
        (·⁻¹ x y p q r)

·/ : (x y : ℚ) (p : ¬ y ≡ 0) → y · (x / y [ p ]) ≡ x
·/ x y p = y · (x / y [ p ])
             ≡⟨ cong (_·_ y) (·Comm x (y [ p ]⁻¹)) ⟩
           y · (y [ p ]⁻¹ · x)
             ≡⟨ ·Assoc y (y [ p ]⁻¹) x ⟩
           (y · y [ p ]⁻¹) · x
             ≡⟨ cong (flip _·_ x) (⁻¹-inverse y p) ⟩
           1 · x
             ≡⟨ ·IdL x ⟩
           x ∎

/· : (x y : ℚ) (p : ¬ y ≡ 0) → (x / y [ p ]) · y ≡ x
/· x y p = (x / y [ p ]) · y
             ≡⟨ ·Comm (x / y [ p ]) y ⟩
           y · (x / y [ p ])
             ≡⟨ ·/ x y p ⟩
           x ∎

·/' : (x y : ℚ) (p : ¬ x ≡ 0) → (x · y) / x [ p ] ≡ y
·/' x y p = (x · y) / x [ p ]
              ≡⟨ (sym $ ·Assoc x y (x [ p ]⁻¹)) ⟩
            x · (y · x [ p ]⁻¹)
              ≡⟨ cong (_·_ x) (·Comm y (x [ p ]⁻¹)) ⟩
            x · (x [ p ]⁻¹ · y)
              ≡⟨ ·Assoc x (x [ p ]⁻¹) y ⟩
            (x · x [ p ]⁻¹) · y
              ≡⟨ cong (flip _·_ y) (⁻¹-inverse x p) ⟩
            1 · y
              ≡⟨ ·IdL y ⟩
            y ∎

-- y · (x / y [ p ])
--              ≡⟨ ? ⟩ -- cong (_·_ y) (·Comm x (y [ p ]⁻¹))
--            y · (y [ p ]⁻¹ · x)
--              ≡⟨ ·Assoc y (y [ p ]⁻¹) x ⟩
--            (y · y [ p ]⁻¹) · x
--              ≡⟨ cong (flip _·_ x) (⁻¹-inverse y p) ⟩
--            1 · x
--              ≡⟨ ·IdL x ⟩
--            x ∎

