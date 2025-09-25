module HoTTReals.Data.Rationals.Properties where

open import Cubical.Algebra.Field.Base
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

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
