module HoTTReals.Data.Rationals.Properties where

open import Cubical.Algebra.Field.Base
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude

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
