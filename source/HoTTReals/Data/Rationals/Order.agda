module HoTTReals.Data.Rationals.Order where

open import Cubical.Data.Int.Base as ℤ using (ℤ)
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Int.Properties as ℤ using ()
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary

+0< : {x y : ℚ} → 0 < x → 0 < y → 0 < x + y
+0< {x} {y} p q = r
  -- Don't need `subst` because the path is refl
  where
  r : 0 + 0 < x + y
  r = <Monotone+ 0 x 0 y p q

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
