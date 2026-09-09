module HoTTReals.Algebra.CommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos ; negsuc)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_] ; eq/ ; ℕ₊₁→ℤ)
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SQ using ([_])

private
  variable
    ℓ : Level

ℤ→ℚ+ : (m n : ℤ) → [ m ℤ.+ n / 1 ] ≡ [ m / 1 ] ℚ.+ [ n / 1 ]
ℤ→ℚ+ m n =
  eq/ _ _ $
    (m ℤ.+ n) ℤ.· 1
      ≡⟨ ℤ.·IdR (m ℤ.+ n) ⟩
    m ℤ.+ n
      ≡⟨ cong₂ ℤ._+_ (sym $ ℤ.·IdR m) (sym $ ℤ.·IdR n) ⟩
    m ℤ.· 1 ℤ.+ n ℤ.· 1
      ≡⟨ sym $ ℤ.·IdR (m ℤ.· 1 ℤ.+ n ℤ.· 1) ⟩
    (m ℤ.· 1 ℤ.+ n ℤ.· 1) ℤ.· 1 ∎

ℤ→ℚ- : (n : ℤ) → [ ℤ.- n / 1 ] ≡ ℚ.- [ n / 1 ]
ℤ→ℚ- n =
  eq/ _ _ $
    (ℤ.- n) ℤ.· 1
      ≡⟨ ℤ.·IdR (ℤ.- n) ⟩
    ℤ.- n
      ≡⟨ cong ℤ.-_ (sym $ ℤ.·IdL n) ⟩
    ℤ.- (1 ℤ.· n)
      ≡⟨ sym $ ℤ.negsuc·ℤ 0 n ⟩
    negsuc 0 ℤ.· n
      ≡⟨ sym $ ℤ.·IdR (negsuc 0 ℤ.· n) ⟩
    (negsuc 0 ℤ.· n) ℤ.· 1 ∎

module _ (R : CommRing ℓ) (f g : CommRingHom ℚCommRing R) where
  open CommRingStr (snd R)

  private
    module f = IsCommRingHom (snd f)
    module g = IsCommRingHom (snd g)
    F = fst f
    G = fst g

    pos≡ : (k : ℕ) → F [ pos k / 1 ] ≡ G [ pos k / 1 ]
    pos≡ zero = f.pres0 ∙ sym g.pres0
    pos≡ (suc k) =
      F [ pos (suc k) / 1 ]
        ≡⟨ cong F (ℤ→ℚ+ 1 (pos k)) ⟩
      F (1 ℚ.+ [ pos k / 1 ])
        ≡⟨ f.pres+ 1 [ pos k / 1 ] ⟩
      F 1 + F [ pos k / 1 ]
        ≡⟨ cong₂ _+_ (f.pres1 ∙ sym g.pres1) (pos≡ k) ⟩
      G 1 + G [ pos k / 1 ]
        ≡⟨ sym $ g.pres+ 1 [ pos k / 1 ] ⟩
      G (1 ℚ.+ [ pos k / 1 ])
        ≡⟨ cong G (sym $ ℤ→ℚ+ 1 (pos k)) ⟩
      G [ pos (suc k) / 1 ] ∎
    ℤ≡ : (n : ℤ) → F [ n / 1 ] ≡ G [ n / 1 ]
    ℤ≡ (pos k) = pos≡ k
    ℤ≡ (negsuc k) =
      F [ negsuc k / 1 ]
        ≡⟨ cong F (ℤ→ℚ- (pos (suc k))) ⟩
      F (ℚ.- [ pos (suc k) / 1 ])
        ≡⟨ f.pres- [ pos (suc k) / 1 ] ⟩
      - F [ pos (suc k) / 1 ]
        ≡⟨ cong -_ (pos≡ (suc k)) ⟩
      - G [ pos (suc k) / 1 ]
        ≡⟨ sym $ g.pres- [ pos (suc k) / 1 ] ⟩
      G (ℚ.- [ pos (suc k) / 1 ])
        ≡⟨ cong G (sym $ ℤ→ℚ- (pos (suc k))) ⟩
      G [ negsuc k / 1 ] ∎

    ℚ≡ : (q : ℚ) → F q ≡ G q
    ℚ≡ = SQ.elimProp (λ q → is-set (F q) (G q)) onFrac
      where
      onFrac : (u : ℤ × ℕ₊₁) → F SQ.[ u ] ≡ G SQ.[ u ]
      onFrac (a , b) =
        F [ a / b ]
          ≡⟨ sym $ ·IdR (F [ a / b ]) ⟩
        F [ a / b ] · 1r
          ≡⟨ cong (F [ a / b ] ·_) (sym unit) ⟩
        F [ a / b ] · (F [ ℕ₊₁→ℤ b / 1 ] · F [ 1 / b ])
          ≡⟨ ·Assoc _ _ _ ⟩
        (F [ a / b ] · F [ ℕ₊₁→ℤ b / 1 ]) · F [ 1 / b ]
          ≡⟨ cong (_· F [ 1 / b ]) (sym $ f.pres· [ a / b ] [ ℕ₊₁→ℤ b / 1 ]) ⟩
        F ([ a / b ] ℚ.· [ ℕ₊₁→ℤ b / 1 ]) · F [ 1 / b ]
          ≡⟨ cong (λ q → F q · F [ 1 / b ]) cancel ⟩
        F [ a / 1 ] · F [ 1 / b ]
          ≡⟨ cong (_· F [ 1 / b ]) (ℤ≡ a) ⟩
        G [ a / 1 ] · F [ 1 / b ]
          ≡⟨ cong (λ q → G q · F [ 1 / b ]) (sym cancel) ⟩
        G ([ a / b ] ℚ.· [ ℕ₊₁→ℤ b / 1 ]) · F [ 1 / b ]
          ≡⟨ cong (_· F [ 1 / b ]) (g.pres· [ a / b ] [ ℕ₊₁→ℤ b / 1 ]) ⟩
        (G [ a / b ] · G [ ℕ₊₁→ℤ b / 1 ]) · F [ 1 / b ]
          ≡⟨ cong (λ y → (G [ a / b ] · y) · F [ 1 / b ]) (sym $ ℤ≡ (ℕ₊₁→ℤ b)) ⟩
        (G [ a / b ] · F [ ℕ₊₁→ℤ b / 1 ]) · F [ 1 / b ]
          ≡⟨ sym $ ·Assoc _ _ _ ⟩
        G [ a / b ] · (F [ ℕ₊₁→ℤ b / 1 ] · F [ 1 / b ])
          ≡⟨ cong (G [ a / b ] ·_) unit ⟩
        G [ a / b ] · 1r
          ≡⟨ ·IdR (G [ a / b ]) ⟩
        G [ a / b ] ∎
        where
        cancel : [ a / b ] ℚ.· [ ℕ₊₁→ℤ b / 1 ] ≡ [ a / 1 ]
        cancel =
          cong (λ d → [ a ℤ.· ℕ₊₁→ℤ b / d ]) (·₊₁-comm b 1) ∙ ℚ.·CancelR b

        cancel' : [ ℕ₊₁→ℤ b / 1 ] ℚ.· [ 1 / b ] ≡ 1
        cancel' =
          cong (λ d → [ ℕ₊₁→ℤ b ℤ.· 1 / d ]) (·₊₁-comm 1 b) ∙ ℚ.·CancelL b

        unit : F [ ℕ₊₁→ℤ b / 1 ] · F [ 1 / b ] ≡ 1r
        unit =
          sym (f.pres· [ ℕ₊₁→ℤ b / 1 ] [ 1 / b ]) ∙ cong F cancel' ∙ f.pres1

  CommRingHomℚ≡ : f ≡ g
  CommRingHomℚ≡ = CommRingHom≡ (funExt ℚ≡)

isPropCommRingHomℚ : (R : CommRing ℓ) → isProp (CommRingHom ℚCommRing R)
isPropCommRingHomℚ R = CommRingHomℚ≡ R
