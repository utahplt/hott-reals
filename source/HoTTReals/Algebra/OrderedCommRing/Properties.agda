module HoTTReals.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base
import Cubical.Algebra.OrderedCommRing.Properties as
  CubicalOrderedCommRingProperties
open import Cubical.Algebra.Ring

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level

module _ (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    RCR = OrderedCommRing→CommRing R'
  open OrderedCommRingStr (snd R')

  module OrderedCommRingTheory where
    open CubicalOrderedCommRingProperties.OrderedCommRingTheory R' using
      ( abs ; 0≤abs ; ²∘abs≡² ; ·MonoL≤ ; ¬<→≥)
    open RingTheory (CommRing→Ring RCR) using (0LeftAnnihilates)

    0≤· : {x y : R} → 0r ≤ x → 0r ≤ y → 0r ≤ x · y
    0≤· {x} {y} 0≤x 0≤y =
      subst (_≤ x · y) (0LeftAnnihilates y) (·MonoR≤ 0r x y 0≤y 0≤x)

    0≤→<→²<² : {x y : R} → 0r ≤ x → x < y → x · x < y · y
    0≤→<→²<² {x} {y} 0≤x x<y =
      ≤-<-trans (x · x) (x · y) (y · y)
        ( ·MonoL≤ x y x 0≤x $ <-≤-weaken x y x<y)
        ( ·MonoR< x y y (≤-<-trans 0r x y 0≤x x<y) x<y)

    0≤→0≤→²≡²→≡ : {x y : R} → 0r ≤ x → 0r ≤ y → x · x ≡ y · y → x ≡ y
    0≤→0≤→²≡²→≡ {x} {y} 0≤x 0≤y x²≡y² =
      is-antisym x y
        ( ¬<→≥ y x $ λ y<x →
          is-irrefl (y · y) $ subst (y · y <_) x²≡y² (0≤→<→²<² 0≤y y<x))
        ( ¬<→≥ x y $ λ x<y →
          is-irrefl (x · x) $
            subst (x · x <_) (sym x²≡y²) (0≤→<→²<² 0≤x x<y))

    abs· : (x y : R) → abs (x · y) ≡ abs x · abs y
    abs· x y =
      0≤→0≤→²≡²→≡ (0≤abs $ x · y) (0≤· (0≤abs x) (0≤abs y)) squares
      where
      squares :
        abs (x · y) · abs (x · y) ≡ (abs x · abs y) · (abs x · abs y)
      squares =
        abs (x · y) · abs (x · y)
          ≡⟨ ²∘abs≡² (x · y) ⟩
        (x · y) · (x · y)
          ≡⟨ solve! RCR ⟩
        (x · x) · (y · y)
          ≡⟨ cong₂ _·_ (sym $ ²∘abs≡² x) (sym $ ²∘abs≡² y) ⟩
        (abs x · abs x) · (abs y · abs y)
          ≡⟨ solve! RCR ⟩
        (abs x · abs y) · (abs x · abs y) ∎
