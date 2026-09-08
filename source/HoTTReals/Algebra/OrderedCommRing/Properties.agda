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
    0≤· {x} {y} 0≤x 0≤y = {!!}

    0≤→<→²<² : {x y : R} → 0r ≤ x → x < y → x · x < y · y
    0≤→<→²<² {x} {y} 0≤x x<y = {!!}

    0≤→0≤→²≡²→≡ : {x y : R} → 0r ≤ x → 0r ≤ y → x · x ≡ y · y → x ≡ y
    0≤→0≤→²≡²→≡ {x} {y} 0≤x 0≤y x²≡y² = {!!}

    abs· : (x y : R) → abs (x · y) ≡ abs x · abs y
    abs· x y = {!!}
