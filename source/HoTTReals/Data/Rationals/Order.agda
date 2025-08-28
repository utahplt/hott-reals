module HoTTReals.Data.Rationals.Order where

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Foundations.Prelude

+0< : {x y : ℚ} → 0 < x → 0 < y → 0 < x + y
+0< {x} {y} p q = isTrans≤< 0 (0 + 0) (x + y) (isRefl≤ 0) r
  where
  r : 0 + 0 < x + y
  r = <Monotone+ 0 x 0 y p q
