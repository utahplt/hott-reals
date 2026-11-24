{-
  This is the preferred version of the Reals in the library, defined as the HIIT
  Cauchy-completion of the rationals
-}
module HoTTReals.Relation.Premetric.Instances.Reals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos ; neg ; negsuc)
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Positive

open import Cubical.Relation.Premetric.Instances.Rationals as ℚ

open import HoTTReals.Relation.Premetric.Completion.Base ℚPrSpace public renaming (
  ℭ to ℝ ; ι to rat ; eqℭ to eqℝ ; ι-ι to rat-rat ; ι-lim to rat-lim ; lim-ι to lim-rat)
open import HoTTReals.Relation.Premetric.Completion.Properties _ ℚPrSpace
  public renaming (
    isSetℭ to isSetℝ ; ℭPremetricSpace to ℝPremetricSpace ; isCompleteℭ to isCompleteℝ
  ; isInjectiveι to isInjectiveRat ; isEmbeddingι to isEmbeddingRat
  ; ιᴵ to ratᴵ ; ιⁿ to ratⁿ ; ιᶜ to ratᶜ ; ιᵘᶜ to ratᵘᶜ ; ιᴸ to ratᴸ)

pattern Δrat< p = rat-rat (ℚ.pos<pos p)

-- Natural number and negative integer literals for ℝ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℝ : HasFromNat ℝ
  fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → rat [ pos n / 1 ] }

instance
  fromNegℝ : HasFromNeg ℝ
  fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → rat [ neg n / 1 ] }

private
  _ : -12297292 ∼[ 2178271827 ] -12296294
  _ = Δrat< tt
