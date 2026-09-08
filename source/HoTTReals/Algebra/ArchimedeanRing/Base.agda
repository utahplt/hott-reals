-- Vendored from LorenzoMolena/cubical algebraic-structures-wip ee4207d0,
-- Cubical/Algebra/ArchimedeanRing/Base.agda, on 2026-09-08. Edited: no.
module HoTTReals.Algebra.ArchimedeanRing.Base where
{-
  Definition of an archimedean ring.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Fast.Int
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Data.Nat        as ℕ   using (ℕ ; suc)
open import Cubical.Data.NatPlusOne as ℕ₊₁ using (ℕ₊₁ ; ℕ₊₁→ℕ)
open import Cubical.Data.Int        as ℤ   using (ℤ ; pos)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Binary.Order.StrictOrder

private
  variable
    ℓ ℓ' : Level

record IsArchimedeanRing
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ')
  (ι : ℤ → R) : Type (ℓ-max ℓ ℓ') where
  constructor isarchimedeanring
  field
    isOrderedCommRing   : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
    ·CancelR<           : ∀ x y z → 0r < z → (x · z) < (y · z) → x < y
    isMonomorphism      : IsOrderedCommRingMono (str ℤOrderedCommRing) ι
                            (orderedcommringstr _ _ _ _ _ _ _ isOrderedCommRing)
    archimedeanProperty : ∀ x y → 0r < y → ∃[ k ∈ ℤ ] x < (ι k · y)

  ι₀₊ : ℕ → R
  ι₀₊ = ι ∘ pos

  ι₊₁ : ℕ₊₁ → R
  ι₊₁ = ι ∘ pos ∘ ℕ₊₁→ℕ

  open IsOrderedCommRing isOrderedCommRing public
  open IsOrderedCommRingMono isMonomorphism public renaming (
      isOrderedCommRingHom to isOrderedCommRingHomι ; isCommRingHom to isCommRingHomι
    ; pres0 to ιpres0 ; pres1 to ιpres1 ; pres+ to ιpres+ ; pres· to ιpres·
    ; pres- to ιpres- ; pres≤ to ιpres≤ ; reflect< to ιreflect< ; pres< to ιpres<)
  ιreflect≤ = isOrderedCommRingMono→reflect≤ isMonomorphism

unquoteDecl IsArchimedeanRingIsoΣ = declareRecordIsoΣ IsArchimedeanRingIsoΣ (quote IsArchimedeanRing)

record ArchimedeanRingStr (ℓ' : Level) (R : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor archimedeanringstr
  field
    0r 1r : R
    _+_ _·_ : R → R → R
    -_ : R → R
    _<_ _≤_ : R → R → Type ℓ'
    ι : ℤ → R
    isArchimedeanRing : IsArchimedeanRing 0r 1r _+_ _·_ -_ _<_ _≤_ ι

  open IsArchimedeanRing isArchimedeanRing public

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

ArchimedeanRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanRing ℓ ℓ' = TypeWithStr ℓ (ArchimedeanRingStr ℓ')

ArchimedeanRing→OrderedCommRing : ArchimedeanRing ℓ ℓ' → OrderedCommRing ℓ ℓ'
ArchimedeanRing→OrderedCommRing R = _ , orderedcommringstr _ _ _ _ _ _ _ isOrderedCommRing
  where open ArchimedeanRingStr (str R)

isPropIsArchimedeanRing : {R : Type ℓ}
                        → (0r 1r : R)
                        → (_+_ _·_ : R → R → R) (-_ : R → R)
                        → (_<_ _≤_ : R → R → Type ℓ')
                        → (ι : ℤ → R)
                        → isProp (IsArchimedeanRing 0r 1r _+_ _·_ -_ _<_ _≤_ ι)
isPropIsArchimedeanRing 0r 1r _+_ _·_ -_ _<_ _≤_ ι = isOfHLevelRetractFromIso 1
  IsArchimedeanRingIsoΣ $
  isPropΣ (isPropIsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_) λ isOCR →
  isProp×2
    (isPropΠ5 λ x y _ _ _ → IsStrictOrder.is-prop-valued
      (IsOrderedCommRing.isStrictOrder isOCR) x y)
    (isPropIsOrderedCommRingMono
      (str ℤOrderedCommRing) ι (orderedcommringstr _ _ _ _ _ _ _ isOCR))
    (isPropΠ3 λ x y _ → squash₁)
