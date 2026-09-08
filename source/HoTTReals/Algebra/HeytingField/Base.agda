-- Vendored from LorenzoMolena/cubical algebraic-structures-wip ee4207d0,
-- Cubical/Algebra/HeytingField/Base.agda, on 2026-09-08. Edited: no.
module HoTTReals.Algebra.HeytingField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Order.Apartness.Base

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    R : Type ℓ

record IsHeytingField
  {R : Type ℓ}
  (0r 1r : R)
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_#_ : R → R → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isheytingfield
  field
    isCommRing  : IsCommRing 0r 1r _+_ _·_ -_
    isApartness : IsApartness _#_
    isTight     : ∀ x y → ¬ x # y → x ≡ y
    +Respect#R  : ∀ x y z → x # y → (x + z) # (y + z)
    #0→isInv    : ∀ x → x # 0r → Σ[ y ∈ R ] x · y ≡ 1r
    isInv→#0    : ∀ x y → x · y ≡ 1r → x # 0r

  open IsCommRing isCommRing public
  open IsApartness isApartness hiding (is-set) public

unquoteDecl IsHeytingFieldIsoΣ = declareRecordIsoΣ IsHeytingFieldIsoΣ (quote IsHeytingField)

record HeytingFieldStr (ℓ' : Level) (R : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor heytingfieldstr
  field
    0r 1r   : R
    _+_ _·_ : R → R → R
    -_      : R → R
    _#_     : R → R → Type ℓ'
    isHeytingField : IsHeytingField 0r 1r _+_ _·_ -_ _#_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix  4 _#_

  open IsHeytingField isHeytingField public

HeytingField : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
HeytingField ℓ ℓ' = TypeWithStr ℓ (HeytingFieldStr ℓ')

HeytingFieldStr→CommRingStr : HeytingFieldStr ℓ' R → CommRingStr R
HeytingFieldStr→CommRingStr (heytingfieldstr _ _ _ _ _ _ H) =
  commringstr _ _ _ _ _ (IsHeytingField.isCommRing H)

HeytingFieldStr→RingStr : HeytingFieldStr ℓ' R → RingStr R
HeytingFieldStr→RingStr R = CommRingStr→RingStr (HeytingFieldStr→CommRingStr R)

HeytingField→CommRing : HeytingField ℓ ℓ' → CommRing ℓ
HeytingField→CommRing (R , H) = R , HeytingFieldStr→CommRingStr H

HeytingField→Ring : HeytingField ℓ ℓ' → Ring ℓ
HeytingField→Ring R = CommRing→Ring (HeytingField→CommRing R)

HeytingFieldStr→ApartnessStr : HeytingFieldStr ℓ' R → ApartnessStr ℓ' R
HeytingFieldStr→ApartnessStr (heytingfieldstr _ _ _ _ _ _ H) =
  apartnessstr _ (IsHeytingField.isApartness H)

HeytingField→Apartness : HeytingField ℓ ℓ' → Apartness ℓ ℓ'
HeytingField→Apartness (R , H) = R , HeytingFieldStr→ApartnessStr H

isPropIsHeytingField : (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) (_#_ : R → R → Type ℓ')
                     → isProp (IsHeytingField 0r 1r _+_ _·_ -_ _#_)
isPropIsHeytingField _ _ _ _ _ _ = isOfHLevelRetractFromIso 1 IsHeytingFieldIsoΣ $
  isPropΣ (isPropIsCommRing _ _ _ _ _) λ isCommRing →
  isPropΣ (isPropIsApartness _) λ isApartness →
  isProp×3
    (isPropΠ3 λ _ _ _ → isCommRing .is-set _ _)
    (isPropΠ4 λ _ _ _ _ → isApartness .is-prop-valued _ _)
    (isPropΠ2 λ _ _ → Units.inverseUniqueness (_ , commringstr _ _ _ _ _ isCommRing) _)
    (isPropΠ3 λ _ _ _ → isApartness .is-prop-valued _ _)
  where open IsApartness; open IsCommRing

record IsHeytingFieldHom
  {A : Type ℓ} {B : Type ℓ'}
  (R : HeytingFieldStr ℓ'' A) (f : A → B) (S : HeytingFieldStr ℓ''' B)
  : Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ''')) where
  no-eta-equality
  private
    module R = HeytingFieldStr R
    module S = HeytingFieldStr S

  field
    pres0 : f R.0r ≡ S.0r
    pres1 : f R.1r ≡ S.1r
    pres+ : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres· : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres- : (x : A) → f (R.- x) ≡ S.- (f x)
    pres# : (x y : A) → (x R.# y) ≃ (f x S.# f y) -- This is actually redundant

unquoteDecl IsHeytingFieldHomIsoΣ = declareRecordIsoΣ IsHeytingFieldHomIsoΣ (quote IsHeytingFieldHom)

isPropIsHeytingFieldHom : {A : Type ℓ} {B : Type ℓ'}
                        → (R : HeytingFieldStr ℓ'' A)
                        → (f : A → B)
                        → (S : HeytingFieldStr ℓ''' B)
                        → isProp (IsHeytingFieldHom R f S)
isPropIsHeytingFieldHom R f S = isOfHLevelRetractFromIso 1 IsHeytingFieldHomIsoΣ $
  isProp×5
    (is-set _ _)
    (is-set _ _)
    (isPropΠ2 λ _ _ → is-set _ _)
    (isPropΠ2 λ _ _ → is-set _ _)
    (isPropΠ  λ _   → is-set _ _)
    (isPropΠ2 λ _ _ → isOfHLevel⁺≃ᵣ 0 (is-prop-valued _ _))
  where open HeytingFieldStr S

isHeytingFieldHom→isRingHom : {A : Type ℓ} {B : Type ℓ'}
                            → (R : HeytingFieldStr ℓ'' A)
                            → (f : A → B)
                            → (S : HeytingFieldStr ℓ''' B)
                            → IsHeytingFieldHom R f S
                            → IsRingHom (HeytingFieldStr→RingStr R) f  (HeytingFieldStr→RingStr S)
isHeytingFieldHom→isRingHom R f S fIsHom = isRingHomf where
  module f = IsHeytingFieldHom fIsHom
  open IsRingHom

  isRingHomf : IsRingHom _ f _
  isRingHomf .pres0 = f.pres0
  isRingHomf .pres1 = f.pres1
  isRingHomf .pres+ = f.pres+
  isRingHomf .pres· = f.pres·
  isRingHomf .pres- = f.pres-

HeytingFieldHom : (R : HeytingField ℓ ℓ'') (S : HeytingField ℓ' ℓ''') → Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
HeytingFieldHom (A , R) (B , S) = Σ[ f ∈ (A → B) ] IsHeytingFieldHom R f S

isSetHeytingFieldHom : (R : HeytingField ℓ ℓ'') (S : HeytingField ℓ' ℓ''') → isSet (HeytingFieldHom R S)
isSetHeytingFieldHom R S = isSetΣSndProp (isSet→ is-set) λ f → isPropIsHeytingFieldHom _ f _
  where open HeytingFieldStr (str S)

HeytingFieldHom→RingHom : (R : HeytingField ℓ ℓ'') (S : HeytingField ℓ' ℓ''')
                        → HeytingFieldHom R S
                        → RingHom (HeytingField→Ring R) (HeytingField→Ring S)
HeytingFieldHom→RingHom R S (f , fIsHom) = f , isHeytingFieldHom→isRingHom _ f _ fIsHom

IsHeytingFieldEquiv : {A : Type ℓ} {B : Type ℓ'}
                    → (R : HeytingFieldStr ℓ'' A) (e : A ≃ B) (S : HeytingFieldStr ℓ''' B)
                    → Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
IsHeytingFieldEquiv R e S = IsHeytingFieldHom R (e .fst) S

HeytingFieldEquiv : (R : HeytingField ℓ ℓ'') (S : HeytingField ℓ' ℓ''') → Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
HeytingFieldEquiv (A , R) (B , S) = Σ[ e ∈ A ≃ B ] IsHeytingFieldEquiv R e S

isSetHeytingFieldEquiv : (R : HeytingField ℓ ℓ'') (S : HeytingField ℓ' ℓ''') → isSet (HeytingFieldEquiv R S)
isSetHeytingFieldEquiv R S =
  isSetΣSndProp (isOfHLevel⁺≃ᵣ 1 is-set) λ (f , _) → isPropIsHeytingFieldHom _ f _
  where open HeytingFieldStr (str S)

HeytingFieldEquiv→RingEquiv : (R : HeytingField ℓ ℓ'') (S : HeytingField ℓ' ℓ''')
                            → HeytingFieldEquiv R S
                            → RingEquiv (HeytingField→Ring R) (HeytingField→Ring S)
HeytingFieldEquiv→RingEquiv R S (e , eIsHom) = e , isHeytingFieldHom→isRingHom _ _ _ eIsHom

𝒮ᴰ-HeytingField : DUARel (𝒮-Univ ℓ) (HeytingFieldStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-HeytingField =
  𝒮ᴰ-Record (𝒮-Univ _) IsHeytingFieldEquiv (fields:
    data[ 0r ∣ null ∣ pres0 ]
    data[ 1r ∣ null ∣ pres1 ]
    data[ _+_ ∣ bin ∣ pres+ ]
    data[ _·_ ∣ bin ∣ pres· ]
    data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
    data[ _#_ ∣ autoDUARel _ _ ∣ pres# ]
    prop[ isHeytingField ∣ (λ _ _ → isPropIsHeytingField _ _ _ _ _ _) ]
  )
  where
    open HeytingFieldStr
    open IsHeytingFieldHom

    null = autoDUARel (𝒮-Univ _) λ A → A
    bin = autoDUARel (𝒮-Univ _) λ A → A → A → A

HeytingFieldPath : (R S : HeytingField ℓ ℓ') → HeytingFieldEquiv R S ≃ (R ≡ S)
HeytingFieldPath = ∫ 𝒮ᴰ-HeytingField .UARel.ua

uaHeytingField : {R S : HeytingField ℓ ℓ'} → HeytingFieldEquiv R S → R ≡ S
uaHeytingField = HeytingFieldPath _ _ .fst

isGroupoidHeytingField : isGroupoid (HeytingField ℓ ℓ')
isGroupoidHeytingField _ _ = isOfHLevelRespectEquiv 2 (HeytingFieldPath _ _) (isSetHeytingFieldEquiv _ _)
