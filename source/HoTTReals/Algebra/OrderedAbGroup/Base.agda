module HoTTReals.Algebra.OrderedAbGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.OrderedCommMonoid.Base
open import Cubical.Algebra.OrderedCommRing.Base

import Cubical.Functions.Logic as L

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset hiding
  ( isPseudolattice ; isPropIsPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Nullary

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

record IsOrderedAbGroup
  {G : Type ℓ}
  (0g : G)
  (_+_ : G → G → G)
  (-_ : G → G)
  (_<_ _≤_ : G → G → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isorderedabgroup
  field
    isAbGroup : IsAbGroup 0g _+_ -_
    isPseudolattice : IsPseudolattice _≤_
    isStrictOrder : IsStrictOrder _<_
    <-≤-weaken : (x y : G) → x < y → x ≤ y
    ≤≃¬> : (x y : G) → (x ≤ y) ≃ (¬ (y < x))
    <-≤-trans : (x y z : G) → x < y → y ≤ z → x < z
    ≤-<-trans : (x y z : G) → x ≤ y → y < z → x < z
    +MonoR≤ : (x y z : G) → x ≤ y → (x + z) ≤ (y + z)
    +MonoR< : (x y z : G) → x < y → (x + z) < (y + z)
    posSum→pos∨pos : (x y : G) → 0g < (x + y) → (0g < x) L.⊔′ (0g < y)

  open IsAbGroup isAbGroup public
  open IsPseudolattice isPseudolattice hiding (is-set) renaming
    ( is-prop-valued to is-prop-valued≤ ; is-trans to is-trans≤ ;
      isPseudolattice to is-pseudolattice ; _∧l_ to _⊓_ ; _∨l_ to _⊔_)
    public
  open IsStrictOrder isStrictOrder hiding (is-set) renaming
    ( is-prop-valued to is-prop-valued< ; is-trans to is-trans<)
    public

unquoteDecl IsOrderedAbGroupIsoΣ =
  declareRecordIsoΣ IsOrderedAbGroupIsoΣ (quote IsOrderedAbGroup)

record OrderedAbGroupStr (ℓ' : Level) (G : Type ℓ) :
  Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedabgroupstr
  field
    0g : G
    _+_ : G → G → G
    -_ : G → G
    _<_ _≤_ : G → G → Type ℓ'
    isOrderedAbGroup : IsOrderedAbGroup 0g _+_ -_ _<_ _≤_

  open IsOrderedAbGroup isOrderedAbGroup public

  infix 8 -_
  infixl 6 _+_
  infix 4 _<_ _≤_

OrderedAbGroup : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedAbGroup ℓ ℓ' = TypeWithStr ℓ (OrderedAbGroupStr ℓ')

module _
  {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
  {_<_ _≤_ : G → G → Type ℓ'}
  (is-setG : isSet G)
  (+Assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
  (+IdR : (x : G) → x + 0g ≡ x)
  (+InvR : (x : G) → x + (- x) ≡ 0g)
  (+Comm : (x y : G) → x + y ≡ y + x)
  (is-prop-valued≤ : isPropValued _≤_)
  (is-refl : isRefl _≤_)
  (is-trans≤ : isTrans _≤_)
  (is-antisym : isAntisym _≤_)
  (is-meet-semipseudolattice :
    isMeetSemipseudolattice
      ( poset G _≤_
        ( isposet is-setG is-prop-valued≤ is-refl is-trans≤ is-antisym)))
  (is-join-semipseudolattice :
    isJoinSemipseudolattice
      ( poset G _≤_
        ( isposet is-setG is-prop-valued≤ is-refl is-trans≤ is-antisym)))
  (is-prop-valued : isPropValued _<_)
  (is-irrefl : isIrrefl _<_)
  (is-trans : isTrans _<_)
  (is-asym : isAsym _<_)
  (is-weakly-linear : isWeaklyLinear _<_)
  (<-≤-weaken : (x y : G) → x < y → x ≤ y)
  (≤≃¬> : (x y : G) → (x ≤ y) ≃ (¬ (y < x)))
  (<-≤-trans : (x y z : G) → x < y → y ≤ z → x < z)
  (≤-<-trans : (x y z : G) → x ≤ y → y < z → x < z)
  (+MonoR≤ : (x y z : G) → x ≤ y → (x + z) ≤ (y + z))
  (+MonoR< : (x y z : G) → x < y → (x + z) < (y + z))
  (posSum→pos∨pos : (x y : G) → 0g < (x + y) → (0g < x) L.⊔′ (0g < y))
  where
  makeIsOrderedAbGroup : IsOrderedAbGroup 0g _+_ -_ _<_ _≤_
  makeIsOrderedAbGroup = OAG
    where
    OAG : IsOrderedAbGroup 0g _+_ -_ _<_ _≤_
    IsOrderedAbGroup.isAbGroup OAG =
      makeIsAbGroup is-setG +Assoc +IdR +InvR +Comm
    IsOrderedAbGroup.isPseudolattice OAG =
      makeIsPseudolattice
        ( is-setG)
        ( is-prop-valued≤)
        ( is-refl)
        ( is-trans≤)
        ( is-antisym)
        ( is-meet-semipseudolattice)
        ( is-join-semipseudolattice)
    IsOrderedAbGroup.isStrictOrder OAG =
      isstrictorder
        ( is-setG)
        ( is-prop-valued)
        ( is-irrefl)
        ( is-trans)
        ( is-asym)
        ( is-weakly-linear)
    IsOrderedAbGroup.<-≤-weaken OAG = <-≤-weaken
    IsOrderedAbGroup.≤≃¬> OAG = ≤≃¬>
    IsOrderedAbGroup.+MonoR≤ OAG = +MonoR≤
    IsOrderedAbGroup.+MonoR< OAG = +MonoR<
    IsOrderedAbGroup.posSum→pos∨pos OAG = posSum→pos∨pos
    IsOrderedAbGroup.<-≤-trans OAG = <-≤-trans
    IsOrderedAbGroup.≤-<-trans OAG = ≤-<-trans

OrderedAbGroup→AbGroup : OrderedAbGroup ℓ ℓ' → AbGroup ℓ
OrderedAbGroup→AbGroup G .fst = G .fst
OrderedAbGroup→AbGroup G .snd = abgroupstr _ _ _ isAbGroup
  where
  open OrderedAbGroupStr (str G)

OrderedAbGroup→Pseudolattice : OrderedAbGroup ℓ ℓ' → Pseudolattice ℓ ℓ'
OrderedAbGroup→Pseudolattice G .fst = G .fst
OrderedAbGroup→Pseudolattice G .snd = pseudolatticestr _ isPseudolattice
  where
  open OrderedAbGroupStr (str G)

OrderedAbGroup→StrictOrder : OrderedAbGroup ℓ ℓ' → StrictOrder ℓ ℓ'
OrderedAbGroup→StrictOrder G .fst = G .fst
OrderedAbGroup→StrictOrder G .snd = strictorderstr _ isStrictOrder
  where
  open OrderedAbGroupStr (str G)

OrderedAbGroup→Poset : OrderedAbGroup ℓ ℓ' → Poset ℓ ℓ'
OrderedAbGroup→Poset = Pseudolattice→Poset ∘ OrderedAbGroup→Pseudolattice

OrderedAbGroup→Quoset : OrderedAbGroup ℓ ℓ' → Quoset ℓ ℓ'
OrderedAbGroup→Quoset = StrictOrder→Quoset ∘ OrderedAbGroup→StrictOrder

OrderedAbGroup→OrderedCommMonoid : OrderedAbGroup ℓ ℓ' → OrderedCommMonoid ℓ ℓ'
OrderedAbGroup→OrderedCommMonoid G .fst = G .fst
OrderedAbGroup→OrderedCommMonoid G .snd = OCM
  where
  open OrderedAbGroupStr (str G)

  OCM : OrderedCommMonoidStr _ _
  OrderedCommMonoidStr._≤_ OCM = _≤_
  OrderedCommMonoidStr._·_ OCM = _+_
  OrderedCommMonoidStr.ε OCM = 0g
  IsOrderedCommMonoid.isPoset (OrderedCommMonoidStr.isOrderedCommMonoid OCM) =
    isPoset
  IsOrderedCommMonoid.isCommMonoid
    ( OrderedCommMonoidStr.isOrderedCommMonoid OCM) =
    iscommmonoid isMonoid +Comm
  IsOrderedCommMonoid.MonotoneR
    ( OrderedCommMonoidStr.isOrderedCommMonoid OCM) {x} {y} {z} x≤y =
    +MonoR≤ x y z x≤y
  IsOrderedCommMonoid.MonotoneL
    ( OrderedCommMonoidStr.isOrderedCommMonoid OCM) {x} {y} {z} x≤y =
    subst2 _≤_ (+Comm x z) (+Comm y z) (+MonoR≤ x y z x≤y)

OrderedCommRing→OrderedAbGroup : OrderedCommRing ℓ ℓ' → OrderedAbGroup ℓ ℓ'
OrderedCommRing→OrderedAbGroup R .fst = R .fst
OrderedCommRing→OrderedAbGroup R .snd = orderedabgroupstr _ _ _ _ _ OAG
  where
  open OrderedCommRingStr (str R)

  OAG : IsOrderedAbGroup 0r _+_ -_ _<_ _≤_
  OAG =
    isorderedabgroup
      ( +IsAbGroup)
      ( isPseudolattice)
      ( isStrictOrder)
      ( <-≤-weaken)
      ( ≤≃¬>)
      ( <-≤-trans)
      ( ≤-<-trans)
      ( +MonoR≤)
      ( +MonoR<)
      ( posSum→pos∨pos)

isPropIsOrderedAbGroup :
  {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
  (_<_ _≤_ : G → G → Type ℓ') →
  isProp (IsOrderedAbGroup 0g _+_ -_ _<_ _≤_)
isPropIsOrderedAbGroup 0g _+_ -_ _<_ _≤_ =
  isOfHLevelRetractFromIso 1 IsOrderedAbGroupIsoΣ $
    isPropΣ (isPropIsAbGroup _ _ _) λ isAG →
    isPropΣ (isPropIsPseudolattice _) λ isPL →
    isPropΣ (isPropIsStrictOrder _) λ isSO →
    isProp×
      ( isPropΠ3 λ _ _ _ → isPL .IsPseudolattice.is-prop-valued _ _) $
    isProp×
      ( isPropΠ2 λ x y →
        isOfHLevel≃ 1
          ( IsPoset.is-prop-valued (IsPseudolattice.isPoset isPL) x y)
          ( isProp¬ (y < x))) $
    isProp×
      ( isPropΠ5 λ _ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _) $
    isProp×
      ( isPropΠ5 λ _ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _) $
    isProp×
      ( isPropΠ4 λ _ _ _ _ → isPL .IsPseudolattice.is-prop-valued _ _) $
    isProp×
      ( isPropΠ4 λ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _)
      ( isPropΠ3 λ _ _ _ → PT.squash₁)
