module HoTTReals.Relation.Premetric.Instances.ArchimedeanField where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties

open import HoTTReals.Algebra.ArchimedeanField.Base
open import HoTTReals.Algebra.OrderedField.Base

open PositiveRationals using (ℚ₊ ; ⟨_⟩₊ ; _+₊_ ; _<₊_)

private
  variable
    ℓ ℓ' : Level

module _ (F : ArchimedeanField ℓ ℓ') where

  FOrderedCommRing : OrderedCommRing ℓ ℓ'
  FOrderedCommRing =
    OrderedField→OrderedCommRing (ArchimedeanField→OrderedField F)

  open ArchimedeanFieldStr (snd F) using
    ( ι ; archimedeanProperty ; ιpres0 ; ιpres+ ; ιpres< ; ιreflect<)
  open OrderedCommRingStr (snd FOrderedCommRing)
  open OrderedCommRingReasoning FOrderedCommRing
  open OrderedCommRingTheory FOrderedCommRing
  open RingTheory (OrderedCommRing→Ring FOrderedCommRing)

  0<+Closed : (x y : ⟨ F ⟩) → 0r < x → 0r < y → 0r < x + y
  0<+Closed x y 0<x 0<y =
    is-trans< 0r y (x + y) 0<y $ subst (_< x + y) (+IdL y) (+MonoR< 0r x y 0<x)

  0<·Closed : (x y : ⟨ F ⟩) → 0r < x → 0r < y → 0r < x · y
  0<·Closed x y 0<x 0<y =
    subst (_< x · y) (0LeftAnnihilates y) (·MonoR< 0r x y 0<y 0<x)

  open Positive FOrderedCommRing 0<+Closed 0<·Closed using (selfSeparated)

  _≈ᶠ[_]_ : ⟨ F ⟩ → ℚ₊ → ⟨ F ⟩ → Type ℓ'
  x ≈ᶠ[ ε ] y = abs (x - y) < ι ⟨ ε ⟩₊

  0<ι₊ : (ε : ℚ₊) → 0r < ι ⟨ ε ⟩₊
  0<ι₊ ε = subst (_< ι ⟨ ε ⟩₊) ιpres0 $ ιpres< _ ⟨ ε ⟩₊ (snd ε)

  ι₊ : (q : ℚ) → 0r < ι q → ℚ₊
  fst (ι₊ q 0<ιq) = q
  snd (ι₊ q 0<ιq) = ιreflect< _ q $ subst (_< ι q) (sym ιpres0) 0<ιq

  isPremetricᶠ : IsPremetric _≈ᶠ[_]_
  isPremetricᶠ = isPMᶠ where
    open IsPremetric

    isPMᶠ : IsPremetric _≈ᶠ[_]_
    isPMᶠ .isSetM = is-set
    isPMᶠ .isProp≈ x y ε = is-prop-valued< (abs (x - y)) (ι ⟨ ε ⟩₊)
    isPMᶠ .isRefl≈ x ε = subst (_< ι ⟨ ε ⟩₊) (sym absΔ≡0) $ 0<ι₊ ε
      where
      absΔ≡0 : abs (x - x) ≡ 0r
      absΔ≡0 = cong abs (+InvR x) ∙ abs0
    isPMᶠ .isSym≈ x y ε = subst (_< ι ⟨ ε ⟩₊) $ abs-Comm x y
    isPMᶠ .isSeparated≈ x y x≈y = selfSeparated x y λ z →
      PT.rec
        ( is-prop-valued< (abs (x - y)) (fst z))
        ( below (fst z))
        ( archimedeanProperty 0r (fst z) (snd z))
      where
      below :
        (z : ⟨ F ⟩)
        → Σ[ q ∈ ℚ ] (0r < ι q) × (ι q < z)
        → abs (x - y) < z
      below z (q , 0<ιq , ιq<z) =
        is-trans< _ _ _ (x≈y (ι₊ q 0<ιq)) ιq<z
    isPMᶠ .isTriangular≈ x y z ε δ <ε <δ =
      subst (abs (x - z) <_) (sym $ ιpres+ ⟨ ε ⟩₊ ⟨ δ ⟩₊) $ begin<
        abs (x - z)
          ≤⟨ triangularInequality- x z y ⟩
        abs (x - y) + abs (y - z)
          <⟨ +Mono< _ _ _ _ <ε <δ ⟩
        ι ⟨ ε ⟩₊ + ι ⟨ δ ⟩₊ ◾
    isPMᶠ .isRounded≈ x y ε x≈y =
      PT.map between $ archimedeanProperty (abs (x - y)) (ι ⟨ ε ⟩₊) x≈y
      where
      between :
        Σ[ q ∈ ℚ ] (abs (x - y) < ι q) × (ι q < ι ⟨ ε ⟩₊)
        → Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x ≈ᶠ[ δ ] y)
      between (q , ∣x-y∣<ιq , ιq<ιε) =
        ι₊ q 0<ιq
        , ιreflect< q ⟨ ε ⟩₊ ιq<ιε
        , ∣x-y∣<ιq
        where
        0<ιq : 0r < ι q
        0<ιq = ≤-<-trans 0r (abs (x - y)) (ι q) (0≤abs (x - y)) ∣x-y∣<ιq

  inducedPremetricSpace : PremetricSpace ℓ ℓ'
  inducedPremetricSpace =
    premetricspace ⟨ F ⟩ _≈ᶠ[_]_ isPremetricᶠ

  IsCauchyComplete : Type (ℓ-max ℓ ℓ')
  IsCauchyComplete = PremetricTheory.isComplete inducedPremetricSpace

  isPropIsCauchyComplete : isProp IsCauchyComplete
  isPropIsCauchyComplete =
    PremetricTheory.isPropIsComplete inducedPremetricSpace
