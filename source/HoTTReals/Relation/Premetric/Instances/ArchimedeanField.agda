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
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties

open import Cubical.Tactics.CommRingSolver

open import HoTTReals.Algebra.ArchimedeanField.Base
open import HoTTReals.Algebra.ArchimedeanField.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Algebra.OrderedAbGroup.Properties
import HoTTReals.Algebra.OrderedCommRing.Properties as
  HoTTRealsOrderedCommRingProperties
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
    ( ι ; archimedeanProperty ; ιpres+ ; ιpres· ; ιreflect<)
  open ArchimedeanFieldTheory F using (0<ι₊ ; ι₊ ; ∃abs<ι₊ ; <→-<→abs<)
  open OrderedCommRingStr (snd FOrderedCommRing)
  open OrderedCommRingReasoning FOrderedCommRing
  open OrderedCommRingTheory FOrderedCommRing
  open RingTheory (OrderedCommRing→Ring FOrderedCommRing)
  open HoTTRealsOrderedCommRingProperties.OrderedCommRingTheory FOrderedCommRing
    using (abs·)
  open OrderedAbGroupTheory (OrderedCommRing→OrderedAbGroup FOrderedCommRing)
    using (absΔabs≤)

  0<+Closed : (x y : ⟨ F ⟩) → 0r < x → 0r < y → 0r < x + y
  0<+Closed x y 0<x 0<y =
    is-trans< 0r y (x + y) 0<y $ subst (_< x + y) (+IdL y) (+MonoR< 0r x y 0<x)

  0<·Closed : (x y : ⟨ F ⟩) → 0r < x → 0r < y → 0r < x · y
  0<·Closed x y 0<x 0<y =
    subst (_< x · y) (0LeftAnnihilates y) (·MonoR< 0r x y 0<y 0<x)

  open Positive FOrderedCommRing 0<+Closed 0<·Closed using (selfSeparated)

  _≈ᶠ[_]_ : ⟨ F ⟩ → ℚ₊ → ⟨ F ⟩ → Type ℓ'
  x ≈ᶠ[ ε ] y = abs (x - y) < ι ⟨ ε ⟩₊

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

  Δ<→≈ : (x y : ⟨ F ⟩) (ε : ℚ₊) → x - y < ι ⟨ ε ⟩₊ → - ι ⟨ ε ⟩₊ < x - y →
    x ≈ᶠ[ ε ] y
  Δ<→≈ x y ε Δ<ιε -ιε<Δ =
    <→-<→abs< (x - y) (ι ⟨ ε ⟩₊) Δ<ιε $
      subst (- (x - y) <_) (-Idempotent (ι ⟨ ε ⟩₊)) (-Flip< _ _ -ιε<Δ)

  [_]+ⁿᶠ : ⟨ F ⟩ → NE[ inducedPremetricSpace , inducedPremetricSpace ]
  fst [ z ]+ⁿᶠ = z +_
  IsNonExpansive.pres≈ (snd [ z ]+ⁿᶠ) x y ε =
    subst (_< ι ⟨ ε ⟩₊) (cong abs (sym cancel))
    where
    cancel : (z + x) - (z + y) ≡ x - y
    cancel = solve! (OrderedCommRing→CommRing FOrderedCommRing)

  +ⁿᶠ[_] : ⟨ F ⟩ → NE[ inducedPremetricSpace , inducedPremetricSpace ]
  fst +ⁿᶠ[ z ] = _+ z
  IsNonExpansive.pres≈ (snd +ⁿᶠ[ z ]) x y ε =
    subst (_< ι ⟨ ε ⟩₊) (cong abs (sym cancel))
    where
    cancel : (x + z) - (y + z) ≡ x - y
    cancel = solve! (OrderedCommRing→CommRing FOrderedCommRing)

  absⁿᶠ : NE[ inducedPremetricSpace , inducedPremetricSpace ]
  fst absⁿᶠ = abs
  IsNonExpansive.pres≈ (snd absⁿᶠ) x y ε =
    ≤-<-trans (abs (abs x - abs y)) (abs (x - y)) (ι ⟨ ε ⟩₊) (absΔabs≤ x y)

  ·IsLipschitzWithLᶠ :
    (M : ℚ₊) (z : ⟨ F ⟩) → abs z < ι ⟨ M ⟩₊ →
    IsLipschitzWith
      ( snd inducedPremetricSpace) (z ·_) (snd inducedPremetricSpace) M
  IsLipschitzWith.pres≈ (·IsLipschitzWithLᶠ M z ∣z∣<ιM) x y ε ∣x-y∣<ιε =
    subst (abs (z · x - z · y) <_) (sym $ ιpres· ⟨ M ⟩₊ ⟨ ε ⟩₊) $ begin<
      abs (z · x - z · y)
        ≡→≤⟨ cong abs (sym $ ·DistR- z x y) ∙ abs· z (x - y) ⟩
      abs z · abs (x - y)
        ≤⟨ ·MonoR≤ (abs z) (ι ⟨ M ⟩₊) (abs (x - y)) (0≤abs (x - y))
             (<-≤-weaken (abs z) (ι ⟨ M ⟩₊) ∣z∣<ιM) ⟩
      ι ⟨ M ⟩₊ · abs (x - y)
        <⟨ ·MonoL< (abs (x - y)) (ι ⟨ ε ⟩₊) (ι ⟨ M ⟩₊) (0<ι₊ M) ∣x-y∣<ιε ⟩
      ι ⟨ M ⟩₊ · ι ⟨ ε ⟩₊ ◾

  [_]·ᶜᶠ : ⟨ F ⟩ → C[ inducedPremetricSpace , inducedPremetricSpace ]
  fst [ z ]·ᶜᶠ = z ·_
  snd [ z ]·ᶜᶠ =
    isLipschitz→isContinuous _ (z ·_) _ $
      PT.map (λ (M , ∣z∣<ιM) → M , ·IsLipschitzWithLᶠ M z ∣z∣<ιM) (∃abs<ι₊ z)

  ·ᶜᶠ[_] : ⟨ F ⟩ → C[ inducedPremetricSpace , inducedPremetricSpace ]
  fst ·ᶜᶠ[ z ] = _· z
  snd ·ᶜᶠ[ z ] =
    subst
      ( λ f →
        isContinuous (snd inducedPremetricSpace) f (snd inducedPremetricSpace))
      ( funExt λ x → ·Comm z x)
      ( snd [ z ]·ᶜᶠ)

IsCauchyCompleteArchimedeanOrderedField :
  OrderedField ℓ ℓ' → Type (ℓ-max ℓ ℓ')
IsCauchyCompleteArchimedeanOrderedField F =
  Σ[ isArchimedeanOrderedField ∈ IsArchimedeanOrderedField F ]
    IsCauchyComplete (OrderedField→ArchimedeanField F isArchimedeanOrderedField)
