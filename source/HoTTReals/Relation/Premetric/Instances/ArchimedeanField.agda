module HoTTReals.Relation.Premetric.Instances.ArchimedeanField where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver

open import HoTTReals.Algebra.ArchimedeanField.Base
open import HoTTReals.Algebra.ArchimedeanField.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Algebra.OrderedAbGroup.Properties
import HoTTReals.Algebra.OrderedCommRing.Properties as
  HoTTRealsOrderedCommRingProperties
open HoTTRealsOrderedCommRingProperties using (module OrderedCommRingMorphismsProperties)
open import HoTTReals.Algebra.CommRing.Instances.Rationals
open import HoTTReals.Algebra.OrderedField.Base

open PositiveRationals using (ℚ₊ ; ⟨_⟩₊ ; _+₊_ ; _<₊_)

private
  variable
    ℓ ℓ' : Level

module _ (F : ArchimedeanField ℓ ℓ') where

  private
    FCR = ArchimedeanField→CommRing F

  open ArchimedeanFieldStr (snd F)
  open ArchimedeanFieldTheory    F -- using (0<ι₊ ; ι₊ ; ∃abs<ι₊ ; <→-<→abs<)
  open ArchimedeanFieldReasoning F
  open OrderedCommRingTheory     (ArchimedeanField→OrderedCommRing F)
  open RingTheory                (ArchimedeanField→Ring F)
  open HoTTRealsOrderedCommRingProperties.OrderedCommRingTheory (ArchimedeanField→OrderedCommRing F)
    using (abs·)
  open OrderedAbGroupTheory ((OrderedCommRing→OrderedAbGroup ∘ ArchimedeanField→OrderedCommRing) F)
    using (absΔabs≤)
  open PremetricStr

  infix 5 _≈ᶠ[_]_

  _≈ᶠ[_]_ : ⟨ F ⟩ → ℚ₊ → ⟨ F ⟩ → Type ℓ'
  x ≈ᶠ[ ε ] y = abs (x - y) < ι ⟨ ε ⟩₊

  isPremetricᶠ : IsPremetric _≈ᶠ[_]_
  isPremetricᶠ = isPMᶠ where
    open IsPremetric

    isPMᶠ : IsPremetric _≈ᶠ[_]_
    isPMᶠ .isSetM = is-set
    isPMᶠ .isProp≈ x y ε = is-prop-valued< (abs (x - y)) (ι ⟨ ε ⟩₊)
    isPMᶠ .isRefl≈ x ε   = subst (_< ι ⟨ ε ⟩₊) (sym (cong abs (+InvR x) ∙ abs0)) $ 0<ι₊ ε
    isPMᶠ .isSym≈  x y ε = subst (_< ι ⟨ ε ⟩₊) $ abs-Comm x y
    isPMᶠ .isSeparated≈ x y ∀ε[x≈ε≈y] =
      equalByDifference x y $
      abs≤0→≡0 (x - y) $
      ¬<→≥ 0f (abs(x - y)) $
      PT.rec isProp⊥
      (λ (q , 0<ιq , ιq<∣x-y∣) → is-asym _ _ ιq<∣x-y∣ (∀ε[x≈ε≈y] (ι₊ q 0<ιq)))
      ∘ archimedeanProperty 0f (abs(x - y))
    isPMᶠ .isTriangular≈ x y z ε δ <ε <δ = begin<
      abs (x - z)                 ≤⟨ triangularInequality- x z y ⟩
      abs (x - y) + abs (y - z)   <⟨ +Mono< _ _ _ _ <ε <δ ⟩
      ι ⟨ ε ⟩₊ + ι ⟨ δ ⟩₊        ≡→≤⟨ sym $ ιpres+ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟩
      ι ⟨ ε +₊ δ ⟩₊               ◾
    isPMᶠ .isRounded≈ x y ε x≈y =
      PT.map
        (λ (q , ∣x-y∣<ιq , ιq<ιε) →
          ι₊ q (≤-<-trans _ _ _ (0≤abs _) ∣x-y∣<ιq)
        , ιreflect< q ⟨ ε ⟩₊ ιq<ιε
        , ∣x-y∣<ιq)
      $ archimedeanProperty (abs (x - y)) (ι ⟨ ε ⟩₊) x≈y

  ArchimedeanField→PremetricSpace : PremetricSpace ℓ ℓ'
  fst ArchimedeanField→PremetricSpace = fst F
  _≈[_]_ (snd ArchimedeanField→PremetricSpace) = _≈ᶠ[_]_
  isPremetric (snd ArchimedeanField→PremetricSpace) = isPremetricᶠ

  IsCauchyComplete : Type (ℓ-max ℓ ℓ')
  IsCauchyComplete = PremetricTheory.isComplete ArchimedeanField→PremetricSpace

  isPropIsCauchyComplete : isProp IsCauchyComplete
  isPropIsCauchyComplete =
    PremetricTheory.isPropIsComplete ArchimedeanField→PremetricSpace

  Δ<→≈ : (x y : ⟨ F ⟩) (ε : ℚ₊) → x - y < ι ⟨ ε ⟩₊ → - ι ⟨ ε ⟩₊ < x - y → x ≈ᶠ[ ε ] y
  Δ<→≈ x y ε Δ<ιε -ιε<Δ =
    <→-<→abs< (x - y) (ι ⟨ ε ⟩₊) Δ<ιε $
      subst (- (x - y) <_) (-Idempotent (ι ⟨ ε ⟩₊)) (-Flip< _ _ -ιε<Δ)

  [_]+ⁿᶠ : ⟨ F ⟩ → NE[ ArchimedeanField→PremetricSpace , ArchimedeanField→PremetricSpace ]
  fst [ z ]+ⁿᶠ = z +_
  IsNonExpansive.pres≈ (snd [ z ]+ⁿᶠ) x y ε = subst (_< ι ⟨ ε ⟩₊) (cong abs (solve! FCR))

  +ⁿᶠ[_] : ⟨ F ⟩ → NE[ ArchimedeanField→PremetricSpace , ArchimedeanField→PremetricSpace ]
  fst +ⁿᶠ[ z ] = _+ z
  IsNonExpansive.pres≈ (snd +ⁿᶠ[ z ]) x y ε = subst (_< ι ⟨ ε ⟩₊) (cong abs (solve! FCR))

  absⁿᶠ : NE[ ArchimedeanField→PremetricSpace , ArchimedeanField→PremetricSpace ]
  fst absⁿᶠ = abs
  IsNonExpansive.pres≈ (snd absⁿᶠ) x y ε =
    ≤-<-trans (abs (abs x - abs y)) (abs (x - y)) (ι ⟨ ε ⟩₊) (absΔabs≤ x y)

  ·IsLipschitzWithLᶠ :
    (M : ℚ₊) (z : ⟨ F ⟩) → abs z < ι ⟨ M ⟩₊ →
    IsLipschitzWith
    (snd ArchimedeanField→PremetricSpace) (z ·_) (snd ArchimedeanField→PremetricSpace) M
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

  [_]·ᶜᶠ : ⟨ F ⟩ → C[ ArchimedeanField→PremetricSpace , ArchimedeanField→PremetricSpace ]
  fst [ z ]·ᶜᶠ = z ·_
  snd [ z ]·ᶜᶠ =
    isLipschitz→isContinuous _ (z ·_) _ $
      PT.map (λ (M , ∣z∣<ιM) → M , ·IsLipschitzWithLᶠ M z ∣z∣<ιM) (∃abs<ι₊ z)

  ·ᶜᶠ[_] : ⟨ F ⟩ → C[ ArchimedeanField→PremetricSpace , ArchimedeanField→PremetricSpace ]
  fst ·ᶜᶠ[ z ] = _· z
  snd ·ᶜᶠ[ z ] =
    subst
      ( λ f →
        isContinuous (snd ArchimedeanField→PremetricSpace) f (snd ArchimedeanField→PremetricSpace))
      ( funExt λ x → ·Comm z x)
      ( snd [ z ]·ᶜᶠ)

IsCauchyCompleteArchimedeanOrderedField :
  OrderedField ℓ ℓ' → Type (ℓ-max ℓ ℓ')
IsCauchyCompleteArchimedeanOrderedField F =
  Σ[ isArchimedeanOrderedField ∈ IsArchimedeanOrderedField F ]
    IsCauchyComplete (OrderedField→ArchimedeanField F isArchimedeanOrderedField)
