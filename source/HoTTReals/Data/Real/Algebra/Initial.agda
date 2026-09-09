module HoTTReals.Data.Real.Algebra.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Categories.Limits.Initial

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Rationals using
  ( ℚPremetricSpace)
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals
open import Cubical.Relation.Premetric.Completion.Lift using
  ( module LiftCompleteCodomain ; nonExpansive≡)

open import HoTTReals.Algebra.ArchimedeanField.Base
open import HoTTReals.Algebra.ArchimedeanField.Properties
open import HoTTReals.Algebra.CommRing.Instances.Rationals
open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Categories.Instances.CauchyCompleteArchimedeanFields
open import HoTTReals.Data.Real.Algebra.ArchimedeanField
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Algebra.OrderedCommRing
open import HoTTReals.Data.Real.Algebra.OrderedField
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Addition
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Relation.Premetric.Completion.Lift using (continuous₂≡)
open import HoTTReals.Relation.Premetric.Instances.ArchimedeanField

open PositiveRationals using (ℚ₊ ; ⟨_⟩₊)
open OrderedAbGroupTheory ℝOrderedAbGroup using (abs ; abs<→< ; abs<→-<)
open OrderedAbGroupTheory ℚOrderedAbGroup using () renaming
  ( abs<→< to abs<→<ℚ ; abs<→-< to abs<→-<ℚ)
open OrderedCommRingTheory ℝOrderedCommRing using () renaming
  ( ≤→0≤Δ to ≤→0≤Δℝ ; 0≤→abs≡id to 0≤→abs≡idℝ)

private
  variable
    ℓ ℓ' : Level

module _ (F : OrderedField ℓ ℓ') (p : IsCauchyCompleteArchimedeanOrderedField F)
  where
  private
    A = OrderedField→ArchimedeanField F (fst p)
    N = inducedPremetricSpace A
    F' = OrderedField→OrderedCommRing F
    ℝ' = OrderedField→OrderedCommRing ℝOrderedField
    Fcr = OrderedCommRing→CommRing F'

    module rat = IsOrderedCommRingMono (snd ratᶠ)

    module F where
      open OrderedCommRingStr (snd F') public
      open OrderedCommRingTheory F' public
      open RingTheory (OrderedCommRing→Ring F') public

  open ArchimedeanFieldStr (snd A) using
    ( ι ; archimedeanProperty ; ιpres1 ; ιpres+ ; ιpres· ; ιpres- ; ιpres< ;
      ιreflect< ; isOrderedFieldHom)
  open ArchimedeanFieldTheory A using (ιpresAbs)
  open LiftCompleteCodomain ℚPremetricSpace N (snd p) using (liftNE)

  private
    ιpresΔ : (q r : ℚ) → ι (q ℚ.- r) ≡ ι q F.- ι r
    ιpresΔ q r = ιpres+ q (ℚ.- r) ∙ congR F._+_ (ιpres- r)

    ιⁿ : NE[ ℚPremetricSpace , N ]
    fst ιⁿ = ι
    IsNonExpansive.pres≈ (snd ιⁿ) q r ε q≈r =
      Δ<→≈ A (ι q) (ι r) ε
        ( subst (F._< ι ⟨ ε ⟩₊) (ιpresΔ q r) $
          ιpres< (q ℚ.- r) ⟨ ε ⟩₊ (abs<→<ℚ q≈r))
        ( subst2 F._<_ (ιpres- ⟨ ε ⟩₊) (ιpresΔ q r) $
          ιpres< (ℚ.- ⟨ ε ⟩₊) (q ℚ.- r) (abs<→-<ℚ q≈r))

    eⁿ : NE[ ℝPremetricSpace , N ]
    eⁿ = liftNE ιⁿ

    e : ℝ → ⟨ F ⟩
    e = fst eⁿ

    epres+ : (x y : ℝ) → e (x + y) ≡ e x F.+ e y
    epres+ =
      continuous₂≡
        ( ℚPremetricSpace)
        ( ℚPremetricSpace)
        ( N)
        ( λ x y → e (x + y))
        ( λ x y → e x F.+ e y)
        ( λ u → isNonExpansive→isContinuous _ _ _ $ snd $ eⁿ ∘NE [ u ]+ⁿ)
        ( λ v → isNonExpansive→isContinuous _ _ _ $ snd $ eⁿ ∘NE +ⁿ[ v ])
        ( λ u → isNonExpansive→isContinuous _ _ _ $ snd $ [_]+ⁿᶠ A (e u) ∘NE eⁿ)
        ( λ v → isNonExpansive→isContinuous _ _ _ $ snd $ +ⁿᶠ[_] A (e v) ∘NE eⁿ)
        ( ιpres+)

    epres· : (x y : ℝ) → e (x · y) ≡ e x F.· e y
    epres· =
      continuous₂≡
        ( ℚPremetricSpace)
        ( ℚPremetricSpace)
        ( N)
        ( λ x y → e (x · y))
        ( λ x y → e x F.· e y)
        ( λ u → snd $ NE→C eⁿ ∘C [ u ]·ᶜ)
        ( λ v → snd $ NE→C eⁿ ∘C ·ᶜ[ v ])
        ( λ u → snd $ [_]·ᶜᶠ A (e u) ∘C NE→C eⁿ)
        ( λ v → snd $ ·ᶜᶠ[_] A (e v) ∘C NE→C eⁿ)
        ( λ q r → cong e (rat·rat q r) ∙ ιpres· q r)

    eIsCommRingHom :
      IsCommRingHom (snd (OrderedCommRing→CommRing ℝ')) e (snd Fcr)
    eIsCommRingHom =
      makeIsCommRingHom {R = OrderedCommRing→CommRing ℝ'} {S = Fcr} {f = e}
        ιpres1 epres+ epres·

    epres- : (x : ℝ) → e (- x) ≡ F.- e x
    epres- = IsCommRingHom.pres- eIsCommRingHom

    epresΔ : (x y : ℝ) → e (x - y) ≡ e x F.- e y
    epresΔ x y = epres+ x (- y) ∙ cong (e x F.+_) (epres- y)

    epresAbs : (x : ℝ) → e (abs x) ≡ F.abs (e x)
    epresAbs =
      nonExpansive≡ ℚPremetricSpace N (eⁿ ∘NE absⁿ) (absⁿᶠ A ∘NE eⁿ) λ q →
        cong e (abs∘rat q) ∙ ιpresAbs q

    epres≤ : (x y : ℝ) → x ≤ y → e x F.≤ e y
    epres≤ x y x≤y =
      F.0≤Δ→≤ (e x) (e y) $ subst (F.0r F.≤_) (epresΔ y x) 0≤eΔ
      where
      0≤eΔ : F.0r F.≤ e (y - x)
      0≤eΔ =
        subst
          ( F.0r F.≤_)
          ( sym (epresAbs (y - x)) ∙
            cong e (0≤→abs≡idℝ (y - x) (≤→0≤Δℝ x y x≤y)))
          ( F.0≤abs (e (y - x)))

    epres< : (x y : ℝ) → x < y → e x F.< e y
    epres< x y =
      PT.rec (F.is-prop-valued< (e x) (e y)) $
        λ ((q , r) , x≤ratq , q<r , ratr≤y) →
          F.≤-<-trans (e x) (ι q) (e y) (epres≤ x (rat q) x≤ratq) $
          F.<-≤-trans (ι q) (ι r) (e y)
            ( ιpres< q r q<r)
            ( epres≤ (rat r) y ratr≤y)

    ereflect< : (x y : ℝ) → e x F.< e y → x < y
    ereflect< x y ex<ey =
      PT.rec (isProp< x y)
        ( λ (q , ex<ιq , ιq<ey) →
          PT.rec (isProp< x y)
            ( λ (r , ιq<ιr , ιr<ey) →
              ∣ (q , r)
              , invEq ≤≃¬> (λ ratq<x →
                  F.is-asym (e x) (ι q) ex<ιq (epres< (rat q) x ratq<x))
              , ιreflect< q r ιq<ιr
              , invEq ≤≃¬> (λ y<ratr →
                  F.is-asym (ι r) (e y) ιr<ey (epres< y (rat r) y<ratr)) ∣₁)
            ( archimedeanProperty (ι q) (e y) ιq<ey))
        ( archimedeanProperty (e x) (e y) ex<ey)

    eHom : IsOrderedCommRingHom (snd ℝ') e (snd F')
    IsOrderedCommRingHom.isCommRingHom eHom = eIsCommRingHom
    IsOrderedCommRingHom.pres≤ eHom = epres≤
    IsOrderedCommRingHom.reflect< eHom = ereflect<

    eMono : OrderedCommRingMono ℝ' F'
    fst eMono = e
    IsOrderedCommRingMono.isOrderedCommRingHom (snd eMono) = eHom
    IsOrderedCommRingMono.pres< (snd eMono) = epres<

    module _ (f : OrderedCommRingMono ℝ' F') where
      private
        module f = IsOrderedCommRingMono (snd f)
        f' = fst f

        f∘ratHom : CommRingHom ℚCommRing Fcr
        f∘ratHom = (_ , f.isCommRingHom) ∘cr (_ , rat.isCommRingHom)

        f∘rat≡ι : (q : ℚ) → f' (rat q) ≡ ι q
        f∘rat≡ι = funExt⁻ $ cong fst $ CommRingHomℚ≡ Fcr f∘ratHom (ι , isCommRingHom)
          where open IsOrderedCommRingMono isOrderedFieldHom

        f'presΔ : (x y : ℝ) → f' (x - y) ≡ f' x F.- f' y
        f'presΔ x y = f.pres+ x (- y) ∙ cong (f' x F.+_) (f.pres- y)

        fⁿ : NE[ ℝPremetricSpace , N ]
        fst fⁿ = f'
        IsNonExpansive.pres≈ (snd fⁿ) x y ε x∼y =
          Δ<→≈ A (f' x) (f' y) ε
            ( subst2 F._<_ (f'presΔ x y) (f∘rat≡ι ⟨ ε ⟩₊) $
              f.pres< (x - y) (rat ⟨ ε ⟩₊) $
                abs<→< {x - y} {rat ⟨ ε ⟩₊} ∣x-y∣<ε)
            ( subst2 F._<_
                ( f.pres- (rat ⟨ ε ⟩₊) ∙ cong F.-_ (f∘rat≡ι ⟨ ε ⟩₊))
                ( f'presΔ x y) $
              f.pres< (- rat ⟨ ε ⟩₊) (x - y) $
                abs<→-< {x - y} {rat ⟨ ε ⟩₊} ∣x-y∣<ε)
          where
          ∣x-y∣<ε : abs (x - y) < rat ⟨ ε ⟩₊
          ∣x-y∣<ε = equivFun (∼≃abs< {x} {y} {ε}) x∼y

      f≡e : (x : ℝ) → f' x ≡ e x
      f≡e = nonExpansive≡ ℚPremetricSpace N fⁿ eⁿ f∘rat≡ι

  isContrOrderedFieldHomℝ :
    isContr
      ( OrderedCommRingMono
        ( OrderedField→OrderedCommRing ℝOrderedField)
        ( OrderedField→OrderedCommRing F))
  isContrOrderedFieldHomℝ =
    eMono , λ f → OrderedCommRingMono≡ (sym (funExt (f≡e f)))

isInitialℝ :
  isInitial
    ( CauchyCompleteArchimedeanFieldsCategory {ℓ-zero} {ℓ-zero})
    ( ℝOrderedField , isCauchyCompleteArchimedeanOrderedFieldℝ)
isInitialℝ (F , isCauchyCompleteArchimedeanOrderedField) =
  isContrOrderedFieldHomℝ F isCauchyCompleteArchimedeanOrderedField
