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
open import HoTTReals.Algebra.ArchimedeanField.Instances.Rationals
open import HoTTReals.Algebra.CommRing.Instances.Rationals
open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedCommRing.Properties using (
  module OrderedCommRingMorphismsProperties)
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
open import HoTTReals.Relation.Premetric.Instances.Rationals

open PositiveRationals using (ℚ₊ ; ⟨_⟩₊)
open OrderedAbGroupTheory ℝOrderedAbGroup using (abs ; abs<→< ; abs<→-<)
open OrderedAbGroupTheory ℚOrderedAbGroup using () renaming
  ( abs<→< to abs<→<ℚ ; abs<→-< to abs<→-<ℚ)
open OrderedCommRingTheory ℝOrderedCommRing using () renaming
  ( ≤→0≤Δ to ≤→0≤Δℝ ; 0≤→abs≡id to 0≤→abs≡idℝ)

private
  variable
    ℓ ℓ<≤ ℓ' ℓ<≤' : Level

module _ {F : ArchimedeanField ℓ ℓ<≤} {K : ArchimedeanField ℓ' ℓ<≤'} where

  private
    F≈ = ArchimedeanField→PremetricSpace F
    K≈ = ArchimedeanField→PremetricSpace K
    module F where
      open ArchimedeanFieldStr       (snd F)                              public
      open ArchimedeanFieldReasoning F                                    public
      open OrderedCommRingTheory     (ArchimedeanField→OrderedCommRing F) public
      open PremetricStr              (snd F≈)                             public

      ιAF : ArchimedeanFieldHom ℚArchimedeanField F
      fst ιAF = ι
      snd ιAF = isOrderedFieldHom

    module K where
      open ArchimedeanFieldStr       (snd K)                              public
      open ArchimedeanFieldReasoning K                                    public
      open OrderedCommRingTheory     (ArchimedeanField→OrderedCommRing K) public
      open PremetricStr              (snd K≈)                             public

      ιAF : ArchimedeanFieldHom ℚArchimedeanField K
      fst ιAF = ι
      snd ιAF = isOrderedFieldHom

  ArchimedeanFieldHom→NE : ArchimedeanFieldHom F K → NE[ F≈ , K≈ ]
  fst (ArchimedeanFieldHom→NE fh@(f , isHom)) = f
  snd (ArchimedeanFieldHom→NE fh@(f , isHom)) = f≈ where
    open IsNonExpansive
    open IsOrderedCommRingMono isHom
    open OrderedCommRingMorphismsProperties
      (snd (ArchimedeanField→OrderedCommRing F))
      f
      (snd (ArchimedeanField→OrderedCommRing K))

    f∘ι : ArchimedeanFieldHom ℚArchimedeanField K
    f∘ι = _∘af_ {F = ℚArchimedeanField} {K = F} {H = K} fh F.ιAF

    f≈ : IsNonExpansive _ f _
    f≈ .pres≈ x y ε x≈y = K.begin<
      K.abs(f x K.- f y)  K.≡→≤⟨ sym $ cong K.abs $ pres+ _ _ ∙ congR K._+_ (pres- _) ⟩
      K.abs(f (x F.- y))  K.≤⟨ absFun≤FunAbs isHom (x F.- y) ⟩
      f (F.abs (x F.- y)) K.<⟨ pres< _ _ x≈y ⟩
      f (F.ι ⟨ ε ⟩₊)       K.≡→≤⟨ isUniqueAFHomℚ→ K f∘ι K.ιAF ⟨ ε ⟩₊ ⟩
      K.ι ⟨ ε ⟩₊           K.◾

module UniversalPropertyℝ
  (F : OrderedField ℓ ℓ') (p : IsCauchyCompleteArchimedeanOrderedField F)
  where
  private
    A = OrderedField→ArchimedeanField F (fst p)
    N = ArchimedeanField→PremetricSpace A
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

  module Existence where
    ιpresΔ : (q r : ℚ) → ι (q ℚ.- r) ≡ ι q F.- ι r
    ιpresΔ q r = ιpres+ q (ℚ.- r) ∙ congR F._+_ (ιpres- r)

    ιⁿ : NE[ ℚPremetricSpace , N ]
    fst ιⁿ = ι
    snd ιⁿ = transport
      (λ i → IsNonExpansive (snd (inducedPremetricSpaceℚ≡ i)) ι (snd N))
      (snd (ArchimedeanFieldHom→NE (ι , isOrderedFieldHom)))

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

  module Uniqueness (f g : OrderedCommRingMono ℝ' F') where
    private
      module f = IsOrderedCommRingMono (snd f)
      f' = fst f
      module g = IsOrderedCommRingMono (snd g)
      g' = fst g

      f∘ratHom : ArchimedeanFieldHom ℚArchimedeanField A
      f∘ratHom = _∘af_ {F = ℚArchimedeanField} {ℝArchimedeanField} {A} f ratᶠ

      g∘ratHom : ArchimedeanFieldHom ℚArchimedeanField A
      g∘ratHom = _∘af_ {F = ℚArchimedeanField} {ℝArchimedeanField} {A} g ratᶠ

    pointwise : ∀ x → f' x ≡ g' x
    pointwise = nonExpansive≡ ℚPremetricSpace (ArchimedeanField→PremetricSpace A)
      ( fst f
      , transport
          (λ i → IsNonExpansive (snd (inducedPremetricSpaceℝ≡ i)) f' (snd N))
          (snd (ArchimedeanFieldHom→NE f)))
      ( fst g
      , transport
          (λ i → IsNonExpansive (snd (inducedPremetricSpaceℝ≡ i)) g' (snd N))
          (snd (ArchimedeanFieldHom→NE g)))
      (isUniqueAFHomℚ→ A f∘ratHom g∘ratHom)

    isProp[AFℝ,-] : f ≡ g
    isProp[AFℝ,-] = OrderedCommRingMono≡ (funExt pointwise)

  isContrOrderedFieldHomℝ :
    isContr
      ( OrderedCommRingMono
        ( OrderedField→OrderedCommRing ℝOrderedField)
        ( OrderedField→OrderedCommRing F))
  fst isContrOrderedFieldHomℝ = Existence.eMono
  snd isContrOrderedFieldHomℝ = Uniqueness.isProp[AFℝ,-] Existence.eMono

isInitialℝ :
  isInitial
    ( CauchyCompleteArchimedeanFieldsCategory {ℓ-zero} {ℓ-zero})
    ( ℝOrderedField , isCauchyCompleteArchimedeanOrderedFieldℝ)
isInitialℝ = uncurry UniversalPropertyℝ.isContrOrderedFieldHomℝ
