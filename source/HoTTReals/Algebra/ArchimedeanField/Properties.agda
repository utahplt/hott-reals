module HoTTReals.Algebra.ArchimedeanField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using ()

open import Cubical.HITs.PropositionalTruncation as PT

open import HoTTReals.Algebra.ArchimedeanField.Base
open import HoTTReals.Algebra.OrderedField.Base

open PositiveRationals using (ℚ₊ ; ⟨_⟩₊)

private
  variable
    ℓ ℓ' : Level

module _ (F : ArchimedeanField ℓ ℓ') where
  private
    F' = ArchimedeanField→OrderedCommRing F

  open ArchimedeanFieldStr (snd F) using
    ( ι ; archimedeanProperty ; ιpres0 ; ιpres- ; ιpres≤ ; ιpres< ; ιreflect<)
  open OrderedCommRingStr (snd F')
  open OrderedCommRingTheory F' using
    ( abs ; 0≤abs ; 0≤→abs≡id ; abs- ; ≤0→0≤- ; ⊔LUB ; <SumLeftPos)
  open OrderedCommRingStr (snd ℚOrderedCommRing) using () renaming (0r to 0ℚ)
  open OrderedCommRingTheory ℚOrderedCommRing using () renaming
    ( abs to absℚ ; 0≤→abs≡id to 0≤→absℚ≡id ; abs- to absℚ- ;
      ≤0→0≤- to ≤0→0≤-ℚ)

  module ArchimedeanFieldTheory where

    0<ι₊ : (ε : ℚ₊) → 0r < ι ⟨ ε ⟩₊
    0<ι₊ ε = subst (_< ι ⟨ ε ⟩₊) ιpres0 $ ιpres< _ ⟨ ε ⟩₊ (snd ε)

    ι₊ : (q : ℚ) → 0r < ι q → ℚ₊
    fst (ι₊ q 0<ιq) = q
    snd (ι₊ q 0<ιq) = ιreflect< _ q $ subst (_< ι q) (sym ιpres0) 0<ιq

    ∃abs<ι₊ : (x : ⟨ F ⟩) → ∃[ M ∈ ℚ₊ ] (abs x < ι ⟨ M ⟩₊)
    ∃abs<ι₊ x =
      PT.map
        ( λ (q , ∣x∣<ιq , _) →
          ι₊ q (≤-<-trans 0r (abs x) (ι q) (0≤abs x) ∣x∣<ιq) , ∣x∣<ιq)
        ( archimedeanProperty (abs x) (abs x + 1r) (<SumLeftPos (abs x) 1r 0<1))

    <→-<→abs< : (x y : ⟨ F ⟩) → x < y → - x < y → abs x < y
    <→-<→abs< x y x<y -x<y =
      PT.rec2
        ( is-prop-valued< (abs x) y)
        ( λ (q , x<ιq , ιq<y) (r , -x<ιr , ιr<y) →
          PT.rec
            ( is-prop-valued< (abs x) y)
            ( ⊎.rec
              ( λ q≤r →
                ≤-<-trans (abs x) (ι r) y
                  ( ⊔LUB
                    ( <-≤-weaken x (ι r) $
                      <-≤-trans x (ι q) (ι r) x<ιq (ιpres≤ q r q≤r))
                    ( <-≤-weaken (- x) (ι r) -x<ιr))
                  ( ιr<y))
              ( λ r≤q →
                ≤-<-trans (abs x) (ι q) y
                  ( ⊔LUB
                    ( <-≤-weaken x (ι q) x<ιq)
                    ( <-≤-weaken (- x) (ι q) $
                      <-≤-trans (- x) (ι r) (ι q) -x<ιr (ιpres≤ r q r≤q)))
                  ( ιq<y)))
            ( ℚ.isTotal≤ q r))
        ( archimedeanProperty x y x<y)
        ( archimedeanProperty (- x) y -x<y)

    ιpresAbs : (q : ℚ) → ι (absℚ q) ≡ abs (ι q)
    ιpresAbs q =
      PT.rec
        ( is-set (ι (absℚ q)) (abs (ι q)))
        ( ⊎.rec
          ( λ 0≤q →
            cong ι (0≤→absℚ≡id q 0≤q) ∙
            sym (0≤→abs≡id (ι q) (subst (_≤ ι q) ιpres0 (ιpres≤ 0ℚ q 0≤q))))
          ( λ q≤0 →
            ι (absℚ q)
              ≡⟨ cong ι (sym (absℚ- q) ∙ 0≤→absℚ≡id (ℚ.- q) (≤0→0≤-ℚ q q≤0)) ⟩
            ι (ℚ.- q)
              ≡⟨ ιpres- q ⟩
            - ι q
              ≡⟨ sym $ 0≤→abs≡id (- ι q) $
                   ≤0→0≤- (ι q) (subst (ι q ≤_) ιpres0 (ιpres≤ q 0ℚ q≤0)) ⟩
            abs (- ι q)
              ≡⟨ abs- (ι q) ⟩
            abs (ι q) ∎))
        ( ℚ.isTotal≤ 0ℚ q)
