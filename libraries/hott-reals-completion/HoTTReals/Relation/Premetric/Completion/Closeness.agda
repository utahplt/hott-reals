{-
  Characterization of closeness relation in the completion ;
  Numbered definitions and theorems are from
  Formalising real numbers in homotopy type theory, Gaëtan Gilbert, 2017
-}
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric

-- we use this combinations of levels to avoid using `Lift`s when not needed
module HoTTReals.Relation.Premetric.Completion.Closeness {ℓ} ℓ'
  (M : PremetricSpace ℓ (ℓ-max ℓ ℓ')) where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import HoTTReals.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals renaming (ℚCommRing to ℚCR)
open import Cubical.Algebra.OrderedField
open import Cubical.Algebra.OrderedField.Instances.Rationals

import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Reflection.RecordEquiv

open import HoTTReals.Relation.Premetric.Completion.Base M renaming (ℭ to ℭM)
open import HoTTReals.Relation.Premetric.Completion.Elim M

open import Cubical.Tactics.CommRingSolver

open OrderedFieldReasoning ℚOrderedField
open OrderedFieldTheory    ℚOrderedField

open PremetricStr (snd M)
open PremetricTheory.PremetricReasoning M
open PremetricTheory M

private
  ℓ'' = ℓ-max ℓ ℓ'

-- helper lemmas
-- TO DO: inline solver when mjtg's version will be ready
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R) using () renaming (_+_ to _+r_ ; _-_ to _-r_)
  opaque

    [[Δ+δ]+ε]+η≡Δ+[ε+[δ+η]] : ∀ Δ δ ε η → ((Δ +r δ) +r ε) +r η ≡ Δ +r (ε +r (δ +r η))
    [[Δ+δ]+ε]+η≡Δ+[ε+[δ+η]] _ _ _ _ = solve! R

    Δ+ε+δ'≡Δ+δ'+ε : ∀ Δ ε δ' → (Δ +r ε) +r δ' ≡ (Δ +r δ') +r ε
    Δ+ε+δ'≡Δ+δ'+ε _ _ _ = solve! R

    Δ+ε+[η'+δ]≡[Δ+η']+[ε+δ] : ∀ Δ ε η' δ → Δ +r ε +r (η' +r δ) ≡ (Δ +r η') +r (ε +r δ)
    Δ+ε+[η'+δ]≡[Δ+η']+[ε+δ] _ _ _ _ = solve! R

    Δ+ε+[δ+η']≡[Δ+η']+[ε+δ] : ∀ Δ ε η' δ → Δ +r ε +r (δ +r η') ≡ (Δ +r η') +r (ε +r δ)
    Δ+ε+[δ+η']≡[Δ+η']+[ε+δ] _ _ _ _ = solve! R

    Δ+[η'+δ]+ε≡Δ+η'+[ε+δ] : ∀ Δ η' δ ε → Δ +r (η' +r δ) +r ε ≡ Δ +r η' +r (ε +r δ)
    Δ+[η'+δ]+ε≡Δ+η'+[ε+δ] _ _ _ _ = solve! R

    Δ+[θ'+δ]+ε+η≡Δ+θ'+[ε+[δ+η]] :
      ∀ Δ θ' δ ε η → Δ +r (θ' +r δ) +r ε +r η ≡ (Δ +r θ') +r (ε +r (δ +r η))
    Δ+[θ'+δ]+ε+η≡Δ+θ'+[ε+[δ+η]] _ _ _ _ _ = solve! R

    Δ+[η''+δ]+ε+η'≡Δ+[η'+η'']+[ε+δ] :
      ∀ Δ η'' δ ε η' → Δ +r (η'' +r δ) +r ε +r η' ≡ Δ +r (η' +r η'') +r (ε +r δ)
    Δ+[η''+δ]+ε+η'≡Δ+[η'+η'']+[ε+δ] _ _ _ _ _ = solve! R

    Δ+[η'+δ]+ε+η''≡Δ+[η'+η'']+[ε+δ] :
      ∀ Δ η' δ ε η'' → Δ +r (η' +r δ) +r ε +r η'' ≡ Δ +r (η' +r η'') +r (ε +r δ)
    Δ+[η'+δ]+ε+η''≡Δ+[η'+η'']+[ε+δ] _ _ _ _ _ = solve! R

    Δ+[θ''+δ]+ε+[θ'+η]≡Δ+[θ'+θ'']+[ε+[δ+η]] : ∀ Δ θ'' δ ε θ' η →
      Δ +r (θ'' +r δ) +r ε +r (θ' +r η) ≡ Δ +r (θ' +r θ'') +r (ε +r (δ +r η))
    Δ+[θ''+δ]+ε+[θ'+η]≡Δ+[θ'+θ'']+[ε+[δ+η]] _ _ _ _ _ _ = solve! R

    Δ+[θ'+δ]+ε+[η+θ'']≡Δ+[θ'+θ'']+[ε+[δ+η]] : ∀ Δ θ' δ ε η θ'' →
      Δ +r (θ' +r δ) +r ε +r (η +r θ'') ≡ Δ +r (θ' +r θ'') +r (ε +r (δ +r η))
    Δ+[θ'+δ]+ε+[η+θ'']≡Δ+[θ'+θ'']+[ε+[δ+η]] _ _ _ _ _ _ = solve! R

-- Definition 3.8
record IsBall (B : ℚ₊ → ℭM → Type ℓ'') : Type (ℓ-suc ℓ'') where
  no-eta-equality
  constructor isball
  field
    isPropBall       : ∀ ε y     → isProp (B ε y)
    isRoundedBall    : ∀ ε y     → B ε y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × B δ y
    isTriangularBall : ∀ ε δ y z → B ε y → y ∼[ δ ] z → B (ε +₊ δ) z

unquoteDecl IsBallIsoΣ = declareRecordIsoΣ IsBallIsoΣ (quote IsBall)

Balls : Type (ℓ-suc ℓ'')
Balls = Σ[ B ∈ (ℚ₊ → ℭM → Type ℓ'') ] IsBall B

infixl 4 _[_]ᴮ_
_[_]ᴮ_ : Balls → ℚ₊ → ℭM → Type ℓ''
_[_]ᴮ_ = fst

isPropIsBall : ∀ B → isProp (IsBall B)
isPropIsBall B = isOfHLevelRetractFromIso 1
  IsBallIsoΣ $
  isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ isPropBall →
  isProp×
    (isPropΠ3 λ _ _ _ → squash₁)
    (isPropΠ6 λ _ _ _ _ _ _ → isPropBall _ _)

_≈ᴮ[_]_ : Balls → ℚ₊ → Balls → Type ℓ''
(B , _) ≈ᴮ[ ε ] (B' , _) = ∀ δ y → (B δ y → B' (δ +₊ ε) y) × (B' δ y → B (δ +₊ ε) y)

isProp≈ᴮ : ∀ B B' ε → isProp (B ≈ᴮ[ ε ] B')
isProp≈ᴮ (B , isBallB) (B' , isBallB') ε =
  isPropΠ2 λ δ y → isProp× (isProp→ (B'.isPropBall _ _)) (isProp→ (B.isPropBall _ _))
  where
    module B  = IsBall isBallB
    module B' = IsBall isBallB'

isSym≈ᴮ : ∀ B B' ε → B ≈ᴮ[ ε ] B' → B' ≈ᴮ[ ε ] B
isSym≈ᴮ B B' ε B≈B' δ y = fst Σ-swap-≃ (B≈B' δ y)

-- Definition 3.9
-- NOTE : The definition of UpperCut present in Gilpert's paper requires
-- an equivalence in the field `isRoundedUpperCut`.
-- However, in order to construct `B[_]⟨_,_⟩`, we only need one implication.
record IsUpperCut (U : ℚ₊ → Type ℓ'') : Type (ℓ-suc ℓ'') where
  no-eta-equality
  constructor isuppercut
  field
    isPropUpperCut    : ∀ ε → isProp (U ε)
    isRoundedUpperCut : ∀ ε → U ε → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × U δ

unquoteDecl IsUpperCutIsoΣ = declareRecordIsoΣ IsUpperCutIsoΣ (quote IsUpperCut)

UpperCuts : Type (ℓ-suc ℓ'')
UpperCuts = Σ[ U ∈ (ℚ₊ → Type ℓ'') ] IsUpperCut U

infixl 4 _[_]ᵁ
_[_]ᵁ : UpperCuts → ℚ₊ → Type ℓ''
_[_]ᵁ = fst

isPropIsUpperCut : ∀ U → isProp (IsUpperCut U)
isPropIsUpperCut U = isOfHLevelRetractFromIso 1
  IsUpperCutIsoΣ $
  isPropΣ (isPropΠ λ _ → isPropIsProp) λ _ →
    (isPropΠ2 λ _ _ → squash₁)

_≈ᵁ[_]_ : UpperCuts → ℚ₊ → UpperCuts → Type ℓ''
U ≈ᵁ[ ε ] U' = ∀ δ → (U [ δ ]ᵁ → U' [ δ +₊ ε ]ᵁ) × (U' [ δ ]ᵁ → U [ δ +₊ ε ]ᵁ)

isProp≈ᵁ : ∀ U U' ε → isProp (U ≈ᵁ[ ε ] U')
isProp≈ᵁ (U , isUpperCutU) (U' , isUpperCutU') ε =
  isPropΠ λ δ → isProp× (isProp→ (U'.isPropUpperCut _)) (isProp→ (U.isPropUpperCut _))
  where
    module U  = IsUpperCut isUpperCutU
    module U' = IsUpperCut isUpperCutU'

isSym≈ᵁ : ∀ U U' ε → U ≈ᵁ[ ε ] U' → U' ≈ᵁ[ ε ] U
isSym≈ᵁ U U' ε U≈U' δ = fst Σ-swap-≃ (U≈U' δ)

-- Lemma 3.10
isSeparated≈ᴮ : ∀ B B' → (∀ ε → B ≈ᴮ[ ε ] B') → B ≡ B'
isSeparated≈ᴮ (B , isBallB) (B' , isBallB') B≈B' = Σ≡Prop isPropIsBall $
  funExt λ ε → funExt λ y → hPropExt (B.isPropBall _ _) (B'.isPropBall _ _)
    (λ Bεy → flip (PT.rec (B'.isPropBall _ _)) (B.isRoundedBall ε y Bεy)
     λ (δ , δ<ε , Bδy) →
     subst (flip B' y) (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                       (fst (B≈B' [ ε -₊ δ ]⟨ δ<ε ⟩ δ y) Bδy) )
    (λ B'εy → flip (PT.rec (B.isPropBall _ _)) (B'.isRoundedBall ε y B'εy)
     λ (δ , δ<ε , B'δy) →
     subst (flip B  y) (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                       (snd (B≈B' [ ε -₊ δ ]⟨ δ<ε ⟩ δ y) B'δy))
  where
    module B  = IsBall isBallB
    module B' = IsBall isBallB'

-- Lemma 3.11
isSeparated≈ᵁ : ∀ U U' → (∀ ε → U ≈ᵁ[ ε ] U') → U ≡ U'
isSeparated≈ᵁ (U , isUpperCutU) (U' , isUpperCutU') U≈U' = Σ≡Prop isPropIsUpperCut $
  funExt λ ε → hPropExt (U.isPropUpperCut _) (U'.isPropUpperCut _)
    (λ Uε → flip (PT.rec (U'.isPropUpperCut _)) (U.isRoundedUpperCut _ Uε)
     λ (δ , δ<ε , Uδ) → subst U' (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                                 (fst (U≈U' [ ε -₊ δ ]⟨ δ<ε ⟩ δ) Uδ))
    (λ U'ε → flip (PT.rec (U.isPropUpperCut _)) (U'.isRoundedUpperCut _ U'ε)
     λ (δ , δ<ε , U'δ) → subst U (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                                 (snd (U≈U' [ ε -₊ δ ]⟨ δ<ε ⟩ δ) U'δ))
  where
    module U  = IsUpperCut isUpperCutU
    module U' = IsUpperCut isUpperCutU'

isBall→isUpperCut : (B : Balls) → ∀ y → IsUpperCut (flip (fst B) y)
isBall→isUpperCut B y = isUC where opaque
  open IsBall
  open IsUpperCut

  isUC : IsUpperCut (flip (fst B) y)
  isPropUpperCut    isUC = flip (isPropBall (snd B)) y
  isRoundedUpperCut isUC = flip (isRoundedBall (B .snd)) y

UpperCut≈ : (x y : ⟨ M ⟩) → UpperCuts
fst (UpperCut≈ x y) = x ≈[_] y
snd (UpperCut≈ x y) = isUC where opaque
  open IsUpperCut

  isUC : IsUpperCut (x ≈[_] y)
  isPropUpperCut    isUC = isProp≈ x y
  isRoundedUpperCut isUC = isRounded≈ x y

UpperCut∃< : (U : ℚ₊ → UpperCuts) → UpperCuts
fst (UpperCut∃< U) = λ ε → ∃[ (Δ , δ) ∈ ℚ₊ × ℚ₊ ] (fst Δ ℚ.+ fst δ ≡ fst ε) × fst (U δ) Δ
snd (UpperCut∃< U) = isUC∃< where opaque
  module UC (η : ℚ₊) = IsUpperCut (snd (U η))
  open IsUpperCut

  isUC∃< : IsUpperCut
    λ ε → ∃[ (Δ , δ) ∈ ℚ₊ × ℚ₊ ] (fst Δ ℚ.+ fst δ ≡ fst ε) × fst (U δ) Δ
  isPropUpperCut    isUC∃< = λ _ → squash₁
  isRoundedUpperCut isUC∃< ε ∃<Uε = do
    ((Δ , δ) , Δ+δ≡ε , Uδ[Δ]) ← ∃<Uε
    (Δ' , Δ'<Δ , Uδ[Δ']) ← UC.isRoundedUpperCut δ Δ Uδ[Δ]
    let
      Δ'+δ<ε : Δ' +₊ δ <₊ ε
      Δ'+δ<ε = begin<
        ⟨ Δ' +₊ δ ⟩₊   <⟨ Δ'<Δ <+[ ⟨ δ ⟩₊ ] ⟩
        ⟨ Δ  +₊ δ ⟩₊ ≡→≤⟨ Δ+δ≡ε ⟩
        ⟨ ε ⟩₊        ◾
    return (Δ' +₊ δ , Δ'+δ<ε , ∣ (Δ' , δ) , refl , Uδ[Δ'] ∣₁)

UpperCut∃₂< : (U : ℚ₊ → ℚ₊ → UpperCuts) → UpperCuts
fst (UpperCut∃₂< U) =
  λ ε → ∃[ (Δ , δ , η) ∈ ℚ₊ × ℚ₊ × ℚ₊ ]
    (fst Δ ℚ.+ (fst δ ℚ.+ fst η) ≡ fst ε) × fst (U δ η) Δ
snd (UpperCut∃₂< U) = isUC∃₂< where opaque
  module UC (δ η : ℚ₊) = IsUpperCut (snd (U δ η))
  open IsUpperCut

  isUC∃₂< : IsUpperCut
    λ ε → ∃[ (Δ , δ , η) ∈ ℚ₊ × ℚ₊ × ℚ₊ ]
    (fst Δ ℚ.+ (fst δ ℚ.+ fst η) ≡ fst ε) × fst (U δ η) Δ
  isPropUpperCut    isUC∃₂< = λ _ → squash₁
  isRoundedUpperCut isUC∃₂< ε ∃<₂Uε = do
    ((Δ , δ , η) , Δ+[δ+η]≡ε , Uδ,η[Δ]) ← ∃<₂Uε
    (Δ' , Δ'<Δ , Uδ,η[Δ']) ← UC.isRoundedUpperCut δ η Δ Uδ,η[Δ]
    let
      Δ'+[δ+η]<ε : Δ' +₊ (δ +₊ η) <₊ ε
      Δ'+[δ+η]<ε = begin<
        ⟨ Δ' +₊ (δ +₊ η) ⟩₊   <⟨ Δ'<Δ <+[ ⟨ δ +₊ η ⟩₊ ] ⟩
        ⟨ Δ  +₊ (δ +₊ η) ⟩₊ ≡→≤⟨ Δ+[δ+η]≡ε ⟩
        ⟨ ε ⟩₊                ◾
    return (Δ' +₊ (δ +₊ η) , Δ'+[δ+η]<ε , ∣ (Δ' , δ , η) , refl , Uδ,η[Δ'] ∣₁)

nonExpanding∼→≈ᵁ : (ℭM → UpperCuts) → Type ℓ''
nonExpanding∼→≈ᵁ B = ∀ x y ε → x ∼[ ε ] y → B x ≈ᵁ[ ε ] B y

nonExpanding∼→≈ᴮ : (ℭM → Balls) → Type ℓ''
nonExpanding∼→≈ᴮ B = ∀ x y ε → x ∼[ ε ] y → B x ≈ᴮ[ ε ] B y

-- Lemma 3.12
isNonExpanding∼→≈ᵁ→isBall : ∀ B → nonExpanding∼→≈ᵁ B → IsBall (λ ε y → fst (B y) ε)
isNonExpanding∼→≈ᵁ→isBall B isNE = isBall where opaque
  open IsBall
  open IsUpperCut

  isBall : IsBall λ ε y → fst (B y) ε
  isPropBall       isBall ε y                = isPropUpperCut (snd (B y)) ε
  isRoundedBall    isBall ε y                = isRoundedUpperCut (snd (B y)) ε
  isTriangularBall isBall ε δ y z ⟨By⟩ε y∼δz = fst (isNE y z δ y∼δz ε) ⟨By⟩ε

module _
  (x : ⟨ M ⟩) (Bx,y_ Bx,z_ : ℚ₊ → UpperCuts) (ε δ η : ℚ₊)
  (Bx,yc : ∀ α β → (Bx,y α) ≈ᵁ[ α +₊ β ] (Bx,y β))
  (Bx,zc : ∀ α β → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
  (Bx,yδ≈ᵁBx,zη : (Bx,y δ) ≈ᵁ[ ε ] (Bx,z η))
  (Δ : ℚ₊)
  where

  B⟨ι,lim⟩→B⟨ι,lim⟩ : (UpperCut∃< Bx,y_) [ Δ ]ᵁ
                  → (UpperCut∃< Bx,z_) [ Δ +₊ (ε +₊ (δ +₊ η)) ]ᵁ
  B⟨ι,lim⟩→B⟨ι,lim⟩ = PT.map λ ((Δ' , δ') , Δ'+δ'≡Δ , Bx,yδ'[Δ']) →
    let
      Δ'+[δ'+δ]≡Δ+δ = ℚ.+Assoc ⟨ Δ' ⟩₊ _ _ ∙ cong (ℚ._+ ⟨ δ ⟩₊) Δ'+δ'≡Δ
    in
      ((Δ +₊ δ) +₊ ε , η)
    , [[Δ+δ]+ε]+η≡Δ+[ε+[δ+η]] ℚCR ⟨ Δ ⟩₊ _ _ _
    , (begin→[ Bx,yδ'[Δ'] ]
        Bx,y δ' [ Δ' ]ᵁ              →⟨ fst (Bx,yc δ' δ Δ') ⟩
        Bx,y δ  [ Δ' +₊ (δ' +₊ δ) ]ᵁ →⟨ subst (Bx,y δ [_]ᵁ) (ℚ₊≡ Δ'+[δ'+δ]≡Δ+δ) ⟩
        Bx,y δ  [ Δ +₊ δ ]ᵁ          →⟨ fst (Bx,yδ≈ᵁBx,zη (Δ +₊ δ)) ⟩
        Bx,z η  [ (Δ +₊ δ) +₊ ε ]ᵁ   )

private

  B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ : ∀ x y z ε → (y ≈[ ε ] z) → UpperCut≈ x y ≈ᵁ[ ε ] UpperCut≈ x z
  fst (B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ x y z ε y≈z δ) = flip (isTriangular≈ x y z δ ε) y≈z
  snd (B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ x y z ε y≈z δ) = flip (isTriangular≈ x z y δ ε) (isSym≈ y z ε y≈z)

  B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ : ∀ x y Bx,z_ ε δ → (Bx,zc : ∀ α β → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                  → (Bx,y≈ᵁBx,zδ : (UpperCut≈ x y) ≈ᵁ[ ε ] (Bx,z δ))
                  → (UpperCut≈ x y) ≈ᵁ[ ε +₊ δ ] (UpperCut∃< Bx,z_)
  fst (B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ x y Bx,z_ ε δ Bx,zc Bx,y≈ᵁBx,zδ Δ) = λ x≈[Δ]y →
    ∣ (Δ +₊ ε , δ) , sym (ℚ.+Assoc ⟨ Δ ⟩₊ _ _) , fst (Bx,y≈ᵁBx,zδ Δ) x≈[Δ]y ∣₁
  snd (B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ x y Bx,z_ ε δ Bx,zc Bx,y≈ᵁBx,zδ Δ) = PT.rec (isProp≈ x y _)
    λ ((Δ' , δ') , Δ'+δ'≡Δ , Bx,zδ'[Δ']) →
    let
      step0 = ℚ.+Assoc ⟨ Δ' ⟩₊ _ _ ∙ cong (ℚ._+ ⟨ δ ⟩₊) Δ'+δ'≡Δ
      step1 = sym (ℚ.+Assoc ⟨ Δ ⟩₊ _ _) ∙ cong (⟨ Δ ⟩₊ ℚ.+_) (ℚ.+Comm ⟨ δ ⟩₊ ⟨ ε ⟩₊)
    in
    begin→[ Bx,zδ'[Δ'] ]
      Bx,z δ' [ Δ' ]ᵁ              →⟨ fst (Bx,zc δ' δ Δ') ⟩
      Bx,z δ  [ Δ' +₊ (δ' +₊ δ) ]ᵁ →⟨ subst (fst (Bx,z δ)) (ℚ₊≡ step0) ⟩
      Bx,z δ  [ Δ +₊ δ ]ᵁ          →⟨ snd (Bx,y≈ᵁBx,zδ (Δ +₊ δ)) ⟩
      x ≈[ (Δ +₊ δ) +₊ ε ] y       →⟨ subst≈ x y step1 ⟩
      x ≈[ Δ +₊ (ε +₊ δ) ] y

  B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ : (x : ⟨ M ⟩) → ∀ Bx,y_ Bx,z_ ε δ η
                    → (Bx,yc : ∀ α β → (Bx,y α) ≈ᵁ[ α +₊ β ] (Bx,y β))
                    → (Bx,zc : ∀ α β → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                    → (Bx,yδ≈ᵁBx,zη : (Bx,y δ) ≈ᵁ[ ε ] (Bx,z η))
                    → (UpperCut∃< Bx,y_) ≈ᵁ[ ε +₊ (δ +₊ η) ] (UpperCut∃< Bx,z_)
  fst (B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ x Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Bx,yδ≈ᵁBx,zη Δ) =
    B⟨ι,lim⟩→B⟨ι,lim⟩ x Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Bx,yδ≈ᵁBx,zη Δ
  snd (B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ x Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Bx,yδ≈ᵁBx,zη Δ) =
    subst (λ - → (UpperCut∃< Bx,y_) [ Δ +₊ (ε +₊ -) ]ᵁ)
          (ℚ₊≡ {η +₊ δ} {δ +₊ η} (ℚ.+Comm ⟨ η ⟩₊ ⟨ δ ⟩₊))
        ∘ B⟨ι,lim⟩→B⟨ι,lim⟩ x Bx,z_ Bx,y_ ε η δ Bx,zc Bx,yc
          (isSym≈ᵁ (Bx,y δ) (Bx,z η) ε Bx,yδ≈ᵁBx,zη) Δ

open RecℭSym

BallsAtι[Rec] : ⟨ M ⟩ → RecℭSym UpperCuts (flip ∘ _≈ᵁ[_]_)
BallsAtι[Rec] x .funι     = UpperCut≈ x
BallsAtι[Rec] x .funLim   = const ∘ UpperCut∃<
BallsAtι[Rec] x .funEq    = isSeparated≈ᵁ
BallsAtι[Rec] x .ι︵ι     = B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ x
BallsAtι[Rec] x .ι︵lim   = B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ x
BallsAtι[Rec] x .lim︵lim = B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ x
BallsAtι[Rec] x .isSym︵  = isSym≈ᵁ
BallsAtι[Rec] x .isProp︵ = isProp≈ᵁ

-- Definition 3.13 (first part)
B⟨ι_,_⟩ : ⟨ M ⟩ → ℭM → UpperCuts
B⟨ι_,_⟩ = RecℭSym.go ∘ BallsAtι[Rec]

B[_]⟨ι_,_⟩ : ℚ₊ → ⟨ M ⟩ → ℭM → Type ℓ''
B[ ε ]⟨ι x , y ⟩ = B⟨ι x , y ⟩ [ ε ]ᵁ

isNonExpanding∼→≈ᵁB⟨ι_,⟩ : ∀ (x : ⟨ M ⟩) → nonExpanding∼→≈ᵁ B⟨ι x ,_⟩
isNonExpanding∼→≈ᵁB⟨ι_,⟩ x y z ε = RecℭSym.go∼ (BallsAtι[Rec] x)

B⟨ι_,⟩ : ⟨ M ⟩ → Balls
fst B⟨ι x ,⟩ = B[_]⟨ι x ,_⟩
snd B⟨ι x ,⟩ = isBallB⟨ιx,⟩ where opaque
  isBallB⟨ιx,⟩ : IsBall B[_]⟨ι x ,_⟩
  isBallB⟨ιx,⟩ = isNonExpanding∼→≈ᵁ→isBall B⟨ι x ,_⟩ isNonExpanding∼→≈ᵁB⟨ι x ,⟩

module _ (Bx : ℚ₊ → Balls) (Bxc : ∀ ε δ → Bx ε ≈ᴮ[ ε +₊ δ ] Bx δ) where

  private
    module isBx (η : ℚ₊) where
      open IsBall (snd (Bx η)) public
      ball+∼ : ∀ {ε δ y z} → y ∼[ δ ] z → Bx η .fst ε y → Bx η .fst (ε +₊ δ) z
      ball+∼ = flip (isTriangularBall _ _ _ _)

  B⟨limᴿ[_,_],ι_⟩ : ⟨ M ⟩ → UpperCuts
  B⟨limᴿ[_,_],ι_⟩ y = UpperCut∃< λ δ →
    flip (fst (Bx δ)) (ι y) , isBall→isUpperCut (Bx δ) (ι y)

  B⟨limᴿ[_,_],lim[_,_]⟩ : (y : ℚ₊ → ℭM) (yc : ∀ α β → y α ∼[ α +₊ β ] y β) → UpperCuts
  B⟨limᴿ[_,_],lim[_,_]⟩ y yc = UpperCut∃₂< λ δ η →
    flip (fst (Bx δ)) (y η) , isBall→isUpperCut (Bx δ) (y η)

  module _ (y z : ⟨ M ⟩) (ε : ℚ₊) (y≈z : y ≈[ ε ] z) (δ : ℚ₊) where opaque

    B⟨lim,ι⟩→B⟨lim,ι⟩ : B⟨limᴿ[_,_],ι_⟩ y [ δ ]ᵁ → B⟨limᴿ[_,_],ι_⟩ z [ δ +₊ ε ]ᵁ
    B⟨lim,ι⟩→B⟨lim,ι⟩ = PT.map λ ((Δ , δ') , Δ+δ'≡δ , B[Δ]xδ',y) →
        (Δ +₊ ε , δ')
      , (Δ+ε+δ'≡Δ+δ'+ε ℚCR ⟨ Δ ⟩₊ _ _) ∙ cong (ℚ._+ ⟨ ε ⟩₊) Δ+δ'≡δ
      , isBx.ball+∼ δ' (ι-ι y≈z) B[Δ]xδ',y

  module _
    (y : ⟨ M ⟩) (z : ℚ₊ → ℭM) (ε δ : ℚ₊)
    (zc : ∀ α β → z α ∼[ α +₊ β ] z β)
    (y∼zδ : ι y ∼[ ε ] z δ) (η : ℚ₊)
    where opaque

    B⟨lim,ι⟩→B⟨lim,lim⟩ : B⟨limᴿ[_,_],ι_⟩ y [ η ]ᵁ
                       → B⟨limᴿ[_,_],lim[_,_]⟩ z zc [ η +₊ (ε +₊ δ) ]ᵁ
    B⟨lim,ι⟩→B⟨lim,lim⟩ = PT.map λ ((Δ , η') , Δ+η'≡η , B[Δ]xη',y) →
        (Δ +₊ ε , η' , δ)
      , (Δ+ε+[η'+δ]≡[Δ+η']+[ε+δ] ℚCR ⟨ Δ ⟩₊ _ _ _) ∙ cong (ℚ._+ ⟨ ε +₊ δ ⟩₊) Δ+η'≡η
      , isBx.ball+∼ η' y∼zδ B[Δ]xη',y

    B⟨lim,lim⟩→B⟨lim,ι⟩ : B⟨limᴿ[_,_],lim[_,_]⟩ z zc [ η ]ᵁ
                       → B⟨limᴿ[_,_],ι_⟩ y [ η +₊ (ε +₊ δ) ]ᵁ
    B⟨lim,lim⟩→B⟨lim,ι⟩ = PT.map λ ((Δ , η' , η'') , Δ+[η'+η'']≡η , B[Δ]xη',zη'') →
        (Δ +₊ (η'' +₊ δ) +₊ ε , η')
      , Δ+[η''+δ]+ε+η'≡Δ+[η'+η'']+[ε+δ] ℚCR ⟨ Δ ⟩₊ _ _ _ _ ∙ cong (ℚ._+ _) Δ+[η'+η'']≡η
      , (begin→[ B[Δ]xη',zη'' ]
        Bx η' [ Δ ]ᴮ z η''                 →⟨ isBx.ball+∼ η' (zc η'' δ) ⟩
        Bx η' [ Δ +₊ (η'' +₊ δ) ]ᴮ z δ     →⟨ isBx.ball+∼ η' (isSym∼ _ _ _ y∼zδ) ⟩
        Bx η' [ Δ +₊ (η'' +₊ δ) +₊ ε ]ᴮ ι y)

  module _
    (y z : ℚ₊ → ℭM) (ε δ η : ℚ₊)
    (yc : ∀ α β → y α ∼[ α +₊ β ] y β)
    (zc : ∀ α β → z α ∼[ α +₊ β ] z β)
    (yδ∼zη : y δ ∼[ ε ] z η) (θ : ℚ₊)
    where opaque

    B⟨lim,lim⟩→B⟨lim,lim⟩ : B⟨limᴿ[_,_],lim[_,_]⟩ y yc [ θ ]ᵁ
                         → B⟨limᴿ[_,_],lim[_,_]⟩ z zc [ θ +₊ (ε +₊ (δ +₊ η)) ]ᵁ
    B⟨lim,lim⟩→B⟨lim,lim⟩ = PT.map λ ((Δ , θ' , θ'') , Δ+[θ'+θ'']≡θ , B[Δ]xθ',yθ'') →
        (Δ +₊ (θ'' +₊ δ) +₊ ε , θ' , η)
        , ( Δ+[θ''+δ]+ε+[θ'+η]≡Δ+[θ'+θ'']+[ε+[δ+η]] ℚCR ⟨ Δ ⟩₊ ⟨ θ'' ⟩₊ _ _ ⟨ θ' ⟩₊ _
          ∙ cong (ℚ._+ _) Δ+[θ'+θ'']≡θ)
        , (begin→[ B[Δ]xθ',yθ'' ]
          Bx θ' [ Δ ]ᴮ y θ''                  →⟨ isBx.ball+∼ θ' (yc θ'' δ) ⟩
          Bx θ' [ Δ +₊ (θ'' +₊ δ) ]ᴮ y δ      →⟨ isBx.ball+∼ θ' yδ∼zη ⟩
          Bx θ' [ Δ +₊ (θ'' +₊ δ) +₊ ε ]ᴮ z η )

  private
    B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩ : ∀ y z ε
                      → (y ≈[ ε ] z)
                      → (B⟨limᴿ[_,_],ι_⟩ y) ≈ᵁ[ ε ] (B⟨limᴿ[_,_],ι_⟩ z)
    fst (B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩ y z ε y≈z δ) = B⟨lim,ι⟩→B⟨lim,ι⟩ y z ε y≈z δ
    snd (B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩ y z ε y≈z δ) = B⟨lim,ι⟩→B⟨lim,ι⟩ z y ε (isSym≈ y z ε y≈z) δ

    B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩ : ∀ y z ε δ zc
                        → (y∼zδ : ι y ∼[ ε ] z δ)
                        → (Bx,z_ : ℚ₊ → UpperCuts)
                        → ((α β : ℚ₊) → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                        → (B⟨limᴿ[_,_],ι_⟩ y) ≈ᵁ[ ε ] (Bx,z δ)
                        → (B⟨limᴿ[_,_],ι_⟩ y) ≈ᵁ[ ε +₊ δ ] (B⟨limᴿ[_,_],lim[_,_]⟩ z zc)
    fst (B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩ y z ε δ zc y∼zδ _ _ _ η) =
      B⟨lim,ι⟩→B⟨lim,lim⟩ y z ε δ zc y∼zδ η
    snd (B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩ y z ε δ zc y∼zδ _ _ _ η) =
      B⟨lim,lim⟩→B⟨lim,ι⟩ y z ε δ zc y∼zδ η

    B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩ : ∀ y z ε δ η yc zc
                          → (yδ∼zη : y δ ∼[ ε ] z η)
                          → (Bx,y_ : ℚ₊ → UpperCuts)
                          → ((α β : ℚ₊) → (Bx,y α) ≈ᵁ[ α +₊ β ] (Bx,y β))
                          → (Bx,z_ : ℚ₊ → UpperCuts)
                          → ((α β : ℚ₊) → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                          → (Bx,y δ) ≈ᵁ[ ε ] (Bx,z η)
                          → (B⟨limᴿ[_,_],lim[_,_]⟩ y yc) ≈ᵁ[ ε +₊ (δ +₊ η) ] (B⟨limᴿ[_,_],lim[_,_]⟩ z zc)
    fst (B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩ y z ε δ η yc zc yδ∼zη _ _ _ _ _ θ) =
      B⟨lim,lim⟩→B⟨lim,lim⟩ y z ε δ η yc zc yδ∼zη θ
    snd (B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩ y z ε δ η yc zc yδ∼zη _ _ _ _ _ θ) =
      subst (λ - → B⟨limᴿ[_,_],lim[_,_]⟩ y yc [ θ +₊ (ε +₊ -) ]ᵁ)
            (ℚ₊≡ {η +₊ δ} {δ +₊ η} (ℚ.+Comm ⟨ η ⟩₊ ⟨ δ ⟩₊))
          ∘ B⟨lim,lim⟩→B⟨lim,lim⟩ z y ε η δ zc yc (isSym∼ _ _ _ yδ∼zη) θ

  open CasesℭSym

  BallsAtlim[Cases] : CasesℭSym UpperCuts (flip ∘ _≈ᵁ[_]_)
  BallsAtlim[Cases] .funι     = B⟨limᴿ[_,_],ι_⟩
  BallsAtlim[Cases] .funLim   = B⟨limᴿ[_,_],lim[_,_]⟩
  BallsAtlim[Cases] .funEq    = isSeparated≈ᵁ
  BallsAtlim[Cases] .ι︵ι     = B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩
  BallsAtlim[Cases] .ι︵lim   = B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩
  BallsAtlim[Cases] .lim︵lim = B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩
  BallsAtlim[Cases] .isSym︵  = isSym≈ᵁ
  BallsAtlim[Cases] .isProp︵ = isProp≈ᵁ

  B⟨limᴿ[_,_],_⟩ : ℭM → UpperCuts
  B⟨limᴿ[_,_],_⟩ = CasesℭSym.go BallsAtlim[Cases]

  isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩ : nonExpanding∼→≈ᵁ B⟨limᴿ[_,_],_⟩
  isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩ = λ _ _ _ → CasesℭSym.go∼ BallsAtlim[Cases]

  B⟨limᴿ[_,_],⟩ : Balls
  fst B⟨limᴿ[_,_],⟩ = flip (fst ∘ B⟨limᴿ[_,_],_⟩)
  snd B⟨limᴿ[_,_],⟩ = isBallB⟨limᴿ[_,_],⟩ where opaque
    isBallB⟨limᴿ[_,_],⟩ : IsBall (flip (fst ∘ B⟨limᴿ[_,_],_⟩))
    isBallB⟨limᴿ[_,_],⟩ = isNonExpanding∼→≈ᵁ→isBall B⟨limᴿ[_,_],_⟩ isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩

B[_]⟨limᴿ[_,_],_⟩ : ℚ₊ → ∀ Bx (Bxc : ∀ ε δ → Bx ε ≈ᴮ[ ε +₊ δ ] Bx δ) → ℭM → Type _
B[_]⟨limᴿ[_,_],_⟩ ε Bx Bxc = fst B⟨limᴿ[ Bx , Bxc ],⟩ ε

module _ (x y : ⟨ M ⟩) (ε : ℚ₊) (x≈y : x ≈[ ε ] y) where opaque
  open IsBall

  B⟨ι,⟩→B⟨ι,⟩ : ∀ z δ → B[ δ ]⟨ι x , z ⟩ → B[ δ +₊ ε ]⟨ι y , z ⟩
  B⟨ι,⟩→B⟨ι,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → (δ : ℚ₊) → B[ δ ]⟨ι x , z ⟩ → B[ δ +₊ ε ]⟨ι y , z ⟩
    e .funι    z δ x≈z = begin≈[ δ +₊ ε ]⟨ ℚ.+Comm ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟩
      y ≈[ ε ]⟨ ≈⁻ x≈y ⟩ x ≈[ δ ]⟨ x≈z ⟩ z ≈∎
    e .funLim  z zc Bx,z→By,z δ = PT.map λ ((Δ , δ') , Δ+δ'≡δ , B[Δ]ιx,zδ') →
        (Δ +₊ ε , δ')
      , Δ+ε+δ'≡Δ+δ'+ε ℚCR ⟨ Δ ⟩₊ _ _ ∙ cong (ℚ._+ ⟨ ε ⟩₊) Δ+δ'≡δ
      , Bx,z→By,z δ' Δ B[Δ]ιx,zδ'
    e .is-prop z = isPropΠ λ δ → isProp→ (isPropBall (snd B⟨ι y ,⟩) (δ +₊ ε) z)

module _
  (x : ⟨ M ⟩) (By : ℚ₊ → Balls) (ε δ : ℚ₊)
  (Byc : ∀ α β → By α ≈ᴮ[ α +₊ β ] By β)
  (Bιx≈ᴮ[ε]Byδ : B⟨ι x ,⟩ ≈ᴮ[ ε ] By δ)
  where opaque

  open IsBall

  B⟨ι,⟩→B⟨lim,⟩ : ∀ z η → B[ η ]⟨ι x , z ⟩ → B[ η +₊ (ε +₊ δ) ]⟨limᴿ[ By , Byc ], z ⟩
  B⟨ι,⟩→B⟨lim,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ η → B[ η ]⟨ι x , z ⟩ → B[ η +₊ (ε +₊ δ) ]⟨limᴿ[ By , Byc ], z ⟩
    e .funι    z η x≈z =
      ∣ (η +₊ ε , δ)
      , sym (ℚ.+Assoc ⟨ η ⟩₊ _ _)
      , fst (Bιx≈ᴮ[ε]Byδ η (ι z)) x≈z ∣₁
    e .funLim  z zc _ η = PT.map λ ((Δ , η') , Δ+η'≡η , B[Δ]ιx,zη') →
        (Δ +₊ ε , δ , η')
      , Δ+ε+[δ+η']≡[Δ+η']+[ε+δ] ℚCR ⟨ Δ ⟩₊ _ _ _ ∙ cong (ℚ._+ _) Δ+η'≡η
      , fst (Bιx≈ᴮ[ε]Byδ Δ (z η')) B[Δ]ιx,zη'
    e .is-prop z = isPropΠ λ η → isProp→ (isPropBall (snd B⟨limᴿ[ By , Byc ],⟩) _ z)

  B⟨lim,⟩→B⟨ι,⟩ : ∀ z η → B[ η ]⟨limᴿ[ By , Byc ], z ⟩ → B[ η +₊ (ε +₊ δ) ]⟨ι x , z ⟩
  B⟨lim,⟩→B⟨ι,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ η → B[ η ]⟨limᴿ[ By , Byc ], z ⟩ → B[ η +₊ (ε +₊ δ) ]⟨ι x , z ⟩
    e .funι z η = PT.rec (isProp≈ x z _) λ ((Δ , η') , Δ+η'≡η , B[Δ]yη',ιz) →
      let
        step = subst≈ x z (Δ+[η'+δ]+ε≡Δ+η'+[ε+δ] ℚCR ⟨ Δ ⟩₊ _ _ _ ∙ cong (ℚ._+ _) Δ+η'≡η)
      in
      begin→[ B[Δ]yη',ιz ]
        By η' [ Δ ]ᴮ ι z             →⟨ fst (Byc η' δ Δ (ι z)) ⟩
        By δ [ Δ +₊ (η' +₊ δ) ]ᴮ ι z →⟨ snd (Bιx≈ᴮ[ε]Byδ (Δ +₊ (η' +₊ δ)) (ι z)) ⟩
        x ≈[ Δ +₊ (η' +₊ δ) +₊ ε ] z →⟨ step ⟩
        x ≈[ η +₊ (ε +₊ δ) ] z
    e .funLim z zc _ η = PT.map λ ((Δ , η' , η'') , Δ+[η'+η'']≡η , B[Δ]yη',zη'') →
      (Δ +₊ (η' +₊ δ) +₊ ε , η'')
      , ( Δ+[η'+δ]+ε+η''≡Δ+[η'+η'']+[ε+δ] ℚCR ⟨ Δ ⟩₊ ⟨ η' ⟩₊ _ _ _
        ∙ cong (ℚ._+ _) Δ+[η'+η'']≡η)
      , (begin→[ B[Δ]yη',zη'' ]
        By η' [ Δ ]ᴮ z η''                    →⟨ fst (Byc η' δ Δ (z η'')) ⟩
        By δ [ Δ +₊ (η' +₊ δ) ]ᴮ z η''        →⟨ snd (Bιx≈ᴮ[ε]Byδ _ (z η'')) ⟩
        B[ Δ +₊ (η' +₊ δ) +₊ ε ]⟨ι x , z η'' ⟩ )
    e .is-prop z = isPropΠ λ η → isProp→ (isPropBall (snd B⟨ι x ,⟩) _ z)

module _
  (Bx By : ℚ₊ → Balls) (ε δ η : ℚ₊)
  (Bxc : ∀ α β → (Bx α) ≈ᴮ[ α +₊ β ] (Bx β))
  (Byc : ∀ α β → (By α) ≈ᴮ[ α +₊ β ] (By β))
  (Bxδ≈ᴮ[ε]Byη : (Bx δ) ≈ᴮ[ ε ] (By η))
  where opaque

  open IsBall

  B⟨lim,⟩→B⟨lim,⟩ : ∀ z θ → B[ θ ]⟨limᴿ[ Bx , Bxc ], z ⟩
                         → B[ θ +₊ (ε +₊ (δ +₊ η)) ]⟨limᴿ[ By , Byc ], z ⟩
  B⟨lim,⟩→B⟨lim,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop
    e : Elimℭ-Prop λ z → ∀ θ → B[ θ ]⟨limᴿ[ Bx , Bxc ], z ⟩
                             → B[ θ +₊ (ε +₊ (δ +₊ η)) ]⟨limᴿ[ By , Byc ], z ⟩
    e .funι z θ = PT.map λ ((Δ , θ') , Δ+θ'≡θ , B[Δ]xθ',ιz) →
        (Δ +₊ (θ' +₊ δ) +₊ ε , η)
      , Δ+[θ'+δ]+ε+η≡Δ+θ'+[ε+[δ+η]] ℚCR ⟨ Δ ⟩₊ _ _ _ _ ∙ cong (ℚ._+ _) Δ+θ'≡θ
      , (begin→[ B[Δ]xθ',ιz ]
          Bx θ' [ Δ ]ᴮ ι z                  →⟨ fst (Bxc θ' δ Δ (ι z)) ⟩
          Bx δ [ Δ +₊ (θ' +₊ δ) ]ᴮ ι z      →⟨ fst (Bxδ≈ᴮ[ε]Byη (Δ +₊ (θ' +₊ δ)) (ι z)) ⟩
          By η [ Δ +₊ (θ' +₊ δ) +₊ ε ]ᴮ ι z )
    e .funLim z zc _ θ = PT.map λ ((Δ , θ' , θ'') , Δ+[θ'+θ'']≡θ , B[Δ]xθ',zθ'') →
        (Δ +₊ (θ' +₊ δ) +₊ ε , η , θ'')
      , ( Δ+[θ'+δ]+ε+[η+θ'']≡Δ+[θ'+θ'']+[ε+[δ+η]] ℚCR ⟨ Δ ⟩₊ ⟨ θ' ⟩₊ _ _ _ _
        ∙ cong (ℚ._+ _) Δ+[θ'+θ'']≡θ)
      , (begin→[ B[Δ]xθ',zθ'' ]
          Bx θ' [ Δ ]ᴮ z θ''                  →⟨ fst (Bxc θ' δ Δ (z θ'')) ⟩
          Bx δ [ Δ +₊ (θ' +₊ δ) ]ᴮ z θ''      →⟨ fst (Bxδ≈ᴮ[ε]Byη _ (z θ'')) ⟩
          By η [ Δ +₊ (θ' +₊ δ) +₊ ε ]ᴮ z θ'' )
    e .is-prop z = isPropΠ λ θ → isProp→ (isPropBall (snd B⟨limᴿ[ By , Byc ],⟩) _ z)

private
  B⟨ι,⟩≈ᴮB⟨ι,⟩ : (x y : ⟨ M ⟩) (ε : ℚ₊) → x ≈[ ε ] y → B⟨ι x ,⟩ ≈ᴮ[ ε ] B⟨ι y ,⟩
  B⟨ι,⟩≈ᴮB⟨ι,⟩ x y ε x≈y δ z .fst = B⟨ι,⟩→B⟨ι,⟩ x y ε x≈y z δ
  B⟨ι,⟩≈ᴮB⟨ι,⟩ x y ε x≈y δ z .snd = B⟨ι,⟩→B⟨ι,⟩ y x ε (isSym≈ x y ε x≈y) z δ

  B⟨ι,⟩≈ᴮB⟨lim,⟩ : ∀ x By ε δ Byc
                → B⟨ι x ,⟩ ≈ᴮ[ ε ] By δ
                → B⟨ι x ,⟩ ≈ᴮ[ ε +₊ δ ] B⟨limᴿ[ By , Byc ],⟩
  fst (B⟨ι,⟩≈ᴮB⟨lim,⟩ x By ε δ Byc Bιx≈ᴮ[ε]Byδ η z) =
    B⟨ι,⟩→B⟨lim,⟩ x By ε δ Byc Bιx≈ᴮ[ε]Byδ z η
  snd (B⟨ι,⟩≈ᴮB⟨lim,⟩ x By ε δ Byc Bιx≈ᴮ[ε]Byδ η z) =
    B⟨lim,⟩→B⟨ι,⟩ x By ε δ Byc Bιx≈ᴮ[ε]Byδ z η

  B⟨lim,⟩≈ᴮB⟨lim,⟩ : ∀ Bx By ε δ η Bxc Byc
                  → (Bx δ) ≈ᴮ[ ε ] (By η)
                  → B⟨limᴿ[ Bx , Bxc ],⟩ ≈ᴮ[ ε +₊ (δ +₊ η) ] B⟨limᴿ[ By , Byc ],⟩
  fst (B⟨lim,⟩≈ᴮB⟨lim,⟩ Bx By ε δ η Bxc Byc Bxδ≈ᴮ[ε]Byη θ z) =
    B⟨lim,⟩→B⟨lim,⟩ Bx By ε δ η Bxc Byc Bxδ≈ᴮ[ε]Byη z θ
  snd (B⟨lim,⟩≈ᴮB⟨lim,⟩ Bx By ε δ η Bxc Byc Bxδ≈ᴮ[ε]Byη θ z) =
    subst (λ - → B[ θ +₊ (ε +₊ -) ]⟨limᴿ[ Bx , Bxc ], z ⟩)
          (ℚ₊≡ (ℚ.+Comm ⟨ η ⟩₊ ⟨ δ ⟩₊))
        ∘ B⟨lim,⟩→B⟨lim,⟩ By Bx ε η δ Byc Bxc (isSym≈ᴮ (Bx δ) (By η) ε Bxδ≈ᴮ[ε]Byη) z θ

BallsAt[Rec] : RecℭSym Balls (flip ∘ _≈ᴮ[_]_)
BallsAt[Rec] .funι     = B⟨ι_,⟩
BallsAt[Rec] .funLim   = B⟨limᴿ[_,_],⟩
BallsAt[Rec] .funEq    = isSeparated≈ᴮ
BallsAt[Rec] .ι︵ι     = B⟨ι,⟩≈ᴮB⟨ι,⟩
BallsAt[Rec] .ι︵lim   = B⟨ι,⟩≈ᴮB⟨lim,⟩
BallsAt[Rec] .lim︵lim = B⟨lim,⟩≈ᴮB⟨lim,⟩
BallsAt[Rec] .isSym︵  = isSym≈ᴮ
BallsAt[Rec] .isProp︵ = isProp≈ᴮ

-- Definition 3.13 (second part)
B⟨_,⟩ : ℭM → Balls
B⟨_,⟩ = RecℭSym.go BallsAt[Rec]

B[_]⟨_,_⟩ : ℚ₊ → ℭM → ℭM → Type ℓ''
B[_]⟨_,_⟩ = flip (fst ∘ B⟨_,⟩)

isNonExpanding∼→≈ᴮB⟨,⟩ : nonExpanding∼→≈ᴮ B⟨_,⟩
isNonExpanding∼→≈ᴮB⟨,⟩ = λ _ _ _ → RecℭSym.go∼ BallsAt[Rec]

-- Theorem 3.14
-- {-
module _ where

  B⟨ι,ι⟩β : ∀ {ε x y} → B[ ε ]⟨ ι x , ι y ⟩ ≡ x ≈[ ε ] y
  B⟨ι,ι⟩β = refl

  B⟨ι,lim⟩β : ∀ {ε x y yc} →
      B[ ε ]⟨ ι x , lim y yc ⟩
    ≡ (∃[ (Δ , δ) ∈ ℚ₊ × ℚ₊ ] (⟨ Δ +₊ δ ⟩₊ ≡ ⟨ ε ⟩₊) × B[ Δ ]⟨ ι x , y δ ⟩)
  B⟨ι,lim⟩β = refl

  B⟨lim,ι⟩β : ∀ {ε x y xc} →
      B[ ε ]⟨ lim x xc , ι y ⟩
    ≡ (∃[ (Δ , δ) ∈ ℚ₊ × ℚ₊ ] (⟨ Δ +₊ δ ⟩₊ ≡ ⟨ ε ⟩₊) × B[ Δ ]⟨ x δ , ι y ⟩)
  B⟨lim,ι⟩β = refl

  B⟨lim,lim⟩β : ∀ {ε x y xc yc} →
      B[ ε ]⟨ lim x xc , lim y yc ⟩
    ≡ (∃[ (Δ , δ , η) ∈ ℚ₊ × ℚ₊ × ℚ₊ ] (⟨ Δ +₊ (δ +₊ η) ⟩₊ ≡ ⟨ ε ⟩₊) × B[ Δ ]⟨ x δ , y η ⟩)
  B⟨lim,lim⟩β = refl
-- -}

∼→B : ∀ {x y ε} → x ∼[ ε ] y → B[ ε ]⟨ x , y ⟩
∼→B = Recℭ∼.go∼ r where opaque
  open Recℭ∼
  r : Recℭ∼ λ x y → B[_]⟨ x , y ⟩
  r .ι︵ι     x y ε             x≈y       = x≈y
  r .ι︵lim   x y ε δ yc _      B[ε]ιx,yδ = ∣ (ε , δ)     , refl , B[ε]ιx,yδ ∣₁
  r .lim︵ι   x y ε δ xc _      B[ε]xδ,ιy = ∣ (ε , δ)     , refl , B[ε]xδ,ιy ∣₁
  r .lim︵lim x y ε δ η xc yc _ B[ε]xδ,yη = ∣ (ε , δ , η) , refl , B[ε]xδ,yη ∣₁
  r .isProp︵ x y ε = IsBall.isPropBall (snd B⟨ x ,⟩) ε y

B→∼ : ∀ {x y ε} → B[ ε ]⟨ x , y ⟩ → x ∼[ ε ] y
B→∼ {x} {y} {ε} = Elimℭ-Prop2.go e x y ε where opaque
  open Elimℭ-Prop2

  e : Elimℭ-Prop2 λ x y → ∀ ε → B[ ε ]⟨ x , y ⟩ → x ∼[ ε ] y
  e .funιι   x y ε x≈y   = ι-ι x≈y
  e .funιLim x y yc IH ε = PT.rec (isProp∼ (ι x) ε (lim y yc))
    λ ((Δ , δ) , Δ+δ≡ε , B[Δ]ιx,yδ) →
    subst∼ _ _ Δ+δ≡ε (ι-lim δ yc (IH δ Δ B[Δ]ιx,yδ))
  e .funLimι   x xc y IH ε = PT.rec (isProp∼ (lim x xc) ε (ι y))
    λ ((Δ , δ) , Δ+δ≡ε , B[Δ]xδ,ιy) →
    subst∼ _ _ Δ+δ≡ε (lim-ι δ xc (IH δ Δ B[Δ]xδ,ιy))
  e .funLimLim x xc y yc IH ε = PT.rec (isProp∼ (lim x xc) ε (lim y yc))
    λ ((Δ , δ , η) , Δ+[δ+η]≡ε , B[Δ]xδ,yη) →
    subst∼ _ _ Δ+[δ+η]≡ε (lim-lim δ η xc yc (IH δ η Δ B[Δ]xδ,yη))
  e .is-prop   x y = isPropΠ λ ε → isProp→ (isProp∼ x ε y)

-- Theorem 3.15
∼≃B : ∀ {x y ε} → (x ∼[ ε ] y) ≃ B[ ε ]⟨ x , y ⟩
∼≃B {x} {y} {ε} =
  propBiimpl→Equiv (isProp∼ x ε y) (IsBall.isPropBall (snd B⟨ x ,⟩) ε y) ∼→B B→∼
