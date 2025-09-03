module HoTTReals.Data.Real.Base where

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import HoTTReals.Data.Rationals.Order as ℚ

-- HoTT Definition 11.3.2

data ℝ : Type

data Equivalent-ℝ : (ε : ℚ) → (0 < ε) → ℝ → ℝ → Type

syntax Equivalent-ℝ ε p x y = x ∼[ ε , p ] y

-- HoTT Definition 11.2.10
CauchyApproximation : ((ε : ℚ) → 0 < ε → ℝ) → Type ℓ-zero
CauchyApproximation x =
  ((δ ε : ℚ) (p : 0 < δ) (q : 0 < ε) →
   (x δ p) ∼[ δ + ε , +0< {x = δ} {y = ε} p q ] (x ε q))

data ℝ where
  rational : ℚ → ℝ
  limit : (x : (ε : ℚ) → 0 < ε → ℝ) →
          CauchyApproximation x →
          ℝ
  path : (x y : ℝ) →
         ((ε : ℚ) (p : 0 < ε) → x ∼[ ε , p ] y) →
         x ≡ y

data Equivalent-ℝ where
  rationalRational :
    (q r ε : ℚ) (φ : 0 < ε) →
    - ε < q - r → q - r < ε →
    rational q ∼[ ε , φ ] rational r
  rationalLimit :
    (q ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) (θ : 0 < ε - δ)
    (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y) →
    rational q ∼[ ε - δ , θ ] (y δ ψ) →
    rational q ∼[ ε , φ ] (limit y ω)
  limitRational :
    (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
    (r ε δ : ℚ) (ψ : 0 < ε) (θ : 0 < δ) (ω : 0 < ε - δ) →
    (x δ θ) ∼[ ε - δ , ω ] rational r →
    limit x φ ∼[ ε , ψ ] rational r 
  limitLimit :
    (x y : (ε : ℚ) → 0 < ε → ℝ)
    (φ : CauchyApproximation x) (ψ : CauchyApproximation y)
    (ε δ η : ℚ) (θ : 0 < ε) (ω : 0 < δ) (π : 0 < η) (ρ : 0 < ε - (δ + η)) →
    (x δ ω) ∼[ ε - (δ + η) , ρ ] (y η π) →
    limit x φ ∼[ ε , θ ] limit y ψ
  squash :
    (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → isProp $ u ∼[ ε , φ ] v

-- HoTT 385, dependent Cauchy approximation
CauchyApproximation' :
  {i j : Level}
  (A : ℝ → Type i)
  (B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j)
  (x : (ε : ℚ) → 0 < ε → ℝ) →
  CauchyApproximation x →
  ((ε : ℚ) (p : 0 < ε) → A $ x ε p) →
  Type j
CauchyApproximation' A B x p a =
  (δ ε : ℚ) (q : 0 < δ) (r : 0 < ε) →
  B (a δ q) (a ε r) (p δ ε q r)

Induction :
  {i j : Level}
  (A : ℝ → Type i)
  (B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j) →
  Type (ℓ-max i j)
Induction A B =
  Σ ((x : ℚ) → A $ rational x)
  (λ fRational →
  Σ ((x : (ε : ℚ) → 0 < ε → ℝ)
     (φ : CauchyApproximation x)
     (a : (ε : ℚ) (ψ : 0 < ε) → A $ x ε ψ) →
     CauchyApproximation' A B x φ a →
     A $ limit x φ)
  (λ fLimit →
  ((u v : ℝ) → (φ : (ε : ℚ) (ψ : 0 < ε) → u ∼[ ε , ψ ] v)
   (a : A u) (b : A v) →
   ((ε : ℚ) (ψ : 0 < ε) → B a b (φ ε ψ)) →
   PathP (λ i → A (path u v φ i)) a b) ×
  ((q r ε : ℚ) (φ : 0 < ε) →
   (ψ : - ε < q - r) → (θ : q - r < ε) →
   B (fRational q) (fRational r) (rationalRational q r ε φ ψ θ)) ×
  ((q δ ε : ℚ) (φ : 0 < δ) (ψ : 0 < ε) (θ : 0 < ε - δ) →
   (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y)
   (b : (ε : ℚ) (ρ : 0 < ε) → A $ y ε ρ) (π : CauchyApproximation' A B y ω b)
   (ρ : rational q ∼[ ε - δ , θ ] y δ φ) →
   B (fRational q) (b δ φ) ρ →
   B (fRational q) (fLimit y ω b π) (rationalLimit q ε δ ψ φ θ y ω ρ)) ×
  ((x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
   (r δ ε : ℚ) (ψ : 0 < δ) (θ : 0 < ε) (ω : 0 < ε - δ)
   (a : (ε : ℚ) (π : 0 < ε) → A $ x ε π) (π : CauchyApproximation' A B x φ a)
   (ρ : x δ ψ ∼[ ε - δ , ω ] rational r) →
   B (a δ ψ) (fRational r) ρ →
   B (fLimit x φ a π) (fRational r) (limitRational x φ r ε δ θ ψ ω ρ)) ×
  ((x y : (ε : ℚ) → 0 < ε → ℝ)
   (φ : CauchyApproximation x) (ψ : CauchyApproximation y)
   (ε δ η : ℚ) (θ : 0 < ε) (ω : 0 < δ) (π : 0 < η) (ρ : 0 < ε - (δ + η))
   (a : (ε : ℚ) (σ : 0 < ε) → A $ x ε σ)
   (b : (ε : ℚ) (σ : 0 < ε) → A $ y ε σ)
   (σ : CauchyApproximation' A B x φ a)
   (τ : CauchyApproximation' A B y ψ b)
   (υ : x δ ω ∼[ ε - (δ + η) , ρ ] y η π) →
   B (a δ ω) (b η π) υ →
   B (fLimit x φ a σ)
     (fLimit y ψ b τ)
     (limitLimit x y φ ψ ε δ η θ ω π ρ υ)) ×
  (((u v : ℝ) →
   (ε : ℚ) (φ : 0 < ε) →
   (a : A u) (b : A v) →
   (ψ : u ∼[ ε , φ ] v) →
   isProp (B a b ψ)))))

induction :
  {i j : Level}
  {A : ℝ → Type i}
  {B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j} →
  Induction A B →
  (x : ℝ) → A x

induction-∼ :
  {i j : Level}
  {A : ℝ → Type i}
  {B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j}
  (q : Induction A B)
  {x y : ℝ} {ε : ℚ} {p : 0 < ε} (ζ : x ∼[ ε , p ] y) →
  B (induction {A = A} {B = B} q x) (induction {A = A} {B = B} q y) ζ

induction α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π) (rational q) =
  fRational q
induction α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π) (limit x ρ) =
  fLimit
    x ρ
    (λ ε σ → induction α (x ε σ))
    (λ δ ε τ υ → induction-∼ α (ρ δ ε τ υ))
induction α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π) (path u v ρ i) =
  fPath u v ρ (induction α u) (induction α v) (λ ε σ → induction-∼ α (ρ ε σ)) i

induction-∼ α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π)
  (rationalRational q r ε ρ σ τ) = φ q r ε ρ σ τ
induction-∼ α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π)
  (rationalLimit q ε δ ρ σ τ y υ ι) =
    ψ q δ ε σ ρ τ y υ
      (λ ε κ → induction α (y ε κ))
      (λ δ ε κ μ → induction-∼ α (υ δ ε κ μ))
      ι
      (induction-∼ α ι)
induction-∼ α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π)
  (limitRational x ρ r ε δ σ τ υ ι) =
    θ x ρ r δ ε τ σ υ
      (λ ε κ → induction α (x ε κ))
      (λ δ ε κ μ → induction-∼ α (ρ δ ε κ μ))
      ι
      (induction-∼ α ι)
induction-∼ α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π)
  (limitLimit x y ρ σ ε δ η τ υ ι κ μ) =
    ω x y ρ σ ε δ η τ υ ι κ
      (λ ε ν → induction α (x ε ν))
      (λ ε ν → induction α (y ε ν))
      (λ δ ε ν ξ → induction-∼ α (ρ δ ε ν ξ))
      (λ δ ε ν ξ → induction-∼ α (σ δ ε ν ξ))
      μ
      (induction-∼ α μ)
induction-∼ α@(fRational , fLimit , fPath , φ , ψ , θ , ω , π)
  (squash u v ε ρ ζ ζ' i) =
    isProp→PathP
      (λ j → π u v ε ρ (induction α u) (induction α v) (squash u v ε ρ ζ ζ' j))
      (induction-∼ α ζ)
      (induction-∼ α ζ')
      i

inductionComputationRule :
  {i j : Level}
  {A : ℝ → Type i}
  {B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j} →
  (α : Induction A B)
  (x : ℚ) →
  induction α (rational x) ≡ (fst α) x
inductionComputationRule α x = refl

induction-∼-computationRule :
  {i j : Level}
  {A : ℝ → Type i}
  {B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j} →
  (α : Induction A B)
  (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x) →
  induction α (limit x φ) ≡ fst (snd α) x φ
                              (λ ε ψ → induction α (x ε ψ))
                              (λ δ ε ψ θ → induction-∼ α (φ δ ε ψ θ))
induction-∼-computationRule α x φ = refl

-- TODO:
-- equivalent-ℝ-reflexive : (u : ℝ) (ε : ℚ) (p : 0 < ε) → u ∼[ ε , p ] u
-- equivalent-ℝ-reflexive (rational x) ε p = {!!}
-- equivalent-ℝ-reflexive (limit x x₁) ε p = {!!}
-- equivalent-ℝ-reflexive (path u u₁ x i) ε p = {!!}

-- TODO: Type for lemma 1
