module HoTTReals.Data.Real.Base where

open import Cubical.Data.Bool
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Surjection
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ

-- HoTT Definition 11.3.2

data ℝ : Type

data Close : (ε : ℚ) → (0 < ε) → ℝ → ℝ → Type

syntax Close ε p x y = x ∼[ ε , p ] y

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

data Close where
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
  Σ ((q : ℚ) → A $ rational q)
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

inductionComputationRuleRational :
  {i j : Level}
  {A : ℝ → Type i}
  {B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j} →
  (α : Induction A B)
  (q : ℚ) →
  induction α (rational q) ≡ (fst α) q
inductionComputationRuleRational α x = refl

inductionComputationRuleLimit :
  {i j : Level}
  {A : ℝ → Type i}
  {B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j} →
  (α : Induction A B)
  (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x) →
  induction α (limit x φ) ≡ fst (snd α) x φ
                              (λ ε ψ → induction α (x ε ψ))
                              (λ δ ε ψ θ → induction-∼ α (φ δ ε ψ θ))
inductionComputationRuleLimit α x φ = refl

Inductionℝ : {i : Level} → (ℝ → Type i) → Type i
Inductionℝ {_} A = 
  ((q : ℚ) → A $ rational q) ×
  ((x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x) →
   ((ε : ℚ) (φ : 0 < ε) → A $ x ε φ) →
   A $ limit x φ) ×
  ((u v : ℝ) → (φ : (ε : ℚ) (ψ : 0 < ε) → u ∼[ ε , ψ ] v)
   (a : A u) (b : A v) →
   PathP (λ i → A (path u v φ i)) a b)

inductionℝ : {i : Level} {A : ℝ → Type i} →
             Inductionℝ A →
             (x : ℝ) → A x
inductionℝ α@(fRational , fLimit , fPath) (rational q) =
  fRational q
inductionℝ α@(fRational , fLimit , fPath) (limit x φ) =
  fLimit (λ ε ψ → x ε ψ) (λ δ ε ψ θ → φ δ ε ψ θ) (λ ε ψ → inductionℝ α (x ε ψ))
inductionℝ α@(fRational , fLimit , fPath) (path u v φ i) =
  fPath u v φ (inductionℝ α u) (inductionℝ α v) i

InductionProposition : {i : Level} → (ℝ → Type i) → Type i
InductionProposition {_} A =
  ((q : ℚ) → A $ rational q) ×
  ((x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x) →
   ((ε : ℚ) (ψ : 0 < ε) → A $ x ε ψ) →
   A $ limit x φ) ×
  ((u : ℝ) → isProp (A u))

inductionProposition : {i : Level} {A : ℝ → Type i} →
                       InductionProposition A →
                       (x : ℝ) → A x
inductionProposition α@(fRational , fLimit , φ) (rational q) =
  fRational q
inductionProposition α@(fRational , fLimit , φ) (limit x ψ) =
  fLimit (λ ε θ → x ε θ)
         (λ δ ε θ ω → ψ δ ε θ ω)
         (λ ε θ → inductionProposition α (x ε θ))
inductionProposition α@(fRational , fLimit , φ) (path u v ψ i) =
  isProp→PathP (λ j → φ (path u v ψ j))
               (inductionProposition α u)
               (inductionProposition α v)
               i

Induction∼ :
  {i : Level} →
  ({x y : ℝ} → {ε : ℚ} {φ : 0 < ε} → x ∼[ ε , φ ] y → Type i) →
  Type i
Induction∼ B =
  ((q r ε : ℚ) (φ : 0 < ε) →
   (ψ : - ε < q - r) → (θ : q - r < ε) →
   B (rationalRational q r ε φ ψ θ)) ×
  ((q δ ε : ℚ) (φ : 0 < δ) (ψ : 0 < ε) (θ : 0 < ε - δ) →
   (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y) →
   (π : rational q ∼[ ε - δ , θ ] y δ φ) →
   B π → B (rationalLimit q ε δ ψ φ θ y ω π)) ×
  (((x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
   (r δ ε : ℚ) (ψ : 0 < δ) (θ : 0 < ε) (ω : 0 < ε - δ)
   (π : x δ ψ ∼[ ε - δ , ω ] rational r) →
   B π → B (limitRational x φ r ε δ θ ψ ω π))) ×
  (((x y : (ε : ℚ) → 0 < ε → ℝ)
   (φ : CauchyApproximation x) (ψ : CauchyApproximation y)
   (ε δ η : ℚ) (θ : 0 < ε) (ω : 0 < δ) (π : 0 < η) (ρ : 0 < ε - (δ + η))
   (σ : x δ ω ∼[ ε - (δ + η) , ρ ] y η π) →
   B σ → B (limitLimit x y φ ψ ε δ η θ ω π ρ σ))) ×
  -- TODO: Can't tell if HoTT book omitted this on accident or if there really
  -- is a way to consider non propositional `B`s
  ((u v : ℝ) (ε : ℚ) (φ : 0 < ε) (ψ : u ∼[ ε , φ ] v) → isProp (B ψ))

-- HoTT 387
induction∼ :
  {i : Level}
  {B : {x y : ℝ} → {ε : ℚ} {φ : 0 < ε} → x ∼[ ε , φ ] y → Type i} →
  Induction∼ B →
  {x y : ℝ} {ε : ℚ} {φ : 0 < ε} (ρ : x ∼[ ε , φ ] y) → B ρ
induction∼ {B = B} α@(φ , ψ , θ , ω , π) (rationalRational q r ε ρ σ τ) =
  φ q r ε ρ σ τ
induction∼ {B = B} α@(φ , ψ , θ , ω , π) (rationalLimit q ε δ ρ σ τ y υ β) =
  ψ q δ ε σ ρ τ y υ β (induction∼ {B = B} α β)
induction∼ {B = B} α@(φ , ψ , θ , ω , π) (limitRational x ρ r ε δ σ τ υ β) =
  θ x ρ r δ ε τ σ υ β (induction∼ {B = B} α β)
induction∼ {B = B} α@(φ , ψ , θ , ω , π) (limitLimit x y ρ σ ε δ η τ υ β γ ζ) =
  ω x y ρ σ ε δ η τ υ β γ ζ (induction∼ {B = B} α ζ)
induction∼ {B = B} α@(φ , ψ , θ , ω , π) (squash u v ε ρ σ σ' i) =
  isProp→PathP
    (λ j → π u v ε ρ (squash u v ε ρ σ σ' j))
    (induction∼ {B = B} α σ)
    (induction∼ {B = B} α σ')
    i

-- HoTT Lemma 11.3.8
closeReflexive :
  BinaryRelation.isRefl (λ x y → (ε : ℚ) (φ : 0 < ε) → x ∼[ ε , φ ] y)
closeReflexive u = inductionProposition (ψ , θ , ω) u
  where
  ψ : ((q : ℚ) → ((ε : ℚ) (φ : 0 < ε) → rational q ∼[ ε , φ ] rational q))
  ψ q ε φ = rationalRational
          q q ε φ
          (let θ : q - q ≡ - 0
               θ = q - q ≡⟨ +InvR q ⟩ 0
                         ≡⟨ refl ⟩ - 0 ∎

               ω : - ε < - 0
               ω = <antitone- {x = 0} {y = ε} φ
           in subst (λ ?x → - ε < ?x) (sym θ) ω)
          (subst (λ ?x → ?x < ε) (sym (+InvR q)) φ)

  θ : (x : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation x) →
      ((δ : ℚ) (π : 0 < δ) → ((ε : ℚ) (ρ : 0 < ε) → x δ π ∼[ ε , ρ ] x δ π)) →
      ((ε : ℚ) (π : 0 < ε) → limit x ω ∼[ ε , π ] limit x ω)
  θ x ω π ε ρ =
    let σ : ¬ 3 ≡ 0
        σ = toWitnessFalse {Q = discreteℚ 3 0} tt

        τ' : 0 < 3 [ σ ]⁻¹
        τ' = toWitness {Q = <Dec 0 (3 [ σ ]⁻¹)} tt

        τ : 0 < ε / 3 [ σ ]
        -- TODO: Perphaps pull out into lemma for division
        τ = subst (λ ?x → ?x < (ε / 3 [ σ ]))
                  (·AnnihilR (3 [ σ ]⁻¹))
                  (<-·o 0 ε (3 [ σ ]⁻¹) τ' ρ)

        υ' : (ε / 3 [ σ ] + ε / 3 [ σ ]) ≡ (2 / 3 [ σ ]) · ε
        υ' =
            ε / 3 [ σ ] + ε / 3 [ σ ]
              ≡⟨ sym (·DistR+ ε ε (3 [ σ ]⁻¹)) ⟩
            (ε + ε) · (3 [ σ ]⁻¹)
              ≡⟨ cong (λ ?x → ?x · (3 [ σ ]⁻¹)) (2·≡self+ ε) ⟩
            (2 · ε) · (3 [ σ ]⁻¹)
              ≡⟨ sym (·Assoc 2 ε (3 [ σ ]⁻¹)) ⟩
            2 · (ε · (3 [ σ ]⁻¹))
              ≡⟨ cong (λ ?x → 2 · ?x) (·Comm ε (3 [ σ ]⁻¹)) ⟩
            2 · ((3 [ σ ]⁻¹) · ε)
              ≡⟨ ·Assoc 2 (3 [ σ ]⁻¹) ε ⟩
            (2 · (3 [ σ ]⁻¹)) · ε
              ≡⟨ refl ⟩
            (2 / 3 [ σ ]) · ε ∎

        υ : ε - (ε / 3 [ σ ] + ε / 3 [ σ ]) ≡ ε / 3 [ σ ]
        υ =
          ε - (ε / 3 [ σ ] + ε / 3 [ σ ])
            ≡⟨ cong (λ ?x → ε - ?x) υ' ⟩
          ε + (- ((2 / 3 [ σ ]) · ε))
            ≡⟨ cong (λ ?x → ε + ?x) (-·≡-· (2 / 3 [ σ ]) ε) ⟩
          ε + ((- 2) / 3 [ σ ]) · ε
            ≡⟨ cong (λ ?x → ?x + ((- 2) / 3 [ σ ]) · ε) (sym (·IdL ε)) ⟩
          1 · ε + ((- 2) / 3 [ σ ]) · ε
            ≡⟨ sym (·DistR+ 1 ((- 2) / 3 [ σ ]) ε) ⟩
          (1 - (2 / 3 [ σ ])) · ε
            ≡⟨ refl ⟩
          (3 [ σ ]⁻¹) · ε
            ≡⟨ ·Comm (3 [ σ ]⁻¹) ε ⟩
          ε / 3 [ σ ] ∎

        ι : 0 < ε - (ε / 3 [ σ ] + ε / 3 [ σ ])
        ι = subst (λ ?x → 0 < ?x) (sym υ) τ

        κ : Close (ε - ((ε / 3 [ σ ]) + (ε / 3 [ σ ]))) ι
                  (x (ε / 3 [ σ ]) τ) (x (ε / 3 [ σ ]) τ)
        κ = π (ε / 3 [ σ ]) τ (ε - ((ε / 3 [ σ ]) + (ε / 3 [ σ ]))) ι
    in limitLimit
         x x ω ω
         ε (ε / 3 [ σ ]) (ε / 3 [ σ ]) ρ τ τ ι
         κ

  ω : (u : ℝ) → isProp ((ε : ℚ) (π : 0 < ε) → u ∼[ ε , π ] u)
  ω u = isPropΠ2 (squash u u)

-- HoTT Theorem 11.3.9
ℝ-isSet : isSet ℝ
ℝ-isSet = reflPropRelImpliesIdentity→isSet
            (λ x y → (ε : ℚ) (φ : 0 < ε) → x ∼[ ε , φ ] y)
            closeReflexive
            (λ x y → isPropΠ2 (squash x y))
            (λ {x} {y} → path x y)

-- HoTT Lemma 11.3.10
limitSurjective : isSurjection (uncurry limit)
limitSurjective = inductionProposition (φ , ψ , θ)
  where
  φ : (q : ℚ) → ∥ fiber (uncurry limit) (rational q) ∥₁
  φ q = ∣ ((λ ε _ → rational q) , ψ) ,
          path (limit (λ ε _ → rational q) ψ) (rational q) σ ∣₁
    where
    ψ : CauchyApproximation (λ ε _ → rational q)
    ψ ε δ θ ω =
      let π : 0 < ε + δ
          π = +0< {x = ε} {y = δ} θ ω

          π' : (q - q) < ε + δ
          π' = subst (λ ?x → ?x < ε + δ) (sym (+InvR q)) π

          ρ : - (ε + δ) < (q - q)
          ρ = subst (λ ?x → - (ε + δ) < ?x)
                    (sym (+InvR q))
                    (<antitone- {x = 0} {y = ε + δ} π)
      in rationalRational q q (ε + δ) (+0< {x = ε} {y = δ} θ ω) ρ π'

    σ : (ε : ℚ) (τ : 0 < ε) →
        Close ε τ (limit (λ ε₁ _ → rational q) ψ) (rational q)
    σ ε τ =
      let
        υ : ¬ 2 ≡ 0
        υ = toWitnessFalse {Q = discreteℚ 2 0} tt

        υ' : 0 < 2 [ υ ]⁻¹
        υ' = toWitness {Q = <Dec 0 (2 [ υ ]⁻¹)} tt

        α : 0 < ε / 2 [ υ ]
        α = subst (λ ?x → ?x < ε / 2 [ υ ])
                  (·AnnihilR (2 [ υ ]⁻¹))
                  (<-·o 0 ε (2 [ υ ]⁻¹) υ' τ)

        β = ε - (ε / 2 [ υ ]) ≡ ε / 2 [ υ ]
        β =
          ε - (ε / 2 [ υ ])
            ≡⟨ cong (λ ?x → ?x - (ε / 2 [ υ ])) (sym (·IdR ε)) ⟩
          (ε · 1) - (ε · 2 [ υ ]⁻¹)
            ≡⟨ cong (λ ?x → (ε · 1) + ?x) (-·≡·- ε (2 [ υ ]⁻¹)) ⟩
          (ε · 1) + (ε · (- (2 [ υ ]⁻¹)))
            ≡⟨ sym (·DistL+ ε 1 (- (2 [ υ ]⁻¹))) ⟩
          ε · (1 + (- (2 [ υ ]⁻¹)))
            ≡⟨ refl ⟩
          ε / 2 [ υ ] ∎

        α' : 0 < ε - (ε / 2 [ υ ])
        α' = subst (λ ?x → 0 < ?x) (sym β) α

        γ : q - q < ε - (ε / 2 [ υ ])
        γ = subst (λ ?x → ?x < ε - (ε / 2 [ υ ])) (sym (+InvR q)) α'

        γ' : - (ε - (ε / 2 [ υ ])) < q - q
        γ' =
          subst (λ ?x → - (ε - (ε / 2 [ υ ])) < ?x)
                (sym (+InvR q))
                (<antitone- {x = 0} {y = ε - (ε / 2 [ υ ])} α')
      in limitRational
           (λ ε _ → rational q) ψ
           q
           ε (ε / 2 [ υ ])
           τ α
           α' (rationalRational q q (ε - (ε / 2 [ υ ])) α' γ' γ)

  ψ : (x : (ε : ℚ) → 0 < ε → ℝ) (θ : CauchyApproximation x) →
      ((ε : ℚ) (ψ : 0 < ε) → ∥ fiber (uncurry limit) (x ε ψ) ∥₁) →
      ∥ fiber (uncurry limit) (limit x θ) ∥₁
  ψ x θ _ = ∣ ((x , θ) , refl) ∣₁

  θ : (x : ℝ) → isProp ∥ fiber (uncurry limit) x ∥₁
  θ _ = isPropPropTrunc

-- TODO: HoTT Lemma 11.3.11

-- HoTT Lemma 11.3.12
closeSymmetric :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v → v ∼[ ε , φ ] u
closeSymmetric _ _ _ _ =
  induction∼ {B = λ {u} {v} {ε} {φ} _ → (v ∼[ ε , φ ] u)} (φ , ψ , θ , ω , χ)
  where
  φ : (q r ε : ℚ) (ψ : 0 < ε) →
      (- ε) < q - r → q - r < ε →
      (rational r) ∼[ ε , ψ ] (rational q)
  φ q r ε ψ ω θ = rationalRational r q ε ψ χ π
    where
    α : - (q - r) ≡ r - q
    α = - (q - r)
          ≡⟨ negateSubtract q r ⟩
        - q + r
          ≡⟨ +Comm (- q) r ⟩
        r - q ∎

    χ : - ε < r - q
    χ = subst (λ ?x → - ε < ?x) α (<antitone- {x = q - r} {y = ε} θ)

    π : r - q < ε 
    π = subst2 (λ ?y ?x → ?y < ?x)
               α (-Invol ε)
               (<antitone- {x = - ε} {y = q - r} ω)

  ψ : (q δ ε : ℚ) (φ : 0 < δ) (ψ : 0 < ε) (θ : 0 < ε - δ)
      (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y) →
      (rational q) ∼[ (ε - δ) , θ ] (y δ φ) →
      (y δ φ) ∼[ (ε - δ) , θ ] (rational q) →
      (limit y ω) ∼[ ε , ψ ] (rational q)
  ψ q δ ε φ ψ θ y ω π ρ = limitRational y ω q ε δ ψ φ θ ρ

  θ : (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
      (r δ ε : ℚ) (ψ : 0 < δ) (θ : 0 < ε) (ω : 0 < ε - δ) →
      (x δ ψ) ∼[ (ε - δ) , ω ] (rational r) →
      (rational r) ∼[ (ε - δ) , ω ] (x δ ψ) →
      (rational r) ∼[ ε , θ ]  (limit x φ)
  θ x φ r δ ε ψ θ ω π ρ = rationalLimit r ε δ θ ψ ω x φ ρ

  ω : (x y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
      (ψ : CauchyApproximation y) (ε δ η : ℚ) (θ : 0 < ε) (ω : 0 < δ)
      (π : 0 < η) (ρ : 0 < ε - (δ + η)) →
      (x δ ω) ∼[ ε - (δ + η) , ρ ] (y η π) →
      (y η π) ∼[ ε - (δ + η) , ρ ] (x δ ω) →
      (limit y ψ) ∼[ ε , θ ] (limit x φ)
  ω x y φ ψ ε δ η θ ω π ρ σ τ =
    let υ : Σ (0 < ε - (η + δ)) (λ α → y η π ∼[ ε - (η + δ) , α ] x δ ω)
        υ = subst (λ ?x → Σ (0 < (ε - ?x))
                            (λ α → y η π ∼[ ε - ?x , α ] x δ ω))
                  (+Comm δ η)
                  (ρ , τ)
    in limitLimit y x ψ φ ε η δ θ π ω (fst υ) (snd υ)

  χ : (u v : ℝ) (ε : ℚ) (φ : 0 < ε) (ψ : u ∼[ ε , φ ] v) →
      isProp (v ∼[ ε , φ ] u)
  χ u v ε φ ψ = squash v u ε φ

closeSymmetric' :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v ≃ v ∼[ ε , φ ] u
closeSymmetric' u v ε φ =
  propBiimpl→Equiv
    (squash u v ε φ)
    (squash v u ε φ)
    (closeSymmetric u v ε φ)
    (closeSymmetric v u ε φ)

closeSymmetric'' :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v ≡ v ∼[ ε , φ ] u
closeSymmetric'' u v ε φ = ua (closeSymmetric' u v ε φ)
