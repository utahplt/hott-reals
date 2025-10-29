module HoTTReals.Data.Real.Base where

open import Cubical.Data.Bool as Bool using ()
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
open import HoTTReals.Logic

-- HoTT Definition 11.3.2

data ℝ : Type

data Close : (ε : ℚ) → (0 < ε) → ℝ → ℝ → Type

syntax Close ε p x y = x ∼[ ε , p ] y

-- HoTT Definition 11.2.10
CauchyApproximation : ((ε : ℚ) → 0 < ε → ℝ) → Type ℓ-zero
CauchyApproximation x =
  ((δ ε : ℚ) (p : 0 < δ) (q : 0 < ε) →
   (x δ p) ∼[ δ + ε , 0<+' {x = δ} {y = ε} p q ] (x ε q))

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
    (ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp $ u ∼[ ε , φ ] v

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
  (squash ε ρ u v ζ ζ' i) =
    isProp→PathP
      (λ j → π u v ε ρ (induction α u) (induction α v) (squash ε ρ u v ζ ζ' j))
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
induction∼ {B = B} α@(φ , ψ , θ , ω , π) (squash ε ρ u v σ σ' i) =
  isProp→PathP
    (λ j → π u v ε ρ (squash ε ρ u v σ σ' j))
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
        σ = Bool.toWitnessFalse {Q = discreteℚ 3 0} tt

        τ' : 0 < 3 [ σ ]⁻¹
        τ' = Bool.toWitness {Q = <Dec 0 (3 [ σ ]⁻¹)} tt

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
  ω u = isPropΠ2 (λ ε π → squash ε π u u)

-- HoTT Theorem 11.3.9
ℝ-isSet : isSet ℝ
ℝ-isSet = reflPropRelImpliesIdentity→isSet
            (λ x y → (ε : ℚ) (φ : 0 < ε) → x ∼[ ε , φ ] y)
            closeReflexive
            (λ x y → isPropΠ2 (λ ε π → squash ε π x y))
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
          π = 0<+' {x = ε} {y = δ} θ ω

          π' : (q - q) < ε + δ
          π' = subst (λ ?x → ?x < ε + δ) (sym (+InvR q)) π

          ρ : - (ε + δ) < (q - q)
          ρ = subst (λ ?x → - (ε + δ) < ?x)
                    (sym (+InvR q))
                    (<antitone- {x = 0} {y = ε + δ} π)
      in rationalRational q q (ε + δ) (0<+' {x = ε} {y = δ} θ ω) ρ π'

    σ : (ε : ℚ) (τ : 0 < ε) →
        Close ε τ (limit (λ ε₁ _ → rational q) ψ) (rational q)
    σ ε τ =
      let
        υ : ¬ 2 ≡ 0
        υ = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt

        υ' : 0 < 2 [ υ ]⁻¹
        υ' = Bool.toWitness {Q = <Dec 0 (2 [ υ ]⁻¹)} tt

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
  χ u v ε φ ψ = squash ε φ v u

closeSymmetric' :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v ≃ v ∼[ ε , φ ] u
closeSymmetric' u v ε φ =
  propBiimpl→Equiv
    (squash ε φ u v)
    (squash ε φ v u)
    (closeSymmetric u v ε φ)
    (closeSymmetric v u ε φ)

closeSymmetric'' :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v ≡ v ∼[ ε , φ ] u
closeSymmetric'' u v ε φ = ua (closeSymmetric' u v ε φ)

CauchyApproximation'' : 
  {i j : Level}
  (A : Type i)
  (B : (a b : A) → (ε : ℚ) → 0 < ε → Type j) →
  (f : (ε : ℚ) → 0 < ε → A) →
  Type j
CauchyApproximation'' A B f =
  (ε δ : ℚ) (ψ : 0 < ε) (θ : 0 < δ) →
  B (f ε ψ) (f δ θ) (ε + δ) (0<+' {x = ε} {y = δ} ψ θ)

-- HoTT 388 Enhanced principle of recursion
Recursion :
  {i j : Level}
  (A : Type i) →
  ((a b : A) → (ε : ℚ) → 0 < ε → Type j) →
  Type (ℓ-max i j)
Recursion A B =
  Σ (ℚ → A)
  (λ fRational →
  Σ ((f : (ε : ℚ) → 0 < ε → A) →
     CauchyApproximation'' A B f →
     A)
  (λ fLimit →
  ((a b : A) → ((ε : ℚ) (φ : 0 < ε) → B a b ε φ) → a ≡ b) ×
  ((q r ε : ℚ) (φ : 0 < ε) →
   - ε < q - r → q - r < ε →
   B (fRational q) (fRational r) ε φ) ×
  ((q ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) (θ : 0 < ε - δ) →
   (f : (ε : ℚ) → 0 < ε → A) (ω : CauchyApproximation'' A B f) →
   B (fRational q) (f δ ψ) (ε - δ) θ →
   B (fRational q) (fLimit f ω) ε φ) ×
  ((f : (ε : ℚ) → 0 < ε → A) (φ : CauchyApproximation'' A B f) →
   (r ε δ : ℚ) (ψ : 0 < ε) (θ : 0 < δ) (ω : 0 < ε - δ) →
   B (f δ θ) (fRational r) (ε - δ) ω →
   B (fLimit f φ) (fRational r) ε ψ) ×
  ((f g : (ε : ℚ) → 0 < ε → A)
   (φ : CauchyApproximation'' A B f) →
   (ψ : CauchyApproximation'' A B g) →
   (ε δ η : ℚ) (θ : 0 < ε) (ω : 0 < δ) (χ : 0 < η) (π : 0 < ε - (δ + η)) →
   B (f δ ω) (g η χ) (ε - (δ + η)) π →
   B (fLimit f φ) (fLimit g ψ) ε θ) ×
  ((a b : A) (ε : ℚ) (φ : 0 < ε) → isProp $ B a b ε φ)))

recursion :
  {i j : Level}
  {A : Type i} →
  {B : (a b : A) → (ε : ℚ) → 0 < ε → Type j} →
  Recursion A B →
  (ℝ → A)

recursion∼ :
  {i j : Level}
  {A : Type i} →
  {B : (a b : A) → (ε : ℚ) → 0 < ε → Type j} →
  (α : Recursion A B) →
  {u v : ℝ} {ε : ℚ} {p : 0 < ε} →
  u ∼[ ε , p ] v →
  B (recursion {A = A} {B = B} α u) (recursion {A = A} {B = B} α v) ε p

recursion α@(fRational , fLimit , φ , ψ , θ , ω , χ , π) (rational x) =
  fRational x
recursion α@(fRational , fLimit , φ , ψ , θ , ω , χ , π) (limit x ρ) =
  fLimit (λ ε φ → recursion α (x ε φ))
         (λ ε δ φ ψ → recursion∼ α (ρ ε δ φ ψ))
recursion α@(fRational , fLimit , φ , ψ , θ , ω , χ , π) (path u v ρ i) =
  φ (recursion α u) (recursion α v) (λ ε φ → recursion∼ α (ρ ε φ)) i

recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (rationalRational q r ε ρ σ τ) = ψ q r ε ρ σ τ
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (rationalLimit q ε δ ρ σ τ y υ ι) =
  θ q ε δ ρ σ τ
    (λ ε κ → recursion α (y ε κ))
    (λ ε δ κ μ → recursion∼ α (υ ε δ κ μ))
    (recursion∼ α ι)
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (limitRational x ρ r ε δ σ τ υ ι) =
  ω (λ ε κ → recursion α (x ε κ))
    (λ ε δ κ μ → recursion∼ α (ρ ε δ κ μ))
    r ε δ σ τ υ (recursion∼ α ι)
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (limitLimit x y ρ σ ε δ η τ υ ι κ μ) =
  χ (λ ε ν → recursion α (x ε ν))
    (λ ε ν → recursion α (y ε ν))
    (λ ε δ ν ξ → recursion∼ α (ρ ε δ ν ξ))
    (λ ε δ ν ξ → recursion∼ α (σ ε δ ν ξ))
    ε δ η τ υ ι κ (recursion∼ α μ)
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (squash ε ρ u v ζ ζ' i) =
  isProp→PathP (λ j → π (recursion α u) (recursion α v) ε ρ)
               (recursion∼ α ζ)
               (recursion∼ α ζ')
               i

-- HoTT Definition 11.3.14
Lipschitzℚ : (f : ℚ → ℝ) (L : ℚ) → 0 < L → Type ℓ-zero
Lipschitzℚ f L φ =
  (q r ε : ℚ) (ψ : 0 < ε) →
  ∣ q - r ∣ < ε →
  f q ∼[ L · ε , 0<· {x = L} {y = ε} φ ψ ] f r

Lipschitzℝ : (f : ℝ → ℝ) (L : ℚ) → 0 < L → Type ℓ-zero
Lipschitzℝ f L φ =
  (u v : ℝ)
  (ε : ℚ) (ψ : 0 < ε) →
  u ∼[ ε , ψ ] v →
  f u ∼[ L · ε , 0<· {x = L} {y = ε} φ ψ ] f v

-- HoTT Lemma 11.3.16
closeLimit : (u : ℝ) (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
             (ε δ : ℚ) (ψ : 0 < ε) (ω : 0 < δ) →
             u ∼[ ε , ψ ] (y δ ω) →
             u ∼[ ε + δ , 0<+' {x = ε} {y = δ} ψ ω ] (limit y φ)
closeLimit = {!!}

closeLimit' : (u : ℝ) (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
              (ε δ : ℚ) (ψ : 0 < ε) (ω : 0 < δ) (θ : 0 < ε - δ) →
              u ∼[ ε - δ , θ ] (y δ ω) →
              u ∼[ ε , ψ ] (limit y φ)
closeLimit' u y φ ε δ ψ ω θ χ = σ'
  where
  π : (ε - δ) + δ ≡ ε
  -- TODO: Move to lemma
  π = (ε - δ) + δ
        ≡⟨ (sym $ +Assoc ε (- δ) δ) ⟩
      ε + (- δ + δ)
        ≡⟨ cong (_+_ ε) (+InvL δ) ⟩
      ε + 0
        ≡⟨ +IdR ε ⟩
      ε ∎

  σ : Σ (0 < ε) (λ π → Close ε π u (limit y φ))
  σ = subst (λ ?x → Σ (0 < ?x) (λ π → Close ?x π u (limit y φ)))
            π
            (0<+' {x = ε - δ} {y = δ} θ ω ,
             closeLimit u y φ (ε - δ) δ θ ω χ)

  σ' : Close ε ψ u (limit y φ)
  σ' = subst (λ π → Close ε π _ _) (isProp< 0 ε (fst σ) ψ) (snd σ)

-- HoTT Lemma 11.3.15
-- liftLipschitz : (f : ℚ → ℝ)
--                 (L : ℚ) (φ : 0 < L) →
--                 Lipschitzℚ f L φ →
--                 (ℝ → ℝ)
-- liftLipschitz f L φ george =
--   recursion
--     {A = ℝ}
--     {B = B}
--     ( liftLipschitzRational , liftLipschitzLimit , ψ , θ , ω , χ , π , ρ )
--   where
--   B : ℝ → ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero
--   B u v ε ψ = u ∼[ L · ε , ·0< {x = L} {y = ε} φ ψ ] v

--   liftLipschitzRational : ℚ → ℝ
--   liftLipschitzRational = f

--   φ' : ¬ L ≡ 0
--   φ' = ≠-symmetric $ <→≠ φ

--   φ'' : 0 < L [ φ' ]⁻¹
--   φ'' = 0<⁻¹ {x = L} φ

--   foo : (ε : ℚ) → 0 < ε → 0 < ε · (L [ φ' ]⁻¹)
--   foo ε ψ = ·0< {x = ε} {y = L [ φ' ]⁻¹} ψ φ''

--   buzz : (δ ε : ℚ) → L · ((δ / L [ φ' ]) + (ε / L [ φ' ])) ≡ δ + ε
--   buzz δ ε = L · ((δ / L [ φ' ]) + (ε / L [ φ' ]))
--                ≡⟨ cong (_·_ L) (sym $ ·DistR+ δ ε (L [ φ' ]⁻¹)) ⟩
--              L · ((δ + ε) · L [ φ' ]⁻¹)
--                ≡⟨ cong (_·_ L) (·Comm (δ + ε) (L [ φ' ]⁻¹)) ⟩
--              L · (L [ φ' ]⁻¹ · (δ + ε))
--                ≡⟨ ·Assoc L (L [ φ' ]⁻¹) (δ + ε) ⟩
--              (L · L [ φ' ]⁻¹) · (δ + ε)
--                 ≡⟨ cong (flip _·_ (δ + ε)) (⁻¹-inverse L φ') ⟩
--              1 · (δ + ε)
--                ≡⟨ ·IdL (δ + ε) ⟩
--              δ + ε ∎

--   foo₁ : ((ε : ℚ) → 0 < ε → ℝ) → ((ε : ℚ) → 0 < ε → ℝ)
--   foo₁ g = (λ ε θ → g (ε / L [ φ' ]) (foo ε θ))

--   foo₂ : (g : (ε : ℚ) → 0 < ε → ℝ) →
--          CauchyApproximation'' ℝ B g → 
--          CauchyApproximation (foo₁ g)
--   foo₂ g ψ =
--       (λ δ ε θ ω →
--         -- TODO: Prolly do that crazy sigma trick again
--         let fuz = ψ (δ / L [ φ' ]) (ε / L [ φ' ]) (foo δ θ) (foo ε ω)
--             buz : Σ (0 < δ + ε)
--                     (λ χ → Close (δ + ε)
--                                  χ
--                                  (g (δ / L [ φ' ]) (foo δ θ))
--                                  (g (ε / L [ φ' ]) (foo ε ω)))
--             buz = subst (λ ?x → Σ (0 < ?x)
--                                   (λ χ → Close ?x
--                                                χ
--                                                (g (δ / L [ φ' ]) (foo δ θ))
--                                                (g (ε / L [ φ' ]) (foo ε ω))))
--                         (buzz δ ε)
--                         (·0< {x = L} {y = (δ / L [ φ' ]) + (ε / L [ φ' ])}
--                              φ (+0< {x = δ / L [ φ' ]} {y = ε / L [ φ' ]}
--                                     (foo δ θ)
--                                     (foo ε ω)) ,
--                          fuz)

--             buz' : Close (δ + ε)
--                          (+0< {x = δ} {y = ε} θ ω)
--                          (g (δ / L [ φ' ]) (foo δ θ))
--                          (g (ε / L [ φ' ]) (foo ε ω))
--             buz' = subst (λ ?x → Close (δ + ε)
--                                  ?x
--                                  (g (δ / L [ φ' ]) (foo δ θ))
--                                  (g (ε / L [ φ' ]) (foo ε ω)))
--                          (isProp< 0 (δ + ε) _ _)
--                          (snd buz)
--         in buz')
--     where
--     light : (δ ε : ℚ) →
--             0 < δ → 0 < ε →
--             0 < L · ((δ / L [ φ' ]) + (ε / L [ φ' ]))
--     light δ ε θ ω = subst (_<_ 0) (sym (buzz δ ε)) (+0< {x = δ} {y = ε} θ ω) 

--   liftLipschitzLimit :
--     (f' : (ε : ℚ) → 0 < ε → ℝ) →
--     CauchyApproximation'' ℝ B f' →
--     ℝ
--   liftLipschitzLimit f' ψ =
--     limit
--       (foo₁ f')
--       (foo₂ f' ψ)

--   ψ : (u v : ℝ) → ((ε : ℚ) (φ : 0 < ε) → B u v ε φ) → u ≡ v
--   ψ u v θ = path u v (λ ε ω →
--                        let 
--                        miller : Σ (0 < ε) (λ χ → Close ε χ u v)
--                        miller = subst (λ ?x → Σ (0 < ?x) (λ χ → Close ?x χ u v))
--                                       (·/ ε L φ')
--                                       (·0< {x = L} {y = ε / L [ φ' ]} φ (foo ε ω) , θ (ε / L [ φ' ]) (foo ε ω))

--                        miller' : Close ε ω u v
--                        miller' = subst (λ ?x → Close ε ?x u v) (isProp< 0 ε _ _) (snd miller)
--                        in miller')

--   θ : (q r ε : ℚ) (ω : 0 < ε) →
--       (- ε) < (q - r) →
--       (q - r) < ε →
--       B (liftLipschitzRational q) (liftLipschitzRational r) ε ω
--   θ q r ε ω χ π = george q r ε ω (lemma q r ε π χ)
--     where
--     -- TODO
--     lemma : (q r ε : ℚ) →
--             q - r < ε → - ε < q - r
--             → ∣ q - r ∣ < ε
--     lemma = {!!}

--   -- TODO: Rename f to f'
--   ω : (q ε δ : ℚ) (χ : 0 < ε) (π : 0 < δ) (ρ : 0 < ε - δ)
--       (f : (ε : ℚ) → 0 < ε → ℝ) (σ : CauchyApproximation'' ℝ B f) →
--       B (liftLipschitzRational q) (f δ π) (ε - δ) ρ →
--       B (liftLipschitzRational q) (liftLipschitzLimit f σ) ε χ
--   ω q ε δ χ π ρ f σ τ =
--     closeLimit' (liftLipschitzRational q)
--                 (foo₁ f) (foo₂ f σ)
--                 (L · ε) (L · δ)
--                 (·0< {x = L} {y = ε} φ χ) (·0< {x = L} {y = δ} φ π)
--                 (fst bar₁) (snd bar₁)
--     where
--     -- TODO: Move to lemma
--     bar₀ : L · (ε - δ) ≡ (L · ε) - (L · δ)
--     bar₀ = {!!}

--     bar₃ : f δ π ≡ f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ π))
--     bar₃ = cong₂ f (sym (·/' L δ φ')) (isProp→PathP (λ i → isProp< 0 (·/' L δ φ' (~ i))) π (foo (L · δ) (·0< {x = L} {y = δ} φ π))) 

--     bar₂ : Close (L · (ε - δ)) (·0< {x = L} {y = ε - δ} φ ρ)
--                  (liftLipschitzRational q)
--                  (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ π)))
--     bar₂ = subst (λ ?x → Close _ _ _ ?x) bar₃ τ
--       -- Close (L · (ε - (δ + η))) (·0< {x = L} {y = ε - (δ + η)} φ γ)
--       --       (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--       --       (g ((L · η) / L [ φ' ]) (foo (L · η) (·0< {x = L} {y = η} φ β)))

--     bar₁ : Σ (0 < (L · ε) - (L · δ))
--              (λ υ → Close ((L · ε) - (L · δ)) υ
--                           (liftLipschitzRational q)
--                           (foo₁ f (L · δ) (·0< {x = L} {y = δ} φ π)))
--     bar₁ = subst (λ ?x → Σ (0 < ?x) (λ υ → Close ?x υ _ _)) bar₀ (·0< {x = L} {y = ε - δ} φ ρ , bar₂) 

--   χ : (f' : (ε : ℚ) → 0 < ε → ℝ) (π : CauchyApproximation'' ℝ B f')
--       (r ε δ : ℚ) (ψ₁ : 0 < ε) (θ₁ : 0 < δ) (ω₁ : 0 < (ε - δ)) →
--       B (f₁ δ θ₁) (liftLipschitzRational r) (ε - δ) ω₁ →
--       B (liftLipschitzLimit f' φ₁) (liftLipschitzRational r) ε ψ₁
--   χ = {!!}

--   π : (f g : (ε : ℚ) → 0 < ε → ℝ)
--       (ρ : CauchyApproximation'' ℝ B f)
--       (τ : CauchyApproximation'' ℝ B g)
--       (ε δ η : ℚ)
--       (υ : 0 < ε) (α : 0 < δ) (β : 0 < η) (γ : 0 < (ε - (δ + η))) →
--       B (f δ α) (g η β) (ε - (δ + η)) γ →
--       B (liftLipschitzLimit f ρ) (liftLipschitzLimit g τ) ε υ
--   π f g ρ τ ε δ η υ α β γ ζ =
--     limitLimit (foo₁ f) (foo₁ g)
--                (foo₂ f ρ) (foo₂ g τ)
--                (L · ε) (L · δ) (L · η)
--                (·0< {x = L} {y = ε} φ υ)
--                (·0< {x = L} {y = δ} φ α)
--                (·0< {x = L} {y = η} φ β)
--                (fst foo₃)
--                (snd foo₃)
--     where
--     foo₅ : L · (ε - (δ + η)) ≡ (L · ε) - (L · δ + L · η)
--     foo₅ = {!!}

--     foo₇ : (f δ α) ≡
--            (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--     foo₇ = cong₂ f (sym (·/' L δ φ'))
--                    -- What on God's green earth is (∼ i)
--                    (isProp→PathP (λ i → isProp< 0 (·/' L δ φ' (~ i)))
--                                  α
--                                  (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--       -- (isProp→PathP (λ i → isProp< 0 δ) α {!foo (L · δ) (·0< {x = L} {y = δ} φ α)!})

--     foo₈ : (g η β) ≡
--            (g ((L · η) / L [ φ' ]) (foo (L · η) (·0< {x = L} {y = η} φ β)))
--     foo₈ = cong₂ g (sym (·/' L η φ'))
--                    (isProp→PathP (λ i → isProp< 0 (·/' L η φ' (~ i)))
--                                  β
--                                  (foo (L · η) (·0< {x = L} {y = η} φ β))) 

--     foo₆ :
--       Close (L · (ε - (δ + η))) (·0< {x = L} {y = ε - (δ + η)} φ γ)
--             (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--             (g ((L · η) / L [ φ' ]) (foo (L · η) (·0< {x = L} {y = η} φ β)))
--     foo₆ = subst2 (Close _ _) foo₇ foo₈ ζ

--     foo₃ : Σ (0 < (L · ε) - (L · δ + L · η))
--              (λ foo₄ →
--              Close ((L · ε) - (L · δ + L · η))
--                    foo₄
--                    (foo₁ f (L · δ) (·0< {x = L} {y = δ} φ α))
--                    (foo₁ g (L · η) (·0< {x = L} {y = η} φ β)))
--     foo₃ = subst (λ ?x → Σ (0 < ?x) (λ foo₄ → Close ?x foo₄ _ _))
--                  foo₅
--                  (·0< {x = L} {y = ε - (δ + η)} φ γ , foo₆)

--   ρ : (u v : ℝ) (ε : ℚ) (σ : 0 < ε) → isProp (B u v ε σ)
--   ρ u v ε σ = squash u v (L · ε) (·0< {x = L} {y = ε} φ σ)

-- TODO: Why does this not exist in the cubical library?
_↔_ : {i j : Level} → Type i → Type j → Type (ℓ-max i j)
A ↔ B = (A → B) × (B → A)

-- HoTT 11.3.21
Rounded : {i : Level}
          (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i) →
          ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
          Type i
Rounded B _ =
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) →
  B ε φ u v ↔ ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ ψ → B (ε - θ) ψ u v))

-- HoTT 11.3.22
TriangleInequality₁ :
  {i j : Level}
  (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i)
  (C : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type j) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (C ε φ u v)) →
  Type (ℓ-max i j)
TriangleInequality₁ B C _ _ =
  (u v w : ℝ)
  (ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) →
  C ε φ u v → B δ ψ v w → C (ε + δ) (0<+' {x = ε} {y = δ} φ ψ) u w

-- HoTT 11.3.23
TriangleInequality₂ :
  {i j : Level}
  (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i)
  (C : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type j) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (C ε φ u v)) →
  Type (ℓ-max i j)
TriangleInequality₂ B C _ _ =
  (u v w : ℝ)
  (ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) →
  B ε φ u v → C δ ψ v w → C (ε + δ) (0<+' {x = ε} {y = δ} φ ψ) u w

Close'RationalRational : (q r : ℚ) (ε : ℚ) → 0 < ε → Type ℓ-zero
Close'RationalRational q r ε φ = ∣ q - r ∣ < ε

close'RationalRationalProposition : 
  (q r : ℚ) (ε : ℚ) (φ : 0 < ε)  → isProp (Close'RationalRational q r ε φ)
close'RationalRationalProposition = {!!}

      -- γ : (ε : ℚ) (φ : 0 < ε) →
      --     Close'RationalRational q r ε φ ↔
      --     ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (Close'RationalRational q r (ε - θ)))
      -- γ ε φ = {!!}
      --   -- γ' , γ''
      --   where
      --   γ' : Close'RationalRational q r ε φ →
      --        ∃ ℚ (λ θ → (0 < θ) ×
      --                   Σ (0 < (ε - θ)) (Close'RationalRational q r (ε - θ)))
      --   γ' ψ = ∣ (θ , ι , κ , μ) ∣₁
      --     where
      --     ζ : ¬ 2 ≡ 0
      --     ζ = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt

      --     ζ' : 0 < 2
      --     ζ' = Bool.toWitness {Q = <Dec 0 2} tt

      --     θ = (ε - ∣ q - r ∣) / 2 [ ζ ] 

      --     foo' : ∣ q - r ∣ < ε
      --     foo' = {!!} -- <→∣∣< {x = q - r} {ε = ε} (snd ψ) (fst ψ)

      --     foo : 0 < ε - ∣ q - r ∣
      --     foo = <→0<- {x = ∣ q - r ∣} {y = ε} foo'

      --     ι : 0 < θ
      --     ι = 0</ {x = ε - ∣ q - r ∣} {y = 2} foo ζ'

      --     bar : θ < ε
      --     bar = subst (λ ?x → θ < ?x) (·IdR ε) bar''
      --       where
      --       baz : 2 [ ζ ]⁻¹ < 1
      --       baz = Bool.toWitness {Q = <Dec (2 [ ζ ]⁻¹) 1} tt

      --       baz' : 0 ≤ 2 [ ζ ]⁻¹
      --       baz' = Bool.toWitness {Q = ≤Dec 0 (2 [ ζ ]⁻¹)} tt

      --       bar''' : - ∣ q - r ∣ ≤ 0
      --       bar''' = ≤antitone- {x = 0} {y = ∣ q - r ∣} (0≤∣∣ (q - r))

      --       bar' : (ε - ∣ q - r ∣) ≤ ε
      --       bar' = subst (_≤_ (ε - ∣ q - r ∣))
      --                    (+IdR ε)
      --                    (≤-o+ (- ∣ q - r ∣) 0 ε bar''')

      --       bar'' : (ε - ∣ q - r ∣) · (2 [ ζ ]⁻¹) < ε · 1
      --       bar'' = ≤→<→·<· {x = ε - ∣ q - r ∣} {y = 2 [ ζ ]⁻¹} {z = ε} {w = 1}
      --                       bar' baz φ baz'

      --     κ : 0 < ε - θ
      --     κ = <→0<- {x = θ} {y = ε} bar 

      --     μ : Close'RationalRational q r (ε - θ) κ
      --     μ = {!!} -- (∣∣<→<₂ {x = q - r} {ε = ε - θ} knew) , (∣∣<→<₁ {x = q - r} {ε = ε - θ} knew)
      --       where
      --       bon : 0 < ε / 2 [ ζ ]
      --       bon = 0</ {x = ε} {y = 2} φ ζ'

      --       iver : ε - θ ≡ ε / 2 [ ζ ] + ∣ q - r ∣
      --       iver = {!!}
      --       -- ε - ((ε - ∣ q - r ∣) / 2 [ ζ ])
      --       --          ≡⟨ ? ⟩
      --       --        ε - (ε / 2 [ ζ ] + (- ∣ q - r ∣) / 2 [ ζ ])
      --       --          ≡⟨ ? ⟩
      --       --        ε (- (ε / 2 [ ζ ]) + - ((- ∣ q - r ∣) / 2 [ ζ ]))
      --       --          ≡⟨ ? ⟩
      --       --        ε (- (ε / 2 [ ζ ]) + ((- - ∣ q - r ∣) / 2 [ ζ ]))
      --       --          ≡⟨ ? ⟩
      --       --        ε (- (ε / 2 [ ζ ]) + ∣ q - r ∣ / 2 [ ζ ])
      --       --          ≡⟨ ? ⟩
      --       --        (ε - (ε / 2 [ ζ ]) + ∣ q - r ∣ / 2 [ ζ ]
      --       --          ≡⟨ ? ⟩

      --       -- TODO: No it needs to be ∣ q - r ∣ / 2 [ ] < ε - θ
      --       -- ≡ ε - (ε - ∣ q - r ∣) / 2 [ ]
      --       knew : ∣ q - r ∣ < ε - θ
      --       knew = subst2 _<_
      --                     (+IdL ∣ q - r ∣) (sym iver)
      --                     (<-+o 0 (ε / 2 [ ζ ]) ∣ q - r ∣ bon)

      --   γ'' = {!!}

close'RationalRationalRounded :
  (q r : ℚ) (ε : ℚ) (φ : 0 < ε) →
  Close'RationalRational q r ε φ ↔
  ∃ ℚ (λ θ → (0 < θ) ×
           Σ (0 < (ε - θ))
           (λ ψ → Close'RationalRational q r (ε - θ) ψ))
close'RationalRationalRounded = {!!}

Close'Σ : Σ ((ε : ℚ) → 0 < ε → ℝ → ℝ → Type ℓ-zero)
            (λ Close' →
            Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (Close' ε φ u v))
            (λ φ →
            Rounded Close' φ ×
            TriangleInequality₁ Close Close' squash φ ×
            TriangleInequality₂ Close Close' squash φ))
Close'Σ =
  -- (fst $ (recursion {A = A} {B = B} bar) u) v ε φ
  let foo = recursion {A = A} {B = B} bar
  in (λ ε φ u v → (fst $ foo u) v ε φ) ,
     ((λ ε φ u v → (fst $ snd $ foo u) v ε φ) ,
      (λ u v ε φ → (fst $ snd $ snd $ foo u) v ε φ) ,
      (λ u v w ε η ω θ →
       let foo' = (fst $ snd $ snd $ snd $ foo u) v w η ε θ ω 
       -- Oh my goodness
       in flip foo') ,
      -- This one has eight cases according to the last paragraph of the proof
      -- Not included as as part of A'
      (λ u v w ε η ω θ →
        let foo' = (fst $ snd $ snd $ snd $ foo u) v w ε η ω θ
            foo'' = (snd $ snd $ snd $ snd $ foo u) v w ε η ω θ
        in {!!}))
  where
  A' : (ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero) → Type ℓ-zero
  A' ◆ = ((u : ℝ) (ε : ℚ) (φ : 0 < ε) → isProp (◆ u ε φ)) ×
         ((u : ℝ) (ε : ℚ) (ω : 0 < ε) →
          (◆ u ε ω) ↔ ∃ ℚ (λ θ → (0 < θ) ×
                                 Σ (0 < ε - θ)
                                   (λ χ → ◆ u (ε - θ) χ))) ×
         ((u v : ℝ) (ε η : ℚ) (ω : 0 < ε) (θ : 0 < η) →
          Close ε ω u v →
          ◆ u η θ → ◆ v (η + ε) (0<+' {x = η} {y = ε} θ ω)) ×
         ((u v : ℝ) (ε η : ℚ) (ω : 0 < ε) (θ : 0 < η) →
          Close ε ω u v →
          ◆ v η θ → ◆ u (η + ε) (0<+' {x = η} {y = ε} θ ω))

  A : Type (ℓ-suc ℓ-zero)
  A = Σ (ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero) A'

  B : A → A → (ε : ℚ) → 0 < ε → Type ℓ-zero
  B ◆ ♥ ε φ = (u : ℝ) (η : ℚ) (ψ : 0 < η) →
              ((fst ◆) u η ψ → (fst ♥) u (ε + η) (0<+' {x = ε} {y = η} φ ψ)) × 
              ((fst ♥) u η ψ → (fst ◆) u (ε + η) (0<+' {x = ε} {y = η} φ ψ))

  C' : ((ε : ℚ) → 0 < ε → Type ℓ-zero) → Type ℓ-zero
  C' ▲ =
    ((ε : ℚ) (φ : 0 < ε) → isProp (▲ ε φ)) ×
    ((ε : ℚ) (φ : 0 < ε) → ▲ ε φ ↔ ∃ ℚ (λ θ → (0 < θ) ×
                                              Σ (0 < ε - θ)
                                                (λ χ → ▲ (ε - θ) χ)))

  C : Type (ℓ-suc ℓ-zero)
  C = Σ ((ε : ℚ) → 0 < ε → Type ℓ-zero) C'

  D : C → C → (ε : ℚ) → 0 < ε → Type ℓ-zero
  D ▲ □ ε φ = (η : ℚ) (ψ : 0 < η) →
              ((fst ▲) η ψ → (fst □) (η + ε) (0<+' {x = η} {y = ε} ψ φ)) ×
              ((fst □) η ψ → (fst ▲) (η + ε) (0<+' {x = η} {y = ε} ψ φ))

  lightyear : (◆ : ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero) →
      isProp (A' ◆)
  -- Trick: hehe we need the first projection to prove the rest are
  -- propositions, so just assume it's here. This lemma says we can do that
  lightyear ◆ = isOfHLevelSucIfInhabited→isOfHLevelSuc 0
          (λ a' → let β : (u : ℝ) (ε : ℚ) (φ : 0 < ε) → isProp (◆ u ε φ)
                      β = fst a'
                  in isProp×3 (isPropΠ3 (λ _ _ _ → isPropIsProp))
                              (isPropΠ3 (λ u ε φ →
                                isProp× (isProp→ isPropPropTrunc)
                                        (isProp→ (β u ε φ))))
                              (isPropΠ6 (λ u v ε η ω θ →
                                isPropΠ2 (λ χ π →
                                  β v (η + ε) (0<+' {x = η} {y = ε} θ ω))))
                              (isPropΠ6 λ u v ε η ω θ →
                                isPropΠ2 λ χ π →
                                  β u (η + ε) (0<+' {x = η} {y = ε} θ ω)))

  ψ : ℚ → A
  ψ q =
    let bar' = α , β , γ , ζ , ι , κ , μ , ν
        buzz = recursion {A = C} {B = D} bar'
        buzz' = recursion∼ {A = C} {B = D} bar'
    in (λ u → fst $ buzz u) ,
       ((λ u → fst $ snd $ buzz u) ,
        (λ u → snd $ snd $ buzz u) ,
        (λ u v ε θ φ ψ ω → fst $ buzz' ω θ ψ) ,
        (λ u v ε θ φ ψ ω → snd $ buzz' ω θ ψ))
    where
    α : ℚ → C
    -- HoTT 11.3.17
    α r = Close'RationalRational q r , (close'RationalRationalProposition q r , close'RationalRationalRounded q r)
      where
      -- Close'RationalRational : (ε : ℚ) → 0 < ε → Type ℓ-zero
      -- Close'RationalRational ε φ = (- ε < q - r) × (q - r < ε)

      β : (ε : ℚ) (φ : 0 < ε) → isProp (Close'RationalRational q r ε φ)
      β ε φ = {!!}
      -- isProp× (isProp< (- ε) (q - r)) (isProp< (q - r) ε)

      γ : (ε : ℚ) (φ : 0 < ε) →
          Close'RationalRational q r ε φ ↔
          ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (Close'RationalRational q r (ε - θ)))
      γ ε φ = {!!}
        -- γ' , γ''
        where
        γ' : Close'RationalRational q r ε φ →
             ∃ ℚ (λ θ → (0 < θ) ×
                        Σ (0 < (ε - θ)) (Close'RationalRational q r (ε - θ)))
        γ' ψ = ∣ (θ , ι , κ , μ) ∣₁
          where
          ζ : ¬ 2 ≡ 0
          ζ = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt

          ζ' : 0 < 2
          ζ' = Bool.toWitness {Q = <Dec 0 2} tt

          θ = (ε - ∣ q - r ∣) / 2 [ ζ ] 

          foo' : ∣ q - r ∣ < ε
          foo' = {!!} -- <→∣∣< {x = q - r} {ε = ε} (snd ψ) (fst ψ)

          foo : 0 < ε - ∣ q - r ∣
          foo = <→0<- {x = ∣ q - r ∣} {y = ε} foo'

          ι : 0 < θ
          ι = 0</ {x = ε - ∣ q - r ∣} {y = 2} foo ζ'

          bar : θ < ε
          bar = subst (λ ?x → θ < ?x) (·IdR ε) bar''
            where
            baz : 2 [ ζ ]⁻¹ < 1
            baz = Bool.toWitness {Q = <Dec (2 [ ζ ]⁻¹) 1} tt

            baz' : 0 ≤ 2 [ ζ ]⁻¹
            baz' = Bool.toWitness {Q = ≤Dec 0 (2 [ ζ ]⁻¹)} tt

            bar''' : - ∣ q - r ∣ ≤ 0
            bar''' = ≤antitone- {x = 0} {y = ∣ q - r ∣} (0≤∣∣ (q - r))

            bar' : (ε - ∣ q - r ∣) ≤ ε
            bar' = subst (_≤_ (ε - ∣ q - r ∣))
                         (+IdR ε)
                         (≤-o+ (- ∣ q - r ∣) 0 ε bar''')

            bar'' : (ε - ∣ q - r ∣) · (2 [ ζ ]⁻¹) < ε · 1
            bar'' = ≤→<→·<· {x = ε - ∣ q - r ∣} {y = 2 [ ζ ]⁻¹} {z = ε} {w = 1}
                            bar' baz φ baz'

          κ : 0 < ε - θ
          κ = <→0<- {x = θ} {y = ε} bar 

          μ : Close'RationalRational q r (ε - θ) κ
          μ = {!!} -- (∣∣<→<₂ {x = q - r} {ε = ε - θ} knew) , (∣∣<→<₁ {x = q - r} {ε = ε - θ} knew)
            where
            bon : 0 < ε / 2 [ ζ ]
            bon = 0</ {x = ε} {y = 2} φ ζ'

            iver : ε - θ ≡ ε / 2 [ ζ ] + ∣ q - r ∣
            iver = {!!}
            -- ε - ((ε - ∣ q - r ∣) / 2 [ ζ ])
            --          ≡⟨ ? ⟩
            --        ε - (ε / 2 [ ζ ] + (- ∣ q - r ∣) / 2 [ ζ ])
            --          ≡⟨ ? ⟩
            --        ε (- (ε / 2 [ ζ ]) + - ((- ∣ q - r ∣) / 2 [ ζ ]))
            --          ≡⟨ ? ⟩
            --        ε (- (ε / 2 [ ζ ]) + ((- - ∣ q - r ∣) / 2 [ ζ ]))
            --          ≡⟨ ? ⟩
            --        ε (- (ε / 2 [ ζ ]) + ∣ q - r ∣ / 2 [ ζ ])
            --          ≡⟨ ? ⟩
            --        (ε - (ε / 2 [ ζ ]) + ∣ q - r ∣ / 2 [ ζ ]
            --          ≡⟨ ? ⟩

            -- TODO: No it needs to be ∣ q - r ∣ / 2 [ ] < ε - θ
            -- ≡ ε - (ε - ∣ q - r ∣) / 2 [ ]
            knew : ∣ q - r ∣ < ε - θ
            knew = subst2 _<_
                          (+IdL ∣ q - r ∣) (sym iver)
                          (<-+o 0 (ε / 2 [ ζ ]) ∣ q - r ∣ bon)

        γ'' = {!!}

    β = {!!}

    γ = {!!}

    ζ = {!!}

    ι = {!!}

    κ = {!!}

    μ = {!!}

    ν = {!!}

  ω : (f : (ε : ℚ) → 0 < ε → A) → CauchyApproximation'' A B f → A
  ω f φ =
    let bar' = α , β , γ , ζ , ι , κ , μ , ν
        buzz = recursion {A = C} {B = D} bar'
        buzz' = recursion∼ {A = C} {B = D} bar'
    in (λ u → fst $ buzz u) ,
       ((λ u → fst $ snd $ buzz u) ,
        (λ u → snd $ snd $ buzz u) ,
        (λ u v ε θ φ ψ ω → fst $ buzz' ω θ ψ) ,
        (λ u v ε θ φ ψ ω → snd $ buzz' ω θ ψ))
    where
    α = {!!}

    β = {!!}

    γ = {!!}

    ζ = {!!}

    ι = {!!}

    κ = {!!}

    μ = {!!}

    ν = {!!}

  -- Seperatedness of B
  θ : (◆ ♥ : A) → ((ε : ℚ) (φ : 0 < ε) → B ◆ ♥ ε φ) → ◆ ≡ ♥
  θ ◆ ♥ χ =
    Σ≡Prop lightyear
           (funExt λ u → funExt (λ ε → funExt (λ φ → π u ε φ)))
    where
    π : (u : ℝ) (ε : ℚ) (φ : 0 < ε) → (fst ◆) u ε φ ≡ (fst ♥) u ε φ
    π u ε φ = ua $ propBiimpl→Equiv ((fst $ snd ◆) u ε φ)
                                    ((fst $ snd ♥) u ε φ)
                                    σ τ
      where
      -- TODO: Pull out into lemma
      ρ : (θ : ℚ) → θ + (ε - θ) ≡ ε
      ρ θ = θ + (ε - θ)
              ≡⟨ cong (_+_ θ) (+Comm ε (- θ)) ⟩
            θ + (- θ + ε)
              ≡⟨ +Assoc θ (- θ) ε ⟩
            (θ + - θ) + ε
              ≡⟨ cong (flip _+_ ε) (+InvR θ) ⟩
            0 + ε
              ≡⟨ +IdL ε ⟩
            ε ∎

      σ : (fst ◆) u ε φ → (fst ♥) u ε φ
      σ τ = μ
        where
        ι : ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ τ → (fst ◆) u (ε - θ) τ))
        ι = (fst $ (fst $ snd $ snd ◆) u ε φ) τ

        κ : (θ : ℚ) →
              (0 < θ) × Σ (0 < ε - θ) (λ τ → (fst ◆) u (ε - θ) τ) →
              (fst ♥) u ε φ
        κ θ (τ , υ , γ) = ο
          where
          ν : (fst ♥) u (θ + (ε - θ)) (0<+' {x = θ} {y = ε - θ} τ υ)
          ν = (fst $ χ θ τ u (ε - θ) υ) $ γ

          ξ : Σ (0 < ε) (λ ι → (fst ♥) u ε ι)
          ξ = subst (λ ?x → Σ (0 < ?x) (λ ι → (fst ♥) u ?x ι))
                       (ρ θ)
                       (0<+' {x = θ} {y = ε - θ} τ υ , ν)

          ο : (fst ♥) u ε φ
          ο = subst (λ ?x → (fst ♥) u ε ?x)
                         (isProp< 0 ε (fst ξ) φ)
                         (snd ξ)

        μ : (fst ♥) u ε φ
        μ = ∃-rec ((fst $ snd ♥) u ε φ) κ ι

      τ : (fst ♥) u ε φ → (fst ◆) u ε φ
      τ υ = μ
        where
        ι : ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ τ → (fst ♥) u (ε - θ) τ))
        ι = (fst $ (fst $ snd $ snd ♥) u ε φ) υ

        κ : (θ : ℚ) →
            (0 < θ) × Σ (0 < (ε - θ)) (λ υ → (fst ♥) u (ε - θ) υ) →
            (fst ◆) u ε φ
        κ θ (υ , γ , ζ) = ο
          where
          ν : (fst ◆) u (θ + (ε - θ)) (0<+' {x = θ} {y = ε - θ} υ γ)
          ν = (snd $ χ θ υ u (ε - θ) γ) $ ζ

          ξ : Σ (0 < ε) (λ ι → (fst ◆) u ε ι)
          ξ = subst (λ ?x → Σ (0 < ?x) (λ ι → (fst ◆) u ?x ι))
                       (ρ θ)
                       (0<+' {x = θ} {y = ε - θ} υ γ , ν)

          ο : (fst ◆) u ε φ
          ο = subst (λ ?x → (fst ◆) u ε ?x)
                         (isProp< 0 ε (fst ξ) φ)
                         (snd ξ)

        μ : (fst ◆) u ε φ
        μ = ∃-rec ((fst $ snd ◆) u ε φ) κ ι

  χ = {!!}

  π = {!!}

  ρ = {!!}

  σ = {!!}

  τ = {!!}

  -- TODO: Name
  bar = ψ , ω , θ , χ , π , ρ , σ , τ

Close' : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type ℓ-zero
Close' = fst Close'Σ

syntax Close' ε p x y = x ≈[ ε , p ] y

closeProposition : (ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (Close' ε φ u v)
closeProposition = fst $ snd $ Close'Σ

closeRounded : Rounded Close' closeProposition
closeRounded = fst $ snd $ snd $ Close'Σ

closeTriangleInequality₁ :
  TriangleInequality₁ Close Close' squash closeProposition
closeTriangleInequality₁ = fst $ snd $ snd $ snd $ Close'Σ

closeTriangleInequality₂ :
  TriangleInequality₂ Close Close' squash closeProposition
closeTriangleInequality₂ = snd $ snd $ snd $ snd $ Close'Σ
