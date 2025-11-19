module HoTTReals.Data.Real.Induction where

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Definitions

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

-- HoTT 388 Enhanced principle of recursion
Recursion :
  {i j : Level}
  (A : Type i) →
  ((a b : A) → (ε : ℚ) → 0 < ε → Type j) →
  Type (ℓ-max i j)
Recursion A B =
  Σ (ℚ → A)
  (λ fRational →
  -- It turns out it is useful to have access to both the Cauchy
  -- approximation and the corresponding values in `A` inductively assigned to
  -- it.  I originally only had the values `f`, but needed when defining
  -- alternative closeness `Close'`/`≈`. Specifally, I needed it in the second
  -- subrecursion where the limit-limit case of `≈` is defined.
  --
  -- This is sort of like making sure that in a natural number induction that
  -- the inductive step has access to both what the previous `n` was and which
  -- value we have inductively assigned to it in the codomain. For natural
  -- numbers this is sort of implicit in the fact that the current value is
  -- `successor(n)`, but here we can't derive that information from `f`.
  --
  -- Note, I also later forgot the corresponding inductive assumptions in the
  -- rational-limit, limit-rational, and limit-limit cases which give induction
  -- assumptions about `x` and `y` in the domain and not just `f` and `g` in the
  -- codomain. Marked below with "here".
  Σ ((x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x) →
     (f : (ε : ℚ) → 0 < ε → A) →
     CauchyApproximation'' A B f →
     A)
  (λ fLimit →
  ((a b : A) → ((ε : ℚ) (φ : 0 < ε) → B a b ε φ) → a ≡ b) ×
  ((q r : ℚ)
   (ε : ℚ) (φ : 0 < ε) →
   - ε < q - r → q - r < ε →
   B (fRational q) (fRational r) ε φ) ×
  ((q ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) (θ : 0 < ε - δ) →
   (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y) →
   (g : (ε : ℚ) → 0 < ε → A) (χ : CauchyApproximation'' A B g) →
   -- Here (1)
   (rational q) ∼[ ε - δ , θ ] (y δ ψ) →
   B (fRational q) (g δ ψ) (ε - δ) θ →
   B (fRational q) (fLimit y ω g χ) ε φ) ×
  ((x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
   (f : (ε : ℚ) → 0 < ε → A) (ψ : CauchyApproximation'' A B f) →
   (r ε δ : ℚ) (θ : 0 < ε) (ω : 0 < δ) (χ : 0 < ε - δ) →
   -- Here (2)
   (x δ ω) ∼[ ε - δ , χ ] (rational r) →
   B (f δ ω) (fRational r) (ε - δ) χ →
   B (fLimit x φ f ψ) (fRational r) ε θ) ×
  ((x y : (ε : ℚ) → 0 < ε → ℝ)
   (f g : (ε : ℚ) → 0 < ε → A)
   (φ : CauchyApproximation x)
   (ψ : CauchyApproximation y)
   (θ : CauchyApproximation'' A B f) →
   (ω : CauchyApproximation'' A B g) →
   (ε δ η : ℚ) (χ : 0 < ε) (π : 0 < δ) (ρ : 0 < η) (σ : 0 < ε - (δ + η)) →
   -- Here (3)
   (x δ π) ∼[ ε - (δ + η) , σ ] (y η ρ) →
   B (f δ π) (g η ρ) (ε - (δ + η)) σ →
   B (fLimit x φ f θ) (fLimit y ψ g ω) ε χ) ×
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
  fLimit
    x ρ
    (λ ε φ → recursion α (x ε φ))
    (λ ε δ φ ψ → recursion∼ α (ρ ε δ φ ψ))
recursion α@(fRational , fLimit , φ , ψ , θ , ω , χ , π) (path u v ρ i) =
  φ (recursion α u) (recursion α v) (λ ε φ → recursion∼ α (ρ ε φ)) i

recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (rationalRational q r ε ρ σ τ) = ψ q r ε ρ σ τ
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (rationalLimit q ε δ ρ σ τ y υ ι) =
  θ q ε δ
    ρ σ τ
    y υ
    (λ ε κ → recursion α (y ε κ))
    (λ ε δ κ μ → recursion∼ α (υ ε δ κ μ))
    ι
    (recursion∼ α ι)
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (limitRational x ρ r ε δ σ τ υ ι) =
  ω x ρ
    (λ ε κ → recursion α (x ε κ))
    (λ ε δ κ μ → recursion∼ α (ρ ε δ κ μ))
    r ε δ
    σ τ υ
    ι (recursion∼ α ι)
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (limitLimit x y ρ σ ε δ η τ υ ι κ μ) =
  χ x y
    (λ ε ν → recursion α (x ε ν))
    (λ ε ν → recursion α (y ε ν))
    ρ σ
    (λ ε δ ν ξ → recursion∼ α (ρ ε δ ν ξ))
    (λ ε δ ν ξ → recursion∼ α (σ ε δ ν ξ))
    ε δ η
    τ υ ι
    κ μ (recursion∼ α μ)
recursion∼ α@(fRational , fLimit , φ , ψ , θ , ω , χ , π)
  (squash ε ρ u v ζ ζ' i) =
  isProp→PathP (λ j → π (recursion α u) (recursion α v) ε ρ)
               (recursion∼ α ζ)
               (recursion∼ α ζ')
               i
