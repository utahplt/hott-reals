module HoTTReals.Data.Real.Order.Distance where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order

open BinaryRelation

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Real.Algebra.Negation
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Addition.Addition1
open import HoTTReals.Data.Real.Order.Magnitude

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

distance : ℝ → ℝ → ℝ
distance x y = ∣ x - y ∣

distanceNonexpandingℝ₂ : Nonexpandingℝ₂ distance
distanceNonexpandingℝ₂ = φ , ψ
  where
  φ : (w : ℝ) → Nonexpandingℝ (flip distance w)
  φ w = nonexpandingCompose
          ∣_∣ (flip _-_ w)
          magnitudeNonexpandingℝ (fst -nonexpandingℝ₂ w)

  ψ : (u : ℝ) → Nonexpandingℝ (distance u)
  ψ u = nonexpandingCompose
          ∣_∣ (_-_ u)
          magnitudeNonexpandingℝ (snd -nonexpandingℝ₂ u)

distanceLipschitz₁ : (v : ℝ) → Lipschitzℝ (flip distance v) 1 ℚ.0<1
distanceLipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ distance distanceNonexpandingℝ₂

distanceLipschitz₂ : (u : ℝ) → Lipschitzℝ (distance u) 1 ℚ.0<1
distanceLipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ distance distanceNonexpandingℝ₂

distanceContinuous₁ : (v : ℝ) → Continuous (flip distance v)
distanceContinuous₁ v = lipschitz→continuous (flip distance v) 1 ℚ.0<1 (distanceLipschitz₁ v)

distanceContinuous₂ : (u : ℝ) → Continuous (distance u)
distanceContinuous₂ u = lipschitz→continuous (distance u) 1 ℚ.0<1 (distanceLipschitz₂ u)

distanceExtendsRationalDistance : (q r : ℚ.ℚ) →
  distance (rational q) (rational r) ≡ rational (ℚ.distance q r)
distanceExtendsRationalDistance q r =
  cong ∣_∣ (liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ q (ℚ.- r))

0≤distance : (x y : ℝ) → 0 ≤ distance x y
0≤distance x y = 0≤magnitude (x - y)

close-0→magnitude< :
  {x : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  x ∼[ ε , φ ] 0 →
  ∣ x ∣ < rational ε
close-0→magnitude< {x} {ε} =
  inductionProposition {A = P} (φ , ψ , χ) x ε
  where
  P : ℝ → Type ℓ-zero
  P x = (ε : ℚ.ℚ) (φ : 0 ℚ.< ε) → x ∼[ ε , φ ] 0 → ∣ x ∣ < rational ε

  φ : (q : ℚ.ℚ) (ε : ℚ.ℚ) (ψ : 0 ℚ.< ε) →
      rational q ∼[ ε , ψ ] 0 →
      ∣ rational q ∣ < rational ε
  φ q ε ψ ω = τ
    where
    π : ℚ.∣ q ℚ.- 0 ∣ ℚ.< ε
    π = close→close' (rational q) 0 ε ψ ω

    ρ : ℚ.∣ q ∣ ℚ.< ε
    ρ = subst (ℚ._< ε) (cong ℚ.∣_∣ $ ℚ.+IdR q) π

    τ : rational ℚ.∣ q ∣ < rational ε
    τ = rationalStrictMonotone {ℚ.∣ q ∣} {ε} ρ

    τ' : ∣ rational q ∣ < rational ε
    τ' = subst (_< rational ε)
               (sym $ magnitudeExtendsRationalMagnitude q)
               τ

  ψ : (x : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (ω : CauchyApproximation x) →
      ((δ : ℚ.ℚ) (χ : 0 ℚ.< δ) →
       (ε : ℚ.ℚ) (π : 0 ℚ.< ε) →
       x δ χ ∼[ ε , π ] 0 →
       ∣ x δ χ ∣ < rational ε) →
      (ε : ℚ.ℚ) (π : 0 ℚ.< ε) →
      limit x ω ∼[ ε , π ] 0 →
      ∣ limit x ω ∣ < rational ε
  ψ x ω χ ε π ρ =
    ∃-rec (<-isProp ∣ limit x ω ∣ (rational ε))
          ψ'
          (closeOpen (limit x ω) 0 ε π ρ)
    where
    ψ' : (θ : ℚ.ℚ) →
         (0 ℚ.< θ) × Σ (0 ℚ.< ε ℚ.- θ) (λ σ → limit x ω ∼[ ε ℚ.- θ , σ ] 0) →
         ∣ limit x ω ∣ < rational ε
    ψ' θ (σ , τ , υ) = κ'
      where
      α : 0 ℚ.< θ / 4 [ ℚ.4≠0 ]
      α = ℚ.0</ {x = θ} {y = 4} σ ℚ.0<4

      α' : 0 ℚ.< θ / 2 [ ℚ.2≠0 ]
      α' = ℚ.0</ {x = θ} {y = 2} σ ℚ.0<2

      β : Close ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
                (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α)
                (x (θ / 4 [ ℚ.4≠0 ]) α)
                (limit x ω)
      β = closeLimit'' x ω (θ / 4 [ ℚ.4≠0 ]) (θ / 4 [ ℚ.4≠0 ]) α α

      γ : x (θ / 4 [ ℚ.4≠0 ]) α
          ∼[ ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ) ,
             ℚ.0<+'
               {x = ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))} {y = ε ℚ.- θ}
               (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} α α) τ ]
          0
      γ = closeTriangleInequality
            (x (θ / 4 [ ℚ.4≠0 ]) α) (limit x ω) 0
            ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) (ε ℚ.- θ)
            (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} α α) τ
            β υ

      ζ : ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ) ≡
          ε ℚ.- (θ / 2 [ ℚ.2≠0 ])
      ζ = ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ)
            ≡⟨ cong (flip ℚ._+_ $ ε ℚ.- θ) (ℚ.self/4≡self/2 θ ℚ.4≠0 ℚ.2≠0) ⟩
          (θ / 2 [ ℚ.2≠0 ]) ℚ.+ (ε ℚ.- θ)
            ≡⟨ ℚ.addRightSwap (θ / 2 [ ℚ.2≠0 ]) ε (ℚ.- θ) ⟩
          ε ℚ.+ ((θ / 2 [ ℚ.2≠0 ]) ℚ.- θ)
            ≡⟨ cong (ℚ._+_ ε) (sym $ ℚ.negateSubtract' θ (θ / 2 [ ℚ.2≠0 ])) ⟩
          ε ℚ.- (θ ℚ.- (θ / 2 [ ℚ.2≠0 ]))
            ≡⟨ cong (ℚ._-_ ε) (ℚ.self-self/2≡self/2 θ) ⟩
          ε ℚ.- (θ / 2 [ ℚ.2≠0 ]) ∎

      ι : ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣ <
          rational (((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ))
      ι = χ (θ / 4 [ ℚ.4≠0 ]) α
            (((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ))
            (ℚ.0<+'
               {x = ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))} {y = ε ℚ.- θ}
               (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} α α) τ)
            γ 

      ι' : ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣ <
           rational (ε ℚ.- (θ / 2 [ ℚ.2≠0 ]))
      ι' = subst (_<_ ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣) (cong rational ζ) ι

      β' : Close ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
                 (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α)
                 ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣
                 ∣ limit x ω ∣
      β' = magnitudeNonexpandingℝ
             (x (θ / 4 [ ℚ.4≠0 ]) α) (limit x ω)
             ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
             (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α)
             β

      κ : ∣ limit x ω ∣ <
          rational ((ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+
                    ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])))
      κ = <rational→close→<rational+ε
            {x = ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣} {y = ∣ limit x ω ∣}
            (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α) ι' β'

      μ : (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+
          ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ≡
          ε
      μ = (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+
          ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
            ≡⟨ cong (ℚ._+_ (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])))
                    (ℚ.self/4≡self/2 θ ℚ.4≠0 ℚ.2≠0) ⟩ 
          (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+ (θ / 2 [ ℚ.2≠0 ])
            ≡⟨ (sym $ ℚ.+Assoc ε (ℚ.- (θ / 2 [ ℚ.2≠0 ])) (θ / 2 [ ℚ.2≠0 ])) ⟩ 
          ε ℚ.+ (ℚ.- (θ / 2 [ ℚ.2≠0 ]) ℚ.+ (θ / 2 [ ℚ.2≠0 ]))
            ≡⟨ cong (ℚ._+_ ε) (ℚ.+InvL (θ / 2 [ ℚ.2≠0 ])) ⟩ 
          ε ℚ.+ 0
            ≡⟨ ℚ.+IdR ε ⟩ 
          ε ∎

      κ' : ∣ limit x ω ∣ < rational ε
      κ' = subst (∣ limit x ω ∣ <_) (cong rational μ) κ

  χ : (x : ℝ) → isProp (P x)
  χ x = isPropΠ3 (λ ε φ ψ → <-isProp ∣ x ∣ (rational ε))

close→distance< :
  {x y : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  x ∼[ ε , φ ] y →
  distance x y < rational ε
close→distance< {x} {y} {ε} φ ψ = χ'
  where
  ω : ∣ x - y ∣ ∼[ ε , φ ] ∣ y - y ∣
  ω = fst distanceNonexpandingℝ₂ y x y ε φ ψ

  ω' : ∣ x - y ∣ ∼[ ε , φ ] 0
  ω' = subst (λ ?x → ∣ x - y ∣ ∼[ ε , φ ] ?x) (≡0→magnitude≡0 $ +-inverseᵣ y) ω
  
  χ : ∣ ∣ x - y ∣ ∣ < rational ε
  χ = close-0→magnitude< φ ω'

  χ' : ∣ x - y ∣ < rational ε
  χ' = subst (flip _<_ $ rational ε) (magnitudeMagnitude≡magnitude $ x - y) χ

distance<→close : 
  {x y : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  distance x y < rational ε →
  x ∼[ ε , φ ] y
distance<→close {x} {y} {ε} =
  inductionProposition₂ {A = P}
  (rationalRationalCase ,
   rationalLimitCase ,
   limitRationalCase ,
   limitLimitCase ,
   pProposition)
  x y ε
  where
  P : ℝ → ℝ → Type ℓ-zero
  P x y = (ε : ℚ.ℚ) (φ : 0 ℚ.< ε) → distance x y < rational ε → x ∼[ ε , φ ] y

  rationalRationalCase :
    (q r : ℚ.ℚ) →
    (ε : ℚ.ℚ) (φ : 0 ℚ.< ε) →
    distance (rational q) (rational r) < rational ε →
    (rational q) ∼[ ε , φ ] (rational r)
  rationalRationalCase q r ε φ ψ = χ
    where
    ω : distance (rational q) (rational r) ≡ rational (ℚ.distance q r)
    ω = distanceExtendsRationalDistance q r

    ψ' : rational (ℚ.distance q r) < rational ε
    ψ' = subst (flip _<_ $ rational ε) ω ψ

    ψ'' : ℚ.distance q r ℚ.< ε
    ψ'' = rationalStrictReflective {q = ℚ.distance q r} {r = ε} ψ'

    χ : rational q ∼[ ε , φ ] rational r
    χ = close'→close (rational q) (rational r) ε φ ψ''

  rationalLimitCase :
    (q : ℚ.ℚ) (y : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (φ : CauchyApproximation y) →
    ((δ : ℚ.ℚ) (ψ : 0 ℚ.< δ) →
     (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
     distance (rational q) (y δ ψ) < rational ε →
     (rational q) ∼[ ε , ω ] (y δ ψ)) →
    (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
    distance (rational q) (limit y φ) < rational ε →
    (rational q) ∼[ ε , ω ] (limit y φ)
  rationalLimitCase q y φ ψ ε ω χ =
    ∃-rec (squash ε ω (rational q) (limit y φ)) rationalLimitCase'
          (<-archimedian (distance (rational q) (limit y φ)) (rational ε) χ)
    where
    rationalLimitCase' :
      (θ : ℚ.ℚ) →
      (distance (rational q) (limit y φ) < rational θ) ×
      (rational θ < rational ε) →
      rational q ∼[ ε , ω ] limit y φ
    rationalLimitCase' θ (π , ρ) = ζ''
      where
      σ : 0 ℚ.< θ
      σ = rationalStrictReflective {q = 0} {r = θ}
            (≤→<→< {x = 0} (0≤distance (rational q) (limit y φ)) π)

      ρ' : θ ℚ.< ε
      ρ' = rationalStrictReflective {q = θ} {r = ε} ρ

      τ : 0 ℚ.< ε ℚ.- θ
      τ = ℚ.<→0<- {x = θ} {y = ε} ρ'

      δ : ℚ.ℚ
      δ = (ε ℚ.- θ) / 4 [ ℚ.4≠0 ]

      σ' : 0 ℚ.< δ
      σ' = ℚ.0</ {x = ε ℚ.- θ} {y = 4} τ ℚ.0<4

      υ : limit y φ ∼[ (δ ℚ.+ δ) , ℚ.0<+' {x = δ} {y = δ} σ' σ' ] y δ σ'
      υ = limitClose'' y φ δ δ σ' σ'

      υ' : y δ σ' ∼[ (δ ℚ.+ δ) , ℚ.0<+' {x = δ} {y = δ} σ' σ' ] limit y φ
      υ' = closeSymmetric (limit y φ) (y δ σ') (δ ℚ.+ δ)
                          (ℚ.0<+' {x = δ} {y = δ} σ' σ') υ

      α : distance (rational q) (limit y φ)
          ∼[ δ ℚ.+ δ , ℚ.0<+' {x = δ} {y = δ} σ' σ' ]
          distance (rational q) (y δ σ')
      α = snd distanceNonexpandingℝ₂
            (rational q) (limit y φ) (y δ σ')
            (δ ℚ.+ δ) (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            υ

      β : distance (rational q) (y δ σ') < rational (θ ℚ.+ (δ ℚ.+ δ))
      β = <rational→close→<rational+ε (ℚ.0<+' {x = δ} {y = δ} σ' σ') π α

      γ : rational q
          ∼[ θ ℚ.+ (δ ℚ.+ δ) ,
             ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ') ]
          y δ σ'
      γ = ψ δ
            σ'
            (θ ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            β

      ζ : rational q ∼[ (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ) , _ ] limit y φ
      ζ = closeTriangleInequality
            (rational q) (y δ σ') (limit y φ)
            (θ ℚ.+ (δ ℚ.+ δ)) (δ ℚ.+ δ)
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ
              (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            γ υ'

      ι' : (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ) ≡ ε ℚ.- θ
      ι' = (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)
            ≡⟨ cong₂ ℚ._+_
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0)
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0) ⟩
          ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ]) ℚ.+ ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ])
            ≡⟨ ℚ.self/2≡self (ε ℚ.- θ) ℚ.2≠0 ⟩
          ε ℚ.- θ ∎

      ι : (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ) ≡ ε
      ι = (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)
            ≡⟨ sym $ ℚ.+Assoc θ (δ ℚ.+ δ) (δ ℚ.+ δ) ⟩
          θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))
            ≡⟨ cong (ℚ._+_ θ) ι' ⟩
          θ ℚ.+ (ε ℚ.- θ)
            ≡⟨ ℚ.addLeftSubtractCancel θ ε ⟩
          ε ∎

      ζ' : Σ (0 ℚ.< ε)
             (λ ?ξ → Close ε ?ξ (rational q) (limit y φ))
      ζ' = subst (λ ?x → Σ (0 ℚ.< ?x)
                           (λ ξ → Close ?x ξ (rational q) (limit y φ)))
                 ι
                 (_ , ζ)

      ζ'' : rational q ∼[ ε , ω ] limit y φ
      ζ'' = subst (λ ?ξ → Close ε ?ξ (rational q) (limit y φ))
                  (ℚ.isProp< 0 ε (fst ζ') ω)
                  (snd ζ') 

  limitRationalCase :
    (x : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (φ : CauchyApproximation x) (r : ℚ.ℚ) →
    ((δ : ℚ.ℚ) (ψ : 0 ℚ.< δ) →
     (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
     distance (x δ ψ) (rational r) < rational ε →
     x δ ψ ∼[ ε , ω ] rational r) →
    (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
    distance (limit x φ) (rational r) < rational ε →
    limit x φ ∼[ ε , ω ] rational r
  limitRationalCase x φ r ψ ε ω χ =
    ∃-rec (squash ε ω (limit x φ) (rational r)) limitRationalCase'
          (<-archimedian (distance (limit x φ) (rational r)) (rational ε) χ)
    where
    limitRationalCase' :
      (θ : ℚ.ℚ) →
      (distance (limit x φ) (rational r) < rational θ) ×
      (rational θ < rational ε) →
      limit x φ ∼[ ε , ω ] rational r
    limitRationalCase' θ (π , ρ) = ζ''
      where
      σ : 0 ℚ.< θ
      σ = rationalStrictReflective {q = 0} {r = θ}
            (≤→<→< {x = 0} (0≤distance (limit x φ) (rational r)) π)

      ρ' : θ ℚ.< ε
      ρ' = rationalStrictReflective {q = θ} {r = ε} ρ

      τ : 0 ℚ.< ε ℚ.- θ
      τ = ℚ.<→0<- {x = θ} {y = ε} ρ'

      δ : ℚ.ℚ
      δ = (ε ℚ.- θ) / 4 [ ℚ.4≠0 ]

      σ' : 0 ℚ.< δ
      σ' = ℚ.0</ {x = ε ℚ.- θ} {y = 4} τ ℚ.0<4

      υ : limit x φ ∼[ (δ ℚ.+ δ) , ℚ.0<+' {x = δ} {y = δ} σ' σ' ] x δ σ'
      υ = limitClose'' x φ δ δ σ' σ'

      α : distance (limit x φ) (rational r)
          ∼[ δ ℚ.+ δ , ℚ.0<+' {x = δ} {y = δ} σ' σ' ]
          distance (x δ σ') (rational r)
      α = fst distanceNonexpandingℝ₂
            (rational r) (limit x φ) (x δ σ')
            (δ ℚ.+ δ) (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            υ

      β : distance (x δ σ') (rational r) < rational (θ ℚ.+ (δ ℚ.+ δ))
      β = <rational→close→<rational+ε (ℚ.0<+' {x = δ} {y = δ} σ' σ') π α

      γ : x δ σ'
          ∼[ θ ℚ.+ (δ ℚ.+ δ) ,
             ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ') ]
          rational r
      γ = ψ δ
            σ'
            (θ ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            β

      ζ : limit x φ ∼[ (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ (δ ℚ.+ δ)) , _ ] rational r
      ζ = closeTriangleInequality
            (limit x φ) (x δ σ') (rational r)
            (δ ℚ.+ δ) (θ ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ
              (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            υ γ

      ι' : (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ) ≡ ε ℚ.- θ
      ι' = (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)
            ≡⟨ cong₂ ℚ._+_
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0)
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0) ⟩
          ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ]) ℚ.+ ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ])
            ≡⟨ ℚ.self/2≡self (ε ℚ.- θ) ℚ.2≠0 ⟩
          ε ℚ.- θ ∎

      ι : (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ (δ ℚ.+ δ)) ≡ ε
      ι = (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ (δ ℚ.+ δ))
            ≡⟨ ℚ.addRightSwap (δ ℚ.+ δ) θ (δ ℚ.+ δ) ⟩
          θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))
            ≡⟨ cong (ℚ._+_ θ) ι' ⟩
          θ ℚ.+ (ε ℚ.- θ)
            ≡⟨ ℚ.addLeftSubtractCancel θ ε ⟩
          ε ∎

      ζ' : Σ (0 ℚ.< ε)
             (λ ?ξ → Close ε ?ξ (limit x φ) (rational r))
      ζ' = subst (λ ?x → Σ (0 ℚ.< ?x)
                           (λ ξ → Close ?x ξ (limit x φ) (rational r)))
                 ι
                 (_ , ζ)

      ζ'' : limit x φ ∼[ ε , ω ] rational r
      ζ'' = subst (λ ?ξ → Close ε ?ξ (limit x φ) (rational r))
                  (ℚ.isProp< 0 ε (fst ζ') ω)
                  (snd ζ')

  limitLimitCase :
    (x y : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ)
    (φ : CauchyApproximation x)
    (ψ : CauchyApproximation y) →
    ((δ η : ℚ.ℚ) (ω : 0 ℚ.< δ) (χ : 0 ℚ.< η)
     (ε : ℚ.ℚ) (π : 0 ℚ.< ε) →
     distance (x δ ω) (y η χ) < rational ε →
     x δ ω ∼[ ε , π ] y η χ) →
    (ε : ℚ.ℚ) (χ : 0 ℚ.< ε) →
    distance (limit x φ) (limit y ψ) < rational ε →
    limit x φ ∼[ ε , χ ] limit y ψ
  limitLimitCase x y φ ψ ω ε χ π =
    ∃-rec (squash ε χ (limit x φ) (limit y ψ)) limitLimitCase'
          (<-archimedian (distance (limit x φ) (limit y ψ)) (rational ε) π)
    where
    limitLimitCase' :
      (θ : ℚ.ℚ) →
      (distance (limit x φ) (limit y ψ) < rational θ) ×
      (rational θ < rational ε) →
      limit x φ ∼[ ε , χ ] limit y ψ
    limitLimitCase' θ (π' , ρ) = ζ₄
      where
      σ : 0 ℚ.< θ
      σ = rationalStrictReflective {q = 0} {r = θ}
            (≤→<→< {x = 0} (0≤distance (limit x φ) (limit y ψ)) π')

      ρ' : θ ℚ.< ε
      ρ' = rationalStrictReflective {q = θ} {r = ε} ρ

      ρ'' : 0 ℚ.< ε ℚ.- θ
      ρ'' = ℚ.<→0<- {x = θ} {y = ε} ρ'

      δ : ℚ.ℚ
      δ = (ε ℚ.- θ) / 8 [ ℚ.8≠0 ]

      τ : 0 ℚ.< δ
      τ = ℚ.0</ {x = ε ℚ.- θ} {y = 8} ρ'' ℚ.0<8

      τ' : 0 ℚ.< δ ℚ.+ δ
      τ' = ℚ.0<+' {x = δ} {y = δ} τ τ

      υₓ : limit x φ ∼[ δ ℚ.+ δ , τ' ] x δ τ
      υₓ = limitClose'' x φ δ δ τ τ

      υᵧ : limit y ψ ∼[ δ ℚ.+ δ , τ' ] y δ τ
      υᵧ = limitClose'' y ψ δ δ τ τ

      υᵧ' : y δ τ ∼[ δ ℚ.+ δ , τ' ] limit y ψ
      υᵧ' = closeSymmetric (limit y ψ) (y δ τ) (δ ℚ.+ δ) τ' υᵧ

      α₁ : distance (limit x φ) (limit y ψ)
           ∼[ δ ℚ.+ δ , τ' ]
           distance (x δ τ) (limit y ψ)
      α₁ = fst distanceNonexpandingℝ₂
             (limit y ψ) (limit x φ) (x δ τ)
             (δ ℚ.+ δ) τ' υₓ

      β₁ : distance (x δ τ) (limit y ψ) < rational (θ ℚ.+ (δ ℚ.+ δ))
      β₁ = <rational→close→<rational+ε τ' π' α₁

      α₂ : distance (x δ τ) (limit y ψ)
           ∼[ δ ℚ.+ δ , τ' ]
           distance (x δ τ) (y δ τ)
      α₂ = snd distanceNonexpandingℝ₂
             (x δ τ) (limit y ψ) (y δ τ)
             (δ ℚ.+ δ) τ' υᵧ

      β₂ : distance (x δ τ) (y δ τ) < rational ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
      β₂ = <rational→close→<rational+ε τ' β₁ α₂

      γ : x δ τ
          ∼[ (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ) ,
             ℚ.0<+' {x = θ ℚ.+ (δ ℚ.+ δ)} {y = δ ℚ.+ δ}
               (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ τ') τ' ]
          y δ τ
      γ = ω δ δ τ τ
            ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = θ ℚ.+ (δ ℚ.+ δ)} {y = δ ℚ.+ δ}
               (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ τ') τ')
            β₂

      ζ₁ : limit x φ
           ∼[ (δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)) , _ ]
           y δ τ
      ζ₁ = closeTriangleInequality
             (limit x φ) (x δ τ) (y δ τ)
             (δ ℚ.+ δ) ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
             τ'
             (ℚ.0<+' {x = θ ℚ.+ (δ ℚ.+ δ)} {y = δ ℚ.+ δ}
               (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ τ') τ')
             υₓ γ

      ζ₂ : limit x φ
           ∼[ ((δ ℚ.+ δ) ℚ.+
              ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) ℚ.+ (δ ℚ.+ δ) , _ ]
           limit y ψ
      ζ₂ = closeTriangleInequality
            (limit x φ) (y δ τ) (limit y ψ)
            ((δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) (δ ℚ.+ δ)
            _ τ'
            ζ₁ υᵧ'

      η₁ : δ ℚ.+ δ ≡ (ε ℚ.- θ) / 4 [ ℚ.4≠0 ]
      η₁ = ℚ.self/8≡self/4 (ε ℚ.- θ) ℚ.8≠0 ℚ.4≠0

      η₂ : (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ) ≡ (ε ℚ.- θ) / 2 [ ℚ.2≠0 ]
      η₂ = (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)
             ≡⟨ cong₂ ℚ._+_ η₁ η₁ ⟩
           ((ε ℚ.- θ) / 4 [ ℚ.4≠0 ]) ℚ.+ ((ε ℚ.- θ) / 4 [ ℚ.4≠0 ])
             ≡⟨ ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0 ⟩
           (ε ℚ.- θ) / 2 [ ℚ.2≠0 ] ∎

      η₃ : ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ≡ ε ℚ.- θ
      η₃ = ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))
             ≡⟨ cong₂ ℚ._+_ η₂ η₂ ⟩
           ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ]) ℚ.+ ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ])
             ≡⟨ ℚ.self/2≡self (ε ℚ.- θ) ℚ.2≠0 ⟩
           ε ℚ.- θ ∎

      ι : ((δ ℚ.+ δ) ℚ.+
          ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) ℚ.+ (δ ℚ.+ δ) ≡ ε
      ι =
        ((δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) ℚ.+ (δ ℚ.+ δ)
          ≡⟨ sym $ ℚ.+Assoc (δ ℚ.+ δ)
                            ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)) (δ ℚ.+ δ) ⟩
        (δ ℚ.+ δ) ℚ.+ (((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
           ≡⟨ cong (ℚ._+_ (δ ℚ.+ δ))
                   (sym $ ℚ.+Assoc (θ ℚ.+ (δ ℚ.+ δ)) (δ ℚ.+ δ) (δ ℚ.+ δ)) ⟩
        (δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)))
           ≡⟨ cong (ℚ._+_ (δ ℚ.+ δ))
                   (sym $ ℚ.+Assoc θ (δ ℚ.+ δ) ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))) ⟩
        (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))))
           ≡⟨ ℚ.addRightSwap (δ ℚ.+ δ) θ
                             ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))) ⟩
        θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))))
          ≡⟨ cong (ℚ._+_ θ)
                  (ℚ.+Assoc (δ ℚ.+ δ) (δ ℚ.+ δ) ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))) ⟩
        θ ℚ.+ (((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)))
          ≡⟨ cong (ℚ._+_ θ) η₃ ⟩
        θ ℚ.+ (ε ℚ.- θ)
          ≡⟨ ℚ.addLeftSubtractCancel θ ε ⟩
        ε ∎

      ζ₃ : Σ (0 ℚ.< ε) (λ p → Close ε p (limit x φ) (limit y ψ))
      ζ₃ = subst (λ e → Σ (0 ℚ.< e) (λ p → Close e p (limit x φ) (limit y ψ)))
                 ι (_ , ζ₂)

      ζ₄ : limit x φ ∼[ ε , χ ] limit y ψ
      ζ₄ = subst (λ p → Close ε p (limit x φ) (limit y ψ))
                 (ℚ.isProp< 0 ε (fst ζ₃) χ) (snd ζ₃)

  pProposition : (x y : ℝ) → isProp (P x y)
  pProposition x y = isPropΠ3 (λ ε φ ψ → squash ε φ x y)
