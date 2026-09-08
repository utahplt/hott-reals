-- Vendored from LorenzoMolena/cubical algebraic-structures-wip ee4207d0,
-- Cubical/Algebra/ArchimedeanRing/Properties.agda, on 2026-09-08. Edited: no.
module HoTTReals.Algebra.ArchimedeanRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import HoTTReals.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.Ring

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne as ℕ₊₁ using (ℕ₊₁ ; 1+_ ; ℕ₊₁→ℕ)
open import Cubical.Data.Fast.Int.Base as ℤ hiding (_+_ ; _·_ ; -_ ; _-_)
import Cubical.Data.Fast.Int.Properties as ℤ
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level

ArchimedeanRing→StrictOrder : ArchimedeanRing ℓ ℓ' → StrictOrder ℓ ℓ'
ArchimedeanRing→StrictOrder = OrderedCommRing→StrictOrder ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→CommRing : ArchimedeanRing ℓ ℓ' → CommRing ℓ
ArchimedeanRing→CommRing = OrderedCommRing→CommRing ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Ring : ArchimedeanRing ℓ ℓ' → Ring ℓ
ArchimedeanRing→Ring = OrderedCommRing→Ring ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→PseudoLattice : ArchimedeanRing ℓ ℓ' → Pseudolattice ℓ ℓ'
ArchimedeanRing→PseudoLattice = OrderedCommRing→PseudoLattice ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Poset : ArchimedeanRing ℓ ℓ' → Poset ℓ ℓ'
ArchimedeanRing→Poset = OrderedCommRing→Poset ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Quoset : ArchimedeanRing ℓ ℓ' → Quoset ℓ ℓ'
ArchimedeanRing→Quoset = OrderedCommRing→Quoset ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Apartness : ArchimedeanRing ℓ ℓ' → Apartness ℓ ℓ'
ArchimedeanRing→Apartness = OrderedCommRing→Apartness ∘ ArchimedeanRing→OrderedCommRing

module _ (R' : ArchimedeanRing ℓ ℓ') where
  private
    R = fst R'
    ROCR = ArchimedeanRing→OrderedCommRing R'
    RCR  = ArchimedeanRing→CommRing R'

  open RingTheory (ArchimedeanRing→Ring R')
  open ArchimedeanRingStr (snd R')

  open module ArchimedeanRingReasoning = OrderedCommRingReasoning ROCR

  module ArchimedeanRingTheory where
    open OrderedCommRingTheory ROCR public

    ·CancelL< : ∀ x y z → 0r < z → (z · x) < (z · y) → x < y
    ·CancelL< x y z 0<z = ·CancelR< x y z 0<z ∘ subst2 _<_ (·Comm _ _) (·Comm _ _)

    0<ι₊₁ : ∀ a → 0r < ι₊₁ a
    0<ι₊₁ a = subst (_< ι₊₁ a) ιpres0 (ιpres< (pos 0) (pos (ℕ₊₁→ℕ a)) ℤ.zero-<possuc)

    0≤ι₀₊ : ∀ a → 0r ≤ ι₀₊ a
    0≤ι₀₊ zero    = subst (_≤ ι₀₊ 0) ιpres0 (is-refl _)
    0≤ι₀₊ (suc a) = <-≤-weaken 0r (ι₊₁ (1+ a)) (0<ι₊₁ (1+ a))

    ¬0≤ιnegsuc : ∀ n → ¬ (0r ≤ ι (negsuc n))
    ¬0≤ιnegsuc n = ⊥.rec ∘ ℤ.¬pos≤negsuc ∘ ιreflect≤ _ _ ∘ subst (_≤ _) (sym ιpres0)

    ¬0<ιneg : ∀ n → ¬ (0r < ι (neg n))
    ¬0<ιneg zero    = ⊥.rec ∘ is-irrefl 0r ∘ subst (_ <_) ιpres0
    ¬0<ιneg (suc n) = ⊥.rec ∘ ℤ.¬pos<negsuc ∘ ιreflect< _ _ ∘ subst (_< _) (sym ιpres0)

    0≤ι→Σℕ : ∀ k → 0r ≤ ι k → Σ[ n ∈ ℕ ] pos n ≡ k
    0≤ι→Σℕ (pos    n) = λ _ → n , refl
    0≤ι→Σℕ (negsuc n) = ⊥.rec ∘ ¬0≤ιnegsuc n

    0<ι→Σℕ₊₁ : ∀ k → 0r < ι k → Σ[ n ∈ ℕ₊₁ ] pos (ℕ₊₁→ℕ n) ≡ k
    0<ι→Σℕ₊₁ (pos zero   ) = ⊥.rec ∘ ¬0<ιneg 0
    0<ι→Σℕ₊₁ (pos (suc n)) = λ _ → 1+ n , refl
    0<ι→Σℕ₊₁ (negsuc n   ) = ⊥.rec ∘ ¬0<ιneg (suc n)

    archimedeanPropertyℕ₊₁ : ∀ x y → 0r ≤ x → 0r < y → ∃[ n ∈ ℕ₊₁ ] x < ι₊₁ n · y
    archimedeanPropertyℕ₊₁ x y 0≤x 0<y = do
      (k , x<ιky) ← archimedeanProperty x y 0<y
      let
        0<ιk = 0r < ι k
        0<ιk = ·CancelR< 0r (ι k) y 0<y
          (subst (_< ι k · y) (sym (0LeftAnnihilates y)) (≤-<-trans 0r x _ 0≤x x<ιky))
      return (map-snd (flip (subst ((x <_) ∘ (_· y) ∘ ι)) x<ιky ∘ sym) (0<ι→Σℕ₊₁ k 0<ιk))

    ∃ℤUpperBound : ∀ x → ∃[ k ∈ ℤ ] x < ι k
    ∃ℤUpperBound x = do
      (k , x<ιk·1) ← archimedeanProperty x 1r 0<1
      return (k , subst (x <_) (·IdR (ι k)) x<ιk·1)

    ∃ℤLowerBound : ∀ x → ∃[ k ∈ ℤ ] ι k < x
    ∃ℤLowerBound x = do
      (k , -x<ιk) ← ∃ℤUpperBound (- x)
      return (ℤ.- k , subst2 _<_ (sym (ιpres- k)) (solve! RCR) (-Flip< (- x) (ι k) -x<ιk))

    private
      1<Δ-lemma : ∀ x y l d → x + 1r < y → ι l < x → x < ι (pos d ℤ.+ l)
                → ∃[ k ∈ ℤ ] ((x < ι k) × (ι k < y))
      1<Δ-lemma x y (pos    l) zero x+1<y = (⊥.rec ∘_) ∘S is-asym _ _
      1<Δ-lemma x y (negsuc l) zero x+1<y = (⊥.rec ∘_) ∘S is-asym _ _
      1<Δ-lemma x y l (suc d) x+1<y ιl<x x<ι[1+d+l] = do
        let
          +d = pos d ; 1+d = pos (suc d)
        (inl x+1<ι[1+d+l]) ← is-weakly-linear (x + 1r) y (ι (1+d ℤ.+ l)) x+1<y
          where
          (inr ι[1+d+l]<y) → return (1+d ℤ.+ l , x<ι[1+d+l] , ι[1+d+l]<y)
        let
          ι[1+d+l]-1≡ι[d+l] : ι (1+d ℤ.+ l) - 1r ≡ ι (+d ℤ.+ l)
          ι[1+d+l]-1≡ι[d+l] =
            ι (1+d ℤ.+ l)        - 1r ≡⟨ sym $ congL _+_ $ cong ι $ ℤ.+Assoc 1 +d l ⟩
            ι (1 ℤ.+ (+d ℤ.+ l)) - 1r ≡⟨ congL _+_ (ιpres+ 1 _ ∙ congL _+_ ιpres1) ⟩
            1r + ι (+d ℤ.+ l)    - 1r ≡⟨ solve! RCR ⟩
            ι (+d ℤ.+ l)              ∎

        1<Δ-lemma x y l d x+1<y ιl<x
          (subst2 _<_ (solve! RCR) ι[1+d+l]-1≡ι[d+l] (x+1<ι[1+d+l] <+[ - 1r ])
          :> x < ι (+d ℤ.+ l))

    1<Δ→∃ℤ∈[_,_] : ∀ x y → 1r < y - x → ∃[ k ∈ ℤ ] ((x < ι k) × (ι k < y))
    1<Δ→∃ℤ∈[ x , y ] 1<Δ = do
      (l , ιl<x) ← ∃ℤLowerBound x
      (u , x<ιu) ← ∃ℤUpperBound x
      let
        (k , p) = ℤ.<→Σℕ (ιreflect< l u (is-trans< _ _ _ ιl<x x<ιu))
      1<Δ-lemma x y l (suc k)
        (subst (x + 1r <_) (solve! RCR) ([ x ]+< 1<Δ)
        :> x + 1r < y)
        ιl<x
        (subst (x <_) (cong ι (sym p ∙ ℤ.+Comm l _)) x<ιu
        :> x < ι (pos (suc k) ℤ.+ l))
