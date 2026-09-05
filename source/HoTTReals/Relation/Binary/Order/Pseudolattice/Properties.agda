module HoTTReals.Relation.Binary.Order.Pseudolattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary.Order.Pseudolattice.Base
open import Cubical.Relation.Binary.Order.Pseudolattice.Properties
  using (DualPseudolattice)
import Cubical.Relation.Binary.Order.Pseudolattice.Properties
  as PseudolatticeProperties

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module MeetProperties (L≤ : Pseudolattice ℓ ℓ') where
  private
    L = L≤ .fst
    open PseudolatticeStr (L≤ .snd)
    open PseudolatticeProperties.MeetProperties L≤

  ∧Mono : {a b c d : L} → a ≤ b → c ≤ d → a ∧l c ≤ b ∧l d
  ∧Mono a≤b c≤d = ∧GLB (is-trans _ _ _ ∧≤L a≤b) (is-trans _ _ _ ∧≤R c≤d)

  ∧MonoR : {a b c : L} → a ≤ b → a ∧l c ≤ b ∧l c
  ∧MonoR a≤b = ∧Mono a≤b (is-refl _)

  ∧MonoL : {a b c : L} → a ≤ b → c ∧l a ≤ c ∧l b
  ∧MonoL a≤b = ∧Mono (is-refl _) a≤b

module JoinProperties (L≤ : Pseudolattice ℓ ℓ') where
  open MeetProperties (DualPseudolattice L≤) public renaming (
      ∧Mono to ∨Mono ; ∧MonoR to ∨MonoR ; ∧MonoL to ∨MonoL)

module PseudolatticeTheory (L≤ : Pseudolattice ℓ ℓ') where
  open MeetProperties L≤ public
  open JoinProperties L≤ public

DualPseudolatticeEquiv :
  {L≤ : Pseudolattice ℓ ℓ'} {M≤ : Pseudolattice ℓ'' ℓ'''} →
  PseudolatticeEquiv L≤ M≤ →
  PseudolatticeEquiv (DualPseudolattice L≤) (DualPseudolattice M≤)
DualPseudolatticeEquiv e =
  e .fst ,
    ispseudolatticeequiv (λ x y → IsPseudolatticeEquiv.pres≤ (e .snd) y x)

module _
  {L≤ : Pseudolattice ℓ ℓ'} {M≤ : Pseudolattice ℓ'' ℓ'''}
  (e : PseudolatticeEquiv L≤ M≤)
  where
  private
    module L = PseudolatticeStr (L≤ .snd)
    module M = PseudolatticeStr (M≤ .snd)
    module ML = PseudolatticeProperties.MeetProperties L≤
    module MM = PseudolatticeProperties.MeetProperties M≤
    f = equivFun (e .fst)
    g = invEq (e .fst)

    -- m ≤ f x if and only if g m ≤ x, since f (g m) ≡ m and f preserves
    -- and reflects order.
    ≤equivFun→invEq≤ : {m : ⟨ M≤ ⟩} {x : ⟨ L≤ ⟩} → m M.≤ f x → g m L.≤ x
    ≤equivFun→invEq≤ {m} {x} =
      invEq (IsPseudolatticeEquiv.pres≤ (e .snd) (g m) x) ∘
      subst (M._≤ f x) (sym (secEq (e .fst) m))

    invEq≤→≤equivFun : {m : ⟨ M≤ ⟩} {x : ⟨ L≤ ⟩} → g m L.≤ x → m M.≤ f x
    invEq≤→≤equivFun {m} {x} =
      subst (M._≤ f x) (secEq (e .fst) m) ∘
      equivFun (IsPseudolatticeEquiv.pres≤ (e .snd) (g m) x)

  pres∧ : (a b : ⟨ L≤ ⟩) → f (a L.∧l b) ≡ f a M.∧l f b
  pres∧ a b = sym $
    MM.isMeet→≡∧
      (f (a L.∧l b))
      (λ m≤a∧b →
        invEq≤→≤equivFun (equivFun ML.isMeet∧ (≤equivFun→invEq≤ m≤a∧b) .fst))
      (λ m≤a∧b →
        invEq≤→≤equivFun (equivFun ML.isMeet∧ (≤equivFun→invEq≤ m≤a∧b) .snd))
      (λ m≤a m≤b →
        invEq≤→≤equivFun
          (invEq ML.isMeet∧ (≤equivFun→invEq≤ m≤a , ≤equivFun→invEq≤ m≤b)))

module _
  {L≤ : Pseudolattice ℓ ℓ'} {M≤ : Pseudolattice ℓ'' ℓ'''}
  (e : PseudolatticeEquiv L≤ M≤)
  where
  private
    module L = PseudolatticeStr (L≤ .snd)
    module M = PseudolatticeStr (M≤ .snd)
    f = equivFun (e .fst)

  pres∨ : (a b : ⟨ L≤ ⟩) → f (a L.∨l b) ≡ f a M.∨l f b
  pres∨ = pres∧ (DualPseudolatticeEquiv e)
