module HoTTReals.Relation.Binary.Order.Pseudolattice.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Pseudolattice.Base
open import Cubical.Relation.Binary.Order.Pseudolattice.Properties
  using (DualPseudolattice)

private
  variable
    ℓ ℓ' : Level

module MeetProperties (L≤ : Pseudolattice ℓ ℓ') where
  private
    L = L≤ .fst
    open PseudolatticeStr (L≤ .snd)

  ∧Mono : {a b c d : L} → a ≤ b → c ≤ d → a ∧l c ≤ b ∧l d
  ∧Mono = {!!}

  ∧MonoR : {a b c : L} → a ≤ b → a ∧l c ≤ b ∧l c
  ∧MonoR = {!!}

  ∧MonoL : {a b c : L} → a ≤ b → c ∧l a ≤ c ∧l b
  ∧MonoL = {!!}

module JoinProperties (L≤ : Pseudolattice ℓ ℓ') where
  open MeetProperties (DualPseudolattice L≤) public renaming (
      ∧Mono to ∨Mono ; ∧MonoR to ∨MonoR ; ∧MonoL to ∨MonoL)

module PseudolatticeTheory (L≤ : Pseudolattice ℓ ℓ') where
  open MeetProperties L≤ public
  open JoinProperties L≤ public
