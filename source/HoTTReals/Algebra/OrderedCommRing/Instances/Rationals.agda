module HoTTReals.Algebra.OrderedCommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals using (ℚ!)

open PositiveRationals
open ℚ₊Inverse
open OrderedCommRingTheory ℚOrderedCommRing using (·MonoL≤)
open OrderedCommRingReasoning ℚOrderedCommRing

⁻¹₊Flip≤ : {δ ε : ℚ₊} → δ ≤₊ ε → ε ⁻¹₊ ≤₊ δ ⁻¹₊
⁻¹₊Flip≤ {δ} {ε} δ≤ε = begin≤
  ⟨ ε ⁻¹₊ ⟩₊
    ≡→≤⟨ sym (ℚ.·IdR ⟨ ε ⁻¹₊ ⟩₊) ∙ cong (⟨ ε ⁻¹₊ ⟩₊ ℚ.·_) (sym (⁻¹inverse δ)) ⟩
  ⟨ ε ⁻¹₊ ⟩₊ ℚ.· (⟨ δ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊)
    ≡→≤⟨ pullFactorOut ⟨ ε ⁻¹₊ ⟩₊ ⟨ δ ⁻¹₊ ⟩₊ ⟨ δ ⟩₊ ⟩
  (⟨ ε ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊) ℚ.· ⟨ δ ⟩₊
    ≤⟨ ·MonoL≤ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ (ε ⁻¹₊) ·₊ (δ ⁻¹₊) ⟩₊ 0≤reciprocalProduct δ≤ε ⟩
  (⟨ ε ⁻¹₊ ⟩₊ ℚ.· ⟨ δ ⁻¹₊ ⟩₊) ℚ.· ⟨ ε ⟩₊
    ≡→≤⟨ pushFactorIn ⟨ ε ⁻¹₊ ⟩₊ ⟨ δ ⁻¹₊ ⟩₊ ⟨ ε ⟩₊ ⟩
  ⟨ δ ⁻¹₊ ⟩₊ ℚ.· (⟨ ε ⟩₊ ℚ.· ⟨ ε ⁻¹₊ ⟩₊)
    ≡→≤⟨ cong (⟨ δ ⁻¹₊ ⟩₊ ℚ.·_) (⁻¹inverse ε) ∙ ℚ.·IdR ⟨ δ ⁻¹₊ ⟩₊ ⟩
  ⟨ δ ⁻¹₊ ⟩₊ ◾
  where
  pullFactorOut : (u v a : ℚ) → u ℚ.· (a ℚ.· v) ≡ (u ℚ.· v) ℚ.· a
  pullFactorOut u v a = ℚ!

  pushFactorIn : (u v a : ℚ) → (u ℚ.· v) ℚ.· a ≡ v ℚ.· (a ℚ.· u)
  pushFactorIn u v a = ℚ!

  0≤reciprocalProduct : 0 ℚ.≤ ⟨ (ε ⁻¹₊) ·₊ (δ ⁻¹₊) ⟩₊
  0≤reciprocalProduct =
    ℚ.<Weaken≤ 0 ⟨ (ε ⁻¹₊) ·₊ (δ ⁻¹₊) ⟩₊ $ snd ((ε ⁻¹₊) ·₊ (δ ⁻¹₊))
