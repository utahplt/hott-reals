module HoTTReals.Data.Real.Order.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Cubical.HITs.PropositionalTruncation as PT using ()

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Order.Base

open PositiveRationals
open OrderedAbGroupTheory ℝOrderedAbGroup using (<→0<Δ ; 0<Δ→<)

·MonoR≤ : {x y a : ℝ} → 0 ≤ a → x ≤ y → x · a ≤ y · a
·MonoR≤ {x} {y} {a} 0≤a x≤y =
  subst2 _≤_ (·Comm a x) (·Comm a y) (·MonoL≤ {x} {y} {a} 0≤a x≤y)

0<· : {x y : ℝ} → 0 < x → 0 < y → 0 < x · y
0<· {x} {y} 0<x 0<y =
  PT.rec2
    ( isProp< 0 $ x · y)
    ( archimedean)
    ( isArchimedean< 0 x 0<x)
    ( isArchimedean< 0 y 0<y)
  where
  open OrderedAbGroupReasoning ℝOrderedAbGroup

  archimedean :
    (Σ[ q ∈ ℚ ] (0 < rat q) × (rat q < x)) →
    (Σ[ r ∈ ℚ ] (0 < rat r) × (rat r < y)) →
    0 < x · y
  archimedean (q , 0<ratq , ratq<x) (r , 0<ratr , ratr<y) =
    isTrans<≤ {0} {rat (q ℚ.· r)} {x · y} positive bound
    where
    ε : ℚ₊
    ε = q , invEq (<≃rat< {0} {q}) 0<ratq

    δ : ℚ₊
    δ = r , invEq (<≃rat< {0} {r}) 0<ratr

    positive : 0 < rat (q ℚ.· r)
    positive = equivFun (<≃rat< {0} {q ℚ.· r}) $ snd (ε ·₊ δ)

    bound : rat (q ℚ.· r) ≤ x · y
    bound = begin≤
      rat (q ℚ.· r)
        ≡→≤⟨ sym $ rat·rat q r ⟩
      rat q · rat r
        ≤⟨ ·MonoR≤ {rat q} {x} {rat r}
             ( <Weaken≤ {0} {rat r} 0<ratr)
             ( <Weaken≤ {rat q} {x} ratq<x) ⟩
      x · rat r
        ≤⟨ ·MonoL≤ {rat r} {y} {x}
             ( <Weaken≤ {0} {x} 0<x)
             ( <Weaken≤ {rat r} {y} ratr<y) ⟩
      x · y ◾

·MonoL< : {y z a : ℝ} → 0 < a → y < z → a · y < a · z
·MonoL< {y} {z} {a} 0<a y<z =
  0<Δ→< (a · y) (a · z) $
    subst (0 <_) (·DistR- a z y) (0<· 0<a $ <→0<Δ y z y<z)

·MonoR< : {x y a : ℝ} → 0 < a → x < y → x · a < y · a
·MonoR< {x} {y} {a} 0<a x<y =
  subst2 _<_ (·Comm a x) (·Comm a y) (·MonoL< {x} {y} {a} 0<a x<y)
