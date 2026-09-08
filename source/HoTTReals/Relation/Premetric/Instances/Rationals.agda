module HoTTReals.Relation.Premetric.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (min ; max)

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Rationals

open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals

open OrderedAbGroupStr (snd ℚOrderedAbGroup) using (≤-<-trans)
open OrderedAbGroupTheory ℚOrderedAbGroup using
  ( absΔ⊓≤R ; absΔ⊓≤L ; absΔ⊔≤R ; absΔ⊔≤L)

open NE₂[_,_,_]
open IsNonExpansive

minNE₂ : NE₂[ ℚPremetricSpace , ℚPremetricSpace , ℚPremetricSpace ]
fun minNE₂ = min
pres≈ (lNE minNE₂ s) q r ε = ≤-<-trans _ _ _ (absΔ⊓≤R q r s)
pres≈ (rNE minNE₂ q) r s ε = ≤-<-trans _ _ _ (absΔ⊓≤L q r s)

maxNE₂ : NE₂[ ℚPremetricSpace , ℚPremetricSpace , ℚPremetricSpace ]
fun maxNE₂ = max
pres≈ (lNE maxNE₂ s) q r ε = ≤-<-trans _ _ _ (absΔ⊔≤R q r s)
pres≈ (rNE maxNE₂ q) r s ε = ≤-<-trans _ _ _ (absΔ⊔≤L q r s)

minⁿ : NE[ ℚPremetricSpace , NE[ ℚPremetricSpace , ℚPremetricSpace ]PrSpace ]
minⁿ = makeNE₂ minNE₂

maxⁿ : NE[ ℚPremetricSpace , NE[ ℚPremetricSpace , ℚPremetricSpace ]PrSpace ]
maxⁿ = makeNE₂ maxNE₂
