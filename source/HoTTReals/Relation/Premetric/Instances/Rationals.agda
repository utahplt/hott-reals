module HoTTReals.Relation.Premetric.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (min ; max)

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Rationals

minⁿ : NE[ ℚPremetricSpace , NE[ ℚPremetricSpace , ℚPremetricSpace ]PrSpace ]
fst (fst minⁿ q) = min q
snd (fst minⁿ q) = {!!}
snd minⁿ = {!!}

maxⁿ : NE[ ℚPremetricSpace , NE[ ℚPremetricSpace , ℚPremetricSpace ]PrSpace ]
fst (fst maxⁿ q) = max q
snd (fst maxⁿ q) = {!!}
snd maxⁿ = {!!}
