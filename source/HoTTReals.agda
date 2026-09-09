module HoTTReals where

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

import HoTTReals.Algebra.AbGroup.Properties

import HoTTReals.Algebra.ArchimedeanField.Base
import HoTTReals.Algebra.ArchimedeanField.Properties

import HoTTReals.Algebra.CommRing.Instances.Rationals
import HoTTReals.Algebra.CommRing.Properties

import HoTTReals.Algebra.HeytingField.Base
import HoTTReals.Algebra.HeytingField.Properties

import HoTTReals.Algebra.OrderedAbGroup.Base
import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
import HoTTReals.Algebra.OrderedAbGroup.Properties

import HoTTReals.Algebra.OrderedCommRing.Instances.Rationals
import HoTTReals.Algebra.OrderedCommRing.Morphisms
import HoTTReals.Algebra.OrderedCommRing.Properties

import HoTTReals.Algebra.OrderedField.Base
import HoTTReals.Algebra.OrderedField.Book
import HoTTReals.Algebra.OrderedField.Instances.Rationals
import HoTTReals.Algebra.OrderedField.Properties

import HoTTReals.Categories.Instances.CauchyCompleteArchimedeanFields
import HoTTReals.Categories.Instances.OrderedFields

import HoTTReals.Data.Real.Algebra.Addition

import HoTTReals.Data.Real.Algebra.ArchimedeanField
import HoTTReals.Data.Real.Algebra.Initial
import HoTTReals.Data.Real.Algebra.Lattice
import HoTTReals.Data.Real.Algebra.Multiplication
import HoTTReals.Data.Real.Algebra.OrderedAbGroup
import HoTTReals.Data.Real.Algebra.OrderedCommRing
import HoTTReals.Data.Real.Algebra.OrderedField
import HoTTReals.Data.Real.Algebra.Reciprocal

import HoTTReals.Data.Real.Order.Addition
import HoTTReals.Data.Real.Order.Base
import HoTTReals.Data.Real.Order.Magnitude
import HoTTReals.Data.Real.Order.Multiplication

import HoTTReals.Relation.Binary.Order.Proset.Properties

import HoTTReals.Relation.Binary.Order.Pseudolattice.Properties

import HoTTReals.Relation.Premetric.Completion.Lift

import HoTTReals.Relation.Premetric.Instances.ArchimedeanField

import HoTTReals.Relation.Premetric.Instances.Product

import HoTTReals.Relation.Premetric.Instances.Rationals

import HoTTReals.Relation.Premetric.Mappings

import HoTTReals.Relation.Premetric.Properties
