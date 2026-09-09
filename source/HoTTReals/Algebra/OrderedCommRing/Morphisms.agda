module HoTTReals.Algebra.OrderedCommRing.Morphisms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ<≤ ℓ<≤' ℓ<≤'' ℓ<≤''' : Level

idOrderedCommRingHom : (R : OrderedCommRing ℓ ℓ<≤) → OrderedCommRingHom R R
fst (idOrderedCommRingHom R) = idfun ⟨ R ⟩
IsOrderedCommRingHom.isCommRingHom (snd (idOrderedCommRingHom R)) =
  snd (idCommRingHom (OrderedCommRing→CommRing R))
IsOrderedCommRingHom.pres≤ (snd (idOrderedCommRingHom R)) x y = idfun _
IsOrderedCommRingHom.reflect< (snd (idOrderedCommRingHom R)) x y = idfun _

compOrderedCommRingHom :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  {T : OrderedCommRing ℓ'' ℓ<≤''} →
  OrderedCommRingHom R S → OrderedCommRingHom S T → OrderedCommRingHom R T
fst (compOrderedCommRingHom f g) = fst g ∘ fst f
IsOrderedCommRingHom.isCommRingHom (snd (compOrderedCommRingHom f g)) =
  snd $
    compCommRingHom
      ( OrderedCommRingHom→CommRingHom f)
      ( OrderedCommRingHom→CommRingHom g)
IsOrderedCommRingHom.pres≤ (snd (compOrderedCommRingHom f g)) x y =
  IsOrderedCommRingHom.pres≤ (snd g) _ _ ∘
  IsOrderedCommRingHom.pres≤ (snd f) x y
IsOrderedCommRingHom.reflect< (snd (compOrderedCommRingHom f g)) x y =
  IsOrderedCommRingHom.reflect< (snd f) x y ∘
  IsOrderedCommRingHom.reflect< (snd g) _ _

compIdOrderedCommRingHom :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  (f : OrderedCommRingHom R S) →
  compOrderedCommRingHom (idOrderedCommRingHom R) f ≡ f
compIdOrderedCommRingHom f = OrderedCommRingHom≡ refl

idCompOrderedCommRingHom :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  (f : OrderedCommRingHom R S) →
  compOrderedCommRingHom f (idOrderedCommRingHom S) ≡ f
idCompOrderedCommRingHom f = OrderedCommRingHom≡ refl

compAssocOrderedCommRingHom :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  {T : OrderedCommRing ℓ'' ℓ<≤''} {U : OrderedCommRing ℓ''' ℓ<≤'''}
  (f : OrderedCommRingHom R S) (g : OrderedCommRingHom S T)
  (h : OrderedCommRingHom T U) →
  compOrderedCommRingHom (compOrderedCommRingHom f g) h ≡
  compOrderedCommRingHom f (compOrderedCommRingHom g h)
compAssocOrderedCommRingHom f g h = OrderedCommRingHom≡ refl

idOrderedCommRingMono : (R : OrderedCommRing ℓ ℓ<≤) → OrderedCommRingMono R R
fst (idOrderedCommRingMono R) = idfun ⟨ R ⟩
IsOrderedCommRingMono.isOrderedCommRingHom (snd (idOrderedCommRingMono R)) =
  snd (idOrderedCommRingHom R)
IsOrderedCommRingMono.pres< (snd (idOrderedCommRingMono R)) x y = idfun _

compOrderedCommRingMono :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  {T : OrderedCommRing ℓ'' ℓ<≤''} →
  OrderedCommRingMono R S → OrderedCommRingMono S T → OrderedCommRingMono R T
fst (compOrderedCommRingMono f g) = fst g ∘ fst f
IsOrderedCommRingMono.isOrderedCommRingHom (snd (compOrderedCommRingMono f g)) =
  snd $
    compOrderedCommRingHom
      ( OrderedCommRingMono→OrderedCommRingHom f)
      ( OrderedCommRingMono→OrderedCommRingHom g)
IsOrderedCommRingMono.pres< (snd (compOrderedCommRingMono f g)) x y =
  IsOrderedCommRingMono.pres< (snd g) _ _ ∘
  IsOrderedCommRingMono.pres< (snd f) x y

compIdOrderedCommRingMono :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  (f : OrderedCommRingMono R S) →
  compOrderedCommRingMono (idOrderedCommRingMono R) f ≡ f
compIdOrderedCommRingMono f = OrderedCommRingMono≡ refl

idCompOrderedCommRingMono :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  (f : OrderedCommRingMono R S) →
  compOrderedCommRingMono f (idOrderedCommRingMono S) ≡ f
idCompOrderedCommRingMono f = OrderedCommRingMono≡ refl

compAssocOrderedCommRingMono :
  {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
  {T : OrderedCommRing ℓ'' ℓ<≤''} {U : OrderedCommRing ℓ''' ℓ<≤'''}
  (f : OrderedCommRingMono R S) (g : OrderedCommRingMono S T)
  (h : OrderedCommRingMono T U) →
  compOrderedCommRingMono (compOrderedCommRingMono f g) h ≡
  compOrderedCommRingMono f (compOrderedCommRingMono g h)
compAssocOrderedCommRingMono f g h = OrderedCommRingMono≡ refl
