module HoTTReals.Algebra.AbGroup.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Properties

private
  variable
    ℓ : Level

module AbGroupTheory (A' : AbGroup ℓ) where
  private
    A = fst A'
  open AbGroupStr (snd A')
  open GroupTheory (AbGroup→Group A') using (invDistr ; invInv)

  negAddCancelLeft : (a b : A) → (- a) + (a + b) ≡ b
  negAddCancelLeft a b =
    +Assoc (- a) a b ∙ cong (_+ b) (+InvL a) ∙ +IdL b

  addNegCancelLeft : (a b : A) → a + ((- a) + b) ≡ b
  addNegCancelLeft a b =
    +Assoc a (- a) b ∙ cong (_+ b) (+InvR a) ∙ +IdL b

  addNegCancelRight : (a b : A) → (a + b) + (- b) ≡ a
  addNegCancelRight a b =
    sym (+Assoc a b (- b)) ∙ cong (a +_) (+InvR b) ∙ +IdR a

  addSubCancelRight : (a b : A) → (a + b) - b ≡ a
  addSubCancelRight = addNegCancelRight

  negAddCancelRight : (a b : A) → (a + (- b)) + b ≡ a
  negAddCancelRight a b =
    sym (+Assoc a (- b) b) ∙ cong (a +_) (+InvL b) ∙ +IdR a

  subAddCancel : (a b : A) → (a - b) + b ≡ a
  subAddCancel = negAddCancelRight

  negAddCancelCommAssoc : (a b : A) → (- a) + (b + a) ≡ b
  negAddCancelCommAssoc a b =
    cong ((- a) +_) (+Comm b a) ∙ negAddCancelLeft a b

  addNegCancelCommAssoc : (a b : A) → a + (b + (- a)) ≡ b
  addNegCancelCommAssoc a b =
    cong (a +_) (+Comm b (- a)) ∙ addNegCancelLeft a b

  negAddCancelComm : (a b : A) → ((- a) + b) + a ≡ b
  negAddCancelComm a b =
    sym (+Assoc (- a) b a) ∙ negAddCancelCommAssoc a b

  addNegCancelComm : (a b : A) → (a + b) + (- a) ≡ b
  addNegCancelComm a b =
    sym (+Assoc a b (- a)) ∙ addNegCancelCommAssoc a b

  addSubCancelLeft : (a b : A) → (a + b) - a ≡ b
  addSubCancelLeft = addNegCancelComm

  addSubCancel : (a b : A) → a + (b - a) ≡ b
  addSubCancel = addNegCancelCommAssoc

  negAdd : (a b : A) → - (a + b) ≡ (- a) + (- b)
  negAdd a b = invDistr a b ∙ +Comm (- b) (- a)

  negSub : (a b : A) → - (a - b) ≡ b - a
  negSub a b = invDistr a (- b) ∙ cong (_+ (- a)) (invInv b)

  negSubNeg : (a b : A) → (- a) - (- b) ≡ b - a
  negSubNeg a b = cong ((- a) +_) (invInv b) ∙ +Comm (- a) b

  subSubSelf : (a b : A) → a - (a - b) ≡ b
  subSubSelf a b = cong (a +_) (negSub a b) ∙ addSubCancel a b

  subAddSubCancel : (a b c : A) → (a - b) + (b - c) ≡ a - c
  subAddSubCancel a b c =
    +Assoc (a - b) b (- c) ∙ cong (_+ (- c)) (subAddCancel a b)
