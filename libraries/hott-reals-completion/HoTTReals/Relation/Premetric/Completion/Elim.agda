open import Cubical.Relation.Premetric.Base

module HoTTReals.Relation.Premetric.Completion.Elim {ℓ} {ℓ'}
  (M : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Rationals as ℚ hiding (isProp∼)
open import Cubical.Data.Rationals.Positive

open import HoTTReals.Relation.Premetric.Completion.Base M renaming (ℭ to ℭM)

open PremetricStr (snd M)

private
  variable
    ℓA ℓB : Level

record Elimℭ
  (A : ℭM → Type ℓA) (B : ∀ {x y : ℭM} → A x → A y → (ε : ℚ₊) → x ∼[ ε ] y → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where
  no-eta-equality
  field
    funι     : ∀ x → A (ι x)
    funLim   : ∀ x xc → (a∘x : ∀ q → A (x q))
               → (∀ ε δ → B {x ε} {x δ} (a∘x ε) (a∘x δ) (ε +₊ δ) (xc ε δ))
               → A (lim x xc)
    funEq    : ∀ {x y} p a a' → (∀ ε δ → B a a' (ε +₊ δ) (p (ε +₊ δ)))
               → (∀ ε → B a a' ε (p ε))
               → PathP (λ i → A (eqℭ x y p i)) a a'
    ι︵ι     : ∀ x y ε x≈y → B (funι x) (funι y) ε (ι-ι x≈y)
    ι︵lim   : ∀ x y ε δ yc r a∘y ydc
               → B (funι x) (a∘y δ) ε r
               → B (funι x) (funLim y yc a∘y ydc) (ε +₊ δ) (ι-lim δ yc r)
    lim︵ι   : ∀ x y ε δ xc r a∘x xdc
               → B (a∘x δ) (funι y) ε r
               → B (funLim x xc a∘x xdc) (funι y) (ε +₊ δ) (lim-ι δ xc r)
    lim︵lim : ∀ x y ε δ η xc yc
               → (r : x δ ∼[ ε ] y η)
               → ∀ a∘x xdc a∘y ydc
               → B (a∘x δ) (a∘y η) ε r
               → B (funLim x xc a∘x xdc) (funLim y yc a∘y ydc) (ε +₊ (δ +₊ η))
                   (lim-lim δ η xc yc r)
    isProp︵ : ∀ {x y} a a' ε r → isProp (B {x} {y} a a' ε r)

  go : ∀ x → A x
  go∼ : ∀ {x x' ε} → (r : x ∼[ ε ] x') → B (go x) (go x') ε r

  go (ι x)           = funι x
  go (lim x xc)      = funLim x xc (go ∘ x) (λ ε δ → go∼ (xc ε δ))
  go (eqℭ x y x~y i) =
    funEq x~y (go x) (go y) (λ ε δ → go∼ (x~y (ε +₊ δ))) (λ ε → go∼ (x~y ε)) i

  go∼ (ι-ι x≈y)             = ι︵ι _ _ _ x≈y
  go∼ (ι-lim δ yc r)        = ι︵lim _ _ _ δ yc r _ (λ ε' → go∼ ∘ (yc ε')) (go∼ r)
  go∼ (lim-ι δ xc r)        = lim︵ι _ _ _ δ xc r _ (λ ε' → go∼ ∘ (xc ε')) (go∼ r)
  go∼ (lim-lim δ η xc yc r) =
    lim︵lim _ _ _ δ η xc yc r _ (λ ε' → go∼ ∘ (xc ε')) _ (λ ε' → go∼ ∘ (yc ε')) (go∼ r)
  go∼ (isProp∼ x ε y p q i) =
    isProp→PathP (λ i → isProp︵ (go x) (go y) ε (isProp∼ x ε y p q i)) (go∼ p) (go∼ q) i

  goι-β : ∀ q → go (ι q) ≡ funι q
  goι-β _ = refl

  goLim-β : ∀ x xc → go (lim x xc) ≡ funLim x xc (go ∘ x) λ ε δ → go∼ (xc ε δ)
  goLim-β _ _ = refl

  goEq-β : ∀ x y x∼y → cong go (eqℭ x y x∼y) ≡ funEq x∼y (go x) (go y) _ _
  goEq-β _ _ _ = refl

{-# DISPLAY Elimℭ.go r = r #-}

record Elimℭ∼ (B : ∀ x y ε → x ∼[ ε ] y → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where
  no-eta-equality
  field
    ι︵ι     : ∀ x y ε x≈y → B (ι x) (ι y) ε (ι-ι x≈y)
    ι︵lim   : ∀ x y ε δ yc r
               → B (ι x) (y δ) ε r
               → B (ι x) (lim y yc) (ε +₊ δ) (ι-lim δ yc r)
    lim︵ι   : ∀ x y ε δ xc r
               → B (x δ) (ι y) ε r
               → B (lim x xc) (ι y) (ε +₊ δ) (lim-ι δ xc r)
    lim︵lim : ∀ x y ε δ η xc yc
               → (r : x δ ∼[ ε ] y η)
               → B (x δ) (y η) ε r
               → B (lim x xc) (lim y yc) (ε +₊ (δ +₊ η))
                   (lim-lim δ η xc yc r)
    isProp︵ : ∀ x y ε r → isProp (B x y ε r)

  go∼ : ∀ {x x' ε} → (r : x ∼[ ε ] x') → B x x' ε r
  go∼ (ι-ι x≈y)             = ι︵ι _ _ _ x≈y
  go∼ (ι-lim δ yc r)        = ι︵lim _ _ _ δ yc r (go∼ r)
  go∼ (lim-ι δ xc r)        = lim︵ι _ _ _ δ xc r (go∼ r)
  go∼ (lim-lim δ η xc yc r) = lim︵lim _ _ _ δ η xc yc r (go∼ r)
  go∼ (isProp∼ x ε y p q i) =
    isProp→PathP (λ i → isProp︵ x y ε (isProp∼ x ε y p q i)) (go∼ p) (go∼ q) i

{-# DISPLAY Elimℭ∼.go∼ r = r #-}

record Elimℭ-Prop (A : ℭM → Type ℓA) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where
  no-eta-equality
  field
    funι    : ∀ x → A (ι x)
    funLim  : ∀ x xc → (∀ q → A (x q)) → A (lim x xc)
    is-prop : ∀ x → isProp (A x)

  go : ∀ x → A x
  go (ι x)           = funι x
  go (lim x xc)      = funLim x xc (go ∘ x)
  go (eqℭ x y x~y i) = isProp→PathP (λ j → is-prop (eqℭ x y x~y j)) (go x) (go y) i

{-# DISPLAY Elimℭ-Prop.go r = r #-}

record Elimℭ-Prop2 (A : ℭM → ℭM → Type ℓA) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where
  no-eta-equality
  field
    funιι     : ∀ x y → A (ι x) (ι y)
    funιLim   : ∀ x y yc → (∀ ε → A (ι x) (y ε)) → A (ι x) (lim y yc)
    funLimι   : ∀ x xc y → (∀ ε → A (x ε) (ι y)) → A (lim x xc) (ι y)
    funLimLim : ∀ x xc y yc → (∀ ε δ → A (x ε) (y δ)) → A (lim x xc) (lim y yc)
    is-prop   : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = Elimℭ-Prop.go el module lGO where
    el : Elimℭ-Prop λ x → ∀ y → A x y
    el .Elimℭ-Prop.funι x = Elimℭ-Prop.go er module rιGO where
      er : Elimℭ-Prop (A (ι x))
      er .Elimℭ-Prop.funι    = funιι x
      er .Elimℭ-Prop.funLim  = funιLim x
      er .Elimℭ-Prop.is-prop = is-prop (ι x)
    el .Elimℭ-Prop.funLim  x xc funx = Elimℭ-Prop.go er module rLimGO where
      er : Elimℭ-Prop (A (lim x xc))
      er .Elimℭ-Prop.funι    y    = funLimι x xc y (flip funx (ι y))
      er .Elimℭ-Prop.funLim  y yc = λ _ → funLimLim x xc y yc (λ ε → funx ε ∘ y)
      er .Elimℭ-Prop.is-prop      = is-prop (lim x xc)
    el .Elimℭ-Prop.is-prop = isPropΠ ∘ is-prop

{-# DISPLAY Elimℭ-Prop2.lGO.el        r      = r #-}
{-# DISPLAY Elimℭ-Prop2.lGO.rιGO.er   r x    = r (ι x) #-}
{-# DISPLAY Elimℭ-Prop2.lGO.rLimGO.er r x xc = r (lim x xc) #-}

record Elimℭ-Prop2Sym (A : ℭM → ℭM → Type ℓA) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where
  no-eta-equality
  field
    funιι     : ∀ x y → A (ι x) (ι y)
    funιLim   : ∀ x y yc → (∀ ε → A (ι x) (y ε)) → A (ι x) (lim y yc)
    funLimLim : ∀ x xc y yc → (∀ ε δ → A (x ε) (y δ)) → A (lim x xc) (lim y yc)
    is-sym    : ∀ x y → A x y → A y x
    is-prop   : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = Elimℭ-Prop2.go e module GO where
    e : Elimℭ-Prop2 A
    e .Elimℭ-Prop2.funιι     = funιι
    e .Elimℭ-Prop2.funιLim   = funιLim
    e .Elimℭ-Prop2.funLimι   =
      λ x xc y r → is-sym (ι y) (lim x xc) (funιLim y x xc (is-sym _ (ι y) ∘ r))
    e .Elimℭ-Prop2.funLimLim = funLimLim
    e .Elimℭ-Prop2.is-prop   = is-prop

{-# DISPLAY Elimℭ-Prop2Sym.GO.e r = r #-}

record Recℭ (A : Type ℓA) (B : A → A → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where
  no-eta-equality
  field
    funι     : ⟨ M ⟩ → A
    funLim   : (a∘x : ℚ₊ → A) → (∀ ε δ → B (a∘x ε) (a∘x δ) (ε +₊ δ)) → A
    funEq    : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι︵ι     : ∀ x y ε
               → x ≈[ ε ] y
               → B (funι x) (funι y) ε
    ι︵lim   : ∀ x y ε δ yc
               → B (funι x) (y δ) ε
               → B (funι x) (funLim y yc) (ε +₊ δ)
    lim︵ι   : ∀ x y ε δ xc
               → B (x δ) (funι y) ε
               → B (funLim x xc) (funι y) (ε +₊ δ)
    lim︵lim : ∀ x y ε δ η xc yc
               → B (x δ) (y η) ε
               → B (funLim x xc) (funLim y yc) (ε +₊ (δ +₊ η))

    isProp︵ : ∀ a a' ε → isProp (B a a' ε)

  module GO where
    e : Elimℭ (λ _ → A) λ a a' ε _ → B a a' ε
    e .Elimℭ.funι                 = funι
    e .Elimℭ.funLim      _ _ a∘x  = funLim a∘x
    e .Elimℭ.funEq       _ a a' _ = funEq a a'
    e .Elimℭ.ι︵ι                                 = ι︵ι
    e .Elimℭ.ι︵lim   x _ ε δ _ _ a∘y ydc         = ι︵lim x a∘y ε δ ydc
    e .Elimℭ.lim︵ι   _ y ε δ _ _ a∘x xdc         = lim︵ι a∘x y ε δ xdc
    e .Elimℭ.lim︵lim _ _ ε δ η _ _ _ a∘x xdc a∘y = lim︵lim a∘x a∘y ε δ η xdc
    e .Elimℭ.isProp︵  x y ε _ = isProp︵ x y ε

  go : ℭM → A
  go = Elimℭ.go GO.e

  go∼ : {x y : ℭM} {ε : ℚ₊} (r : x ∼[ ε ] y) → B (go x) (go y) ε
  go∼ = Elimℭ.go∼ GO.e

{-# DISPLAY Recℭ.GO.e r = r #-}

record RecℭSym (A : Type ℓA) (B : A → A → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where
  no-eta-equality
  field
    funι     : ⟨ M ⟩ → A
    funLim   : (a∘x : ℚ₊ → A) → (∀ ε δ → B (a∘x ε) (a∘x δ) (ε +₊ δ)) → A
    funEq    : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι︵ι     : ∀ x y ε
               → x ≈[ ε ] y
               → B (funι x) (funι y) ε
    ι︵lim   : ∀ x y ε δ yc
               → B (funι x) (y δ) ε
               → B (funι x) (funLim y yc) (ε +₊ δ)
    lim︵lim : ∀ x y ε δ η xc yc
               → B (x δ) (y η) ε
               → B (funLim x xc) (funLim y yc) (ε +₊ (δ +₊ η))

    isSym︵  : ∀ a a' ε → B a a' ε → B a' a ε
    isProp︵ : ∀ a a' ε → isProp (B a a' ε)

  module GO where
    r : Recℭ A B
    r .Recℭ.funι     = funι
    r .Recℭ.funLim   = funLim
    r .Recℭ.funEq    = funEq
    r .Recℭ.ι︵ι     = ι︵ι
    r .Recℭ.ι︵lim   = ι︵lim
    r .Recℭ.lim︵ι   = λ x y ε δ xc →
      isSym︵ (funι y) (funLim x xc) (ε +₊ δ) ∘ ι︵lim y x ε δ xc ∘ isSym︵ (x δ) (funι y) ε
    r .Recℭ.lim︵lim = lim︵lim
    r .Recℭ.isProp︵ = isProp︵

  go : ℭM → A
  go = Recℭ.go GO.r

  go∼ : {x y : ℭM} {ε : ℚ₊} (r : x ∼[ ε ] y) → B (go x) (go y) ε
  go∼ = Recℭ.go∼ GO.r

{-# DISPLAY RecℭSym.GO.r r = r #-}

record Recℭ∼ (B : ℭM → ℭM → ℚ₊ → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where
  no-eta-equality
  field
    ι︵ι     : ∀ x y ε → (x ≈[ ε ] y) → B (ι x) (ι y) ε
    ι︵lim   : ∀ x y ε δ yc
               → ι x ∼[ ε ] y δ
               → B (ι x) (y δ) ε
               → B (ι x) (lim y yc) (ε +₊ δ)
    lim︵ι   : ∀ x y ε δ xc
               → x δ ∼[ ε ] ι y
               → B (x δ) (ι y) ε
               → B (lim x xc) (ι y) (ε +₊ δ)
    lim︵lim : ∀ x y ε δ η xc yc
               → x δ ∼[ ε ] y η
               → B (x δ) (y η) ε
               → B (lim x xc) (lim y yc) (ε +₊ (δ +₊ η))
    isProp︵ : ∀ x y ε → isProp (B x y ε)

  go∼ : ∀ {x x' ε} → x ∼[ ε ] x' → B x x' ε
  go∼ = Elimℭ∼.go∼ e module GO where
    e : Elimℭ∼ λ x x' ε _ → B x x' ε
    e .Elimℭ∼.ι︵ι     = ι︵ι
    e .Elimℭ∼.ι︵lim   = ι︵lim
    e .Elimℭ∼.lim︵ι   = lim︵ι
    e .Elimℭ∼.lim︵lim = lim︵lim
    e .Elimℭ∼.isProp︵ = λ x y ε _ → isProp︵ x y ε

{-# DISPLAY Recℭ∼.GO.e r = r #-}

record Casesℭ (A : Type ℓA) (B : A → A → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where
  no-eta-equality
  field
    funι     : ⟨ M ⟩ → A
    funLim   : (x : ℚ₊ → ℭM) → isCauchy∼ x → A
    funEq    : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι︵ι     : ∀ x y ε
               → x ≈[ ε ] y
               → B (funι x) (funι y) ε
    ι︵lim   : ∀ x y ε δ yc
               → ι x ∼[ ε ] y δ
               → (a∘y : ℚ₊ → A)
               → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
               → B (funι x) (a∘y δ) ε
               → B (funι x) (funLim y yc) (ε +₊ δ)
    lim︵ι   : ∀ x y ε δ xc
               → x δ ∼[ ε ] ι y
               → (a∘x : ℚ₊ → A)
               → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
               → B (a∘x δ) (funι y) ε
               → B (funLim x xc) (funι y) (ε +₊ δ)
    lim︵lim : ∀ x y ε δ η xc yc
               → x δ ∼[ ε ] y η
               → (a∘x : ℚ₊ → A)
               → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
               → (a∘y : ℚ₊ → A)
               → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
               → B (a∘x δ) (a∘y η) ε
               → B (funLim x xc) (funLim y yc) (ε +₊ (δ +₊ η))
    isProp︵ : ∀ a a' ε → isProp (B a a' ε)

  module GO where
    e : Elimℭ (λ _ → A) λ a a' ε _ → B a a' ε
    e .Elimℭ.funι     = funι
    e .Elimℭ.funLim   = λ x xc _ _ → funLim x xc
    e .Elimℭ.funEq    = λ _ a a' _ p → funEq a a' p
    e .Elimℭ.ι︵ι     = ι︵ι
    e .Elimℭ.ι︵lim   = ι︵lim
    e .Elimℭ.lim︵ι   = lim︵ι
    e .Elimℭ.lim︵lim = lim︵lim
    e .Elimℭ.isProp︵ = λ x y ε _ → isProp︵ x y ε

  go : ℭM → A
  go = Elimℭ.go GO.e

  go∼ : {x y : ℭM} {ε : ℚ₊} → x ∼[ ε ] y → B (go x) (go y) ε
  go∼ = Elimℭ.go∼ GO.e

{-# DISPLAY Casesℭ.GO.e r = r #-}

-- lemma 3.7
isSym∼ : ∀ x y ε → x ∼[ ε ] y → y ∼[ ε ] x
isSym∼ = λ _ _ _ → Recℭ∼.go∼ rec module IsSym∼ where
  rec : Recℭ∼ λ x y ε → y ∼[ ε ] x
  rec .Recℭ∼.ι︵ι     = λ x y ε → ι-ι ∘ isSym≈ x y ε
  rec .Recℭ∼.ι︵lim   = λ x y ε δ yc _ → lim-ι δ yc
  rec .Recℭ∼.lim︵ι   = λ x y ε δ xc _ → ι-lim δ xc
  rec .Recℭ∼.lim︵lim = λ x y ε δ η xc yc _ →
    subst∼ _ _ (cong (⟨ ε ⟩₊ ℚ.+_) (ℚ.+Comm ⟨ η ⟩₊ ⟨ δ ⟩₊)) ∘ lim-lim η δ yc xc
  rec .Recℭ∼.isProp︵ = λ x y ε → isProp∼ y ε x

{-# DISPLAY IsSym∼.rec = isSym∼ #-}

record CasesℭSym (A : Type ℓA) (B : A → A → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where
  no-eta-equality
  field
    funι     : ⟨ M ⟩ → A
    funLim   : (x : ℚ₊ → ℭM) → isCauchy∼ x → A
    funEq    : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι︵ι     : ∀ x y ε
               → x ≈[ ε ] y
               → B (funι x) (funι y) ε
    ι︵lim   : ∀ x y ε δ yc
               → ι x ∼[ ε ] y δ
               → (a∘y : ℚ₊ → A)
               → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
               → B (funι x) (a∘y δ) ε
               → B (funι x) (funLim y yc) (ε +₊ δ)
    lim︵lim : ∀ x y ε δ η xc yc
               → x δ ∼[ ε ] y η
               → (a∘x : ℚ₊ → A)
               → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
               → (a∘y : ℚ₊ → A)
               → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
               → B (a∘x δ) (a∘y η) ε
               → B (funLim x xc) (funLim y yc) (ε +₊ (δ +₊ η))
    isSym︵  : ∀ a a' ε → B a a' ε → B a' a ε
    isProp︵ : ∀ a a' ε → isProp (B a a' ε)

  module GO where
    c : Casesℭ A B
    c .Casesℭ.funι     = funι
    c .Casesℭ.funLim   = funLim
    c .Casesℭ.funEq    = funEq
    c .Casesℭ.ι︵ι     = ι︵ι
    c .Casesℭ.ι︵lim   = ι︵lim
    c .Casesℭ.lim︵ι   = λ x y ε δ xc xδ∼y Bx Bxc →
        isSym︵ (funι y) (funLim x xc) (ε +₊ δ)
      ∘ ι︵lim y x ε δ xc (isSym∼ (x δ) (ι y) ε xδ∼y) Bx Bxc
      ∘ isSym︵ (Bx δ) (funι y) ε
    c .Casesℭ.lim︵lim = lim︵lim
    c .Casesℭ.isProp︵ = isProp︵

  go : ℭM → A
  go = Casesℭ.go GO.c

  go∼ : {x y : ℭM} {ε : ℚ₊} → x ∼[ ε ] y → B (go x) (go y) ε
  go∼ = Casesℭ.go∼ GO.c

{-# DISPLAY CasesℭSym.GO.c r = r #-}
