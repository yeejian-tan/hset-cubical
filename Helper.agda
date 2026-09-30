{-# OPTIONS --cubical=no-glue #-}

module Helper where
  open import Agda.Builtin.Cubical.Path public
  open import Agda.Primitive.Cubical
    renaming ( primIMin       to infixr 20 _∧_  -- I → I → I
             ; primIMax       to infixr 20 _∨_  -- I → I → I
             ; primINeg       to infix 30 ~_ -- I → I
             ; primComp       to comp
             ; primHComp      to hcomp
             ; primTransp     to transp) public

  open import Agda.Primitive public renaming (Set   to Type)
  open import Agda.Builtin.Unit public
  open import Agda.Builtin.Cubical.Sub public
    renaming (primSubOut to outS)

  refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
  refl {x = x} _ = x
  {-# INLINE refl #-}

   -- transport is a special case of transp
  transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
  transport p a = transp (λ i → p i) i0 a

  transportRefl : ∀ {ℓ} {A : Type ℓ} (x : A) → transport refl x ≡ x
  transportRefl {A = A} x i = transp (λ _ → A) i x

  transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A) → PathP (λ i → p i) x (transport p x)
  transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

  SquareP : ∀ {ℓ}
    (A : I → I → Type ℓ)
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
    (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
    → Type ℓ
  SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

  cong : ∀{ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (f : (a : A) → B a) (p : x ≡ y) →
         PathP (λ i → B (p i)) (f x) (f y)
  cong f p i = f (p i)
  {-# INLINE cong #-}

  cong₂ : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} {C : (a : A) → (b : B a) → Type ℓ''} →
          (f : (a : A) → (b : B a) → C a b) →
          (p : x ≡ y) →
          {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
          PathP (λ i → C (p i) (q i)) (f x u) (f y v)
  cong₂ f p q i = f (p i) (q i)
  {-# INLINE cong₂ #-}

  Square : ∀{ℓ} {A : Type ℓ}
    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → Type ℓ
  Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

  _[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
  A [ φ ↦ u ] = Sub A φ u

  infix 4 _[_↦_]

  J : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) (p : x ≡ y) → P y p
  J {x = x} P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  JRefl : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) → J P d refl ≡ d
  JRefl P d = transportRefl d

  sym : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)
  {-# INLINE sym #-}

  data ⊥ : Type where

  ⊥-elim : ∀{ℓ} {A : Type ℓ} (x : ⊥) → A
  ⊥-elim ()

  record Lift {ℓa} ℓ (A : Type ℓa) : Type (ℓa ⊔ ℓ) where
    constructor lift
    field
      lower : A

  ⊥* : ∀{ℓ} → Type ℓ
  ⊥* = Lift _ ⊥

  ⊥*-elim : ∀{ℓ ℓ'} {A : Type ℓ} (x : ⊥* {ℓ'}) → A
  ⊥*-elim ()

  ⊤* : ∀{ℓ} → Type ℓ
  ⊤* = Lift _ ⊤

  tt* : ∀{ℓ} → ⊤* {ℓ}
  tt* = lift tt

  if_then_else_end : I → I → I → I
  if i then j else k end = (k ∧ ((~ i) ∨ j)) ∨ ((i ∨ k) ∧ j)

  {-# INLINE if_then_else_end #-}

  subst : ∀{ℓa ℓb} {A : Type ℓa} {a a' : A} (B : A → Type ℓb) (p : a ≡ a') → B a → B a'
  subst B p = transport (λ i → B (p i))
