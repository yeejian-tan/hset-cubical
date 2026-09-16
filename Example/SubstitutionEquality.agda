{-# OPTIONS --cubical=uip --guardedness #-}

open import Example.Category

module Example.SubstitutionEquality {C : Category} where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Example.Context
open import SqFill
open import SqFillDef

-- infix 1 _≅ᶜ_

private
  variable
    Γ Δ Θ : Ctx C

-- record _≅ᶜ_ (Δ : Ctx C) (Γ : Ctx C) : Set where
--   field
--     from : Δ ⇒ Γ
--     to : Γ ⇒ Δ
--     eq-left : to ⊚ from ≡ id-subst Δ
--     eq-right : from ⊚ to ≡ id-subst Γ

primitive 
  prim^sqFill : ∀ {ℓ} (A : Set ℓ) → SqFill A

sqFill : ∀ {ℓ} (A : Set ℓ) → SqFill A
sqFill = prim^sqFill

uip : ∀ {ℓ} {A : Set ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
uip p q = sqFill _ p q refl refl

module _ {C : Category} {Δ Γ : Ctx C} where
  open Category C
  open Ctx
  open _⇒_

  -- equivalence of substitutions as defined in the original BiSikkel code:
  _≅ˢ_ : (σ τ : Δ ⇒ Γ) → Set
  σ ≅ˢ τ = ∀ {x : Obj} (δ : Δ ⟨ x ⟩) → func σ δ ≡ func τ δ

  -- given that funext is provable in cubical, we can easily "upgrade" the pointwise equality in the func field to propositional equality, then, we use sqFill to show that the naturality proofs of both substitutions are themselves equal
  equiv-to-prop : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → σ ≡ τ
  equiv-to-prop {σ} {τ} e i .func δ = e δ i

-- let e : ∀ δ . func σ δ ≡ func τ δ:
--
--                        λ j → Γ ⟪ f ⟫ (e δ j)
--       Γ ⟪ f ⟫ (func σ) δ ---------------> Γ ⟪ f ⟫ (func τ) δ
--               |                                    |
--               |                                    |
--  naturality σ | ============ sqfill =============> | naturality τ
--               |                                    |
--               ∨                                    ∨
--     (func σ) (Δ ⟪ f ⟫ δ) ---------------> (func τ) (Δ ⟪ f ⟫ δ)
--                       λ j → e (Δ ⟪ f ⟫ δ) j

  equiv-to-prop {σ} {τ} e i .naturality {x} {f = f} {δ = δ} = sqFill (Γ ⟨ x ⟩) (naturality σ) (naturality τ) (λ j → Γ ⟪ f ⟫ (e δ j)) (λ j → e (Δ ⟪ f ⟫ δ) j) i

