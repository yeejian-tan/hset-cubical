{-# OPTIONS --cubical=uip --guardedness #-}

open import Example.Category

module Example.SubstitutionEquality {C : Category} where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Agda.Builtin.Cubical.SqFill renaming (prim^sqFill to sqFill)
open import Example.Context

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


module _ {Δ Γ : Ctx C} where
  open Category C
  open Ctx
  open _⇒_

  -- equivalence of substitutions as defined in the original BiSikkel code:
  record _≅ˢ_ {Δ : Ctx C} {Γ : Ctx C} (σ τ : Δ ⇒ Γ) : Set where
    no-eta-equality
    field
      eq : ∀ {x} δ → func σ {x} δ ≡ func τ δ
  open _≅ˢ_ public

  -- given that funext is provable in cubical, we can easily "upgrade" the pointwise equality in the func field to propositional equality, then, we use sqFill to show that the naturality proofs of both substitutions are themselves equal
  equiv-to-prop : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → σ ≡ τ
  equiv-to-prop {σ} {τ} e i .func δ = e .eq δ i
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

  equiv-to-prop {σ} {τ} e i .naturality {x} {f = f} {δ = δ} = sqFill (Γ ⟨ x ⟩) (naturality σ) (naturality τ) (λ j → Γ ⟪ f ⟫ (e .eq δ j)) (λ j → e .eq (Δ ⟪ f ⟫ δ) j) i

