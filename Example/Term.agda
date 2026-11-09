{-# OPTIONS --cubical=uip --guardedness #-}

open import Example.Category

module Example.Term {C : Category} where

open import Function.Base using (id)
open import Example.Context
open import Example.Type
open import Cubical.Foundations.Prelude hiding (_,_)
open import Example.SubstitutionEquality

open Category C

private
  variable
    x : Obj
    Γ Δ Θ : Ctx C
    T S S' R : Ty Γ

record Tm (Γ : Ctx C) (T : Ty Γ) : Set where
  no-eta-equality
  constructor MkTm
  field
    term : (x : Obj) (γ : Γ ⟨ x ⟩) → T ⟨ x , γ ⟩
    naturality : ∀ {x y} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
                 (f : Hom x y) (eγ : Γ ⟪ f ⟫ γy ≡ γx)
               → T ⟪ f , eγ ⟫ (term y γy) ≡ term x γx

open Tm public renaming (term to infix 15 _⟨_,_⟩')

private
  variable
    t t' : Tm Γ T
    s s' : Tm Γ S

ι[_]_ : T ≡ S → Tm Γ S → Tm Γ T
ι[ p ] s = subst (Tm _) (λ i → p (~ i)) s

ι⁻¹[_]_ : T ≡ S → Tm Γ T → Tm Γ S
ι⁻¹[ p ] t = subst (Tm _) p t


-- substitution of terms
_[_]' : Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
(t [ σ ]') ⟨ x , δ ⟩' = t ⟨ x , func σ δ ⟩'
naturality (t [ σ ]') f eγ = naturality t f _

tm-subst-cong-tm : (σ : Δ ⇒ Γ) → t ≡ s → t [ σ ]' ≡ s [ σ ]'
tm-subst-cong-tm σ e i = e i [ σ ]'
