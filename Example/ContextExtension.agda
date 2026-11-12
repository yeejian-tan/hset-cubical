{-# OPTIONS --cubical=uip --guardedness #-}

open import Example.Category

module Example.ContextExtension {C : Category} where

open import Function.Base using (_∘_)
open import Cubical.Foundations.Prelude renaming (_,_ to [_,_])
open import Example.Context
open import Example.Type
open import Example.Term
open import Example.SubstitutionEquality

open Category C

infixl 15 _,,_
-- infixl 15 _,,_∈_

private
  variable
    Γ Δ Θ : Ctx C
    T S R : Ty Γ

_,,_ : (Γ : Ctx C) (T : Ty Γ) → Ctx C
(Γ ,, T) ⟨ x ⟩ = Σ[ γ ∈ Γ ⟨ x ⟩ ] (T ⟨ x , γ ⟩)
(Γ ,, T) ⟪ f ⟫ [ γ , t ] = [ Γ ⟪ f ⟫ γ , ty-hom T f refl t ]
(Γ ,, T) .ctx-id = to-Σ-ty-eq T (ctx-id Γ) ((ty-cong-2-1 T hom-id-l) ∙ (ty-id T))
(Γ ,, T) .ctx-comp = to-Σ-ty-eq T (ctx-comp Γ) (ty-cong-2-2 T hom-id-r)

π : Γ ,, T ⇒ Γ
π .func = fst
π .naturality = refl

ξ : Tm (Γ ,, T) (T [ π ])
ξ ⟨ _ , [ _ , t ] ⟩' = t
ξ {Γ = Γ} {T = T} .naturality {x = x} {y = y} {γy = [ γy , ty ]} {γx = γx} f eγ =
  J (λ γx' eγ' → T ⟪ f , refl ∙ cong fst eγ' ⟫ _ ≡ snd γx') (ty-cong T refl) eγ

ext-subst-to-subst : (Δ ⇒ Γ ,, T) → (Δ ⇒ Γ)
ext-subst-to-subst τ = π ⊚ τ

ext-subst-to-term : (τ : Δ ⇒ Γ ,, T) → Tm Δ (T [ π ⊚ τ ])
ext-subst-to-term τ ⟨ x , δ ⟩' = (ξ [ τ ]') ⟨ x , δ ⟩'
ext-subst-to-term {Δ = Δ} {T = T} τ .naturality {x = x} {y = y} {γy = γy} {γx = γx} f eγ =
    (T [ π ⊚ τ ]) ⟪ f , eγ ⟫ ((ξ [ τ ]') ⟨ y , γy ⟩')
  ≡⟨ ty-cong T refl ⟩
    (T [ π ] [ τ ]) ⟪ f , eγ ⟫ ((ξ [ τ ]') ⟨ y , γy ⟩')
  ≡⟨ naturality (ξ [ τ ]') f eγ ⟩
    (ξ [ τ ]') ⟨ x , γx ⟩' ∎

to-ext-subst : (T : Ty Γ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → (Δ ⇒ Γ ,, T)
to-ext-subst T σ t .func δ = [ func σ δ , t ⟨ _ , δ ⟩' ]
to-ext-subst {Δ = Δ} T σ t .naturality {f = f} {δ = δ} =
  to-Σ-ty-eq T (naturality σ) (ty-cong-2-1 T hom-id-r ∙ naturality t f refl)

syntax to-ext-subst T σ t = ⟨ σ , t ∈ T ⟩

to-ext-subst-syntax : {T : Ty Γ} (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → (Δ ⇒ Γ ,, T)
to-ext-subst-syntax σ t = to-ext-subst _ σ t
infixl 4 to-ext-subst-syntax
syntax to-ext-subst-syntax σ t = σ ∷ˢ t

ctx-ext-subst-β₁ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) → π ⊚ ⟨ σ , t ∈ T ⟩ ≡ σ
ctx-ext-subst-β₁ σ t i .func = func σ
ctx-ext-subst-β₁ {T = T} σ t i .naturality = uip (naturality (π ⊚ ⟨ σ , t ∈ T ⟩)) (naturality σ) i

-- ctx-ext-subst-β₂ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
--                    ξ [ ⟨ σ , t ∈ T ⟩ ]' ≡ ι[ ty-subst-cong-subst-2-1 T (ctx-ext-subst-β₁ σ t) ] t
-- ctx-ext-subst-β₂ {T = T} σ t = {!!}

ctx-ext-subst-η : (τ : Δ ⇒ Γ ,, T) → ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ≡ τ
ctx-ext-subst-η τ i .func = func τ
ctx-ext-subst-η {T = T} τ i .naturality = uip (naturality ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩) (naturality τ) i

conv-eta : (S : Ty (Γ ,, T)) (τ : Δ ⇒ Γ ,, T) →
         Tm Δ (S [ τ ]) →
         Tm Δ (S [ ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ])
conv-eta {Δ = Δ} S τ c = subst (Tm Δ) (λ i → S [ ctx-ext-subst-η τ (~ i) ]) c

tm-to-subst : Tm Γ T → Γ ⇒ Γ ,, T
tm-to-subst {Γ = Γ}{T = T} t = ⟨ id-subst Γ , t [ id-subst Γ ]' ∈ T ⟩

_/v = tm-to-subst

ctx-ext-subst-cong-tm : (σ : Δ ⇒ Γ) {t t' : Tm Δ (T [ σ ])} → t ≡ t' → ⟨ σ , t ∈ T ⟩ ≡ ⟨ σ , t' ∈ T ⟩
ctx-ext-subst-cong-tm {T = T} σ e i = ⟨ σ , (e i) ∈ T ⟩

/v-cong : {t t' : Tm Γ T} → t ≡ t' → t /v ≡ t' /v
/v-cong e = ctx-ext-subst-cong-tm _ (tm-subst-cong-tm _ e)
