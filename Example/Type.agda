{-# OPTIONS --cubical=uip --guardedness #-}

open import Example.Category

module Example.Type {C : Category} where

open import Example.Context
open import Cubical.Foundations.Prelude renaming (_,_ to [_,_])
open import Agda.Builtin.Cubical.SqFill renaming (prim^sqFill to sqFill)
open import Example.SubstitutionEquality 

open import Function.Base hiding (_⟨_⟩_)

open Category C

-- infix 10 _↣_
-- infix 1 _≅ᵗʸ_
-- infixl 20 _⊙_

private
  variable
    x y z w : Obj
    Δ Γ Θ : Ctx C

record Ty (Γ : Ctx C) : Set₁ where
  no-eta-equality
  constructor MkTy
  field
    ty-cell : (x : Obj) (γ : Γ ⟨ x ⟩) → Set
    ty-hom : {x y : Obj} (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
           → Γ ⟪ f ⟫ γy ≡ γx → ty-cell y γy → ty-cell x γx
    ty-id : {x : Obj} {γ : Γ ⟨ x ⟩} {t : ty-cell x γ}
          → ty-hom hom-id (ctx-id Γ) t ≡ t
    ty-comp : {x y z : Obj} {f : Hom x y} {g : Hom y z}
              {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
            → {eq-γ-zy : Γ ⟪ g ⟫ γz ≡ γy} {eq-γ-yx : Γ ⟪ f ⟫ γy ≡ γx}
              {t : ty-cell z γz}
            → ty-hom (g · f) (strong-ctx-comp Γ eq-γ-zy eq-γ-yx) t ≡ ty-hom f eq-γ-yx (ty-hom g eq-γ-zy t)

open Ty public renaming (ty-cell to infix 15 _⟨_,_⟩; ty-hom to infixr 11 _⟪_,_⟫_)

private
  variable
    T S R : Ty Γ
    T1 T2 T3 T4 : Ty Γ

open Ty public

ty-cong : (T : Ty Γ) {f f' : Hom x y} (eq-hom : f ≡ f')
          {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
          {eq-γ : Γ ⟪ f ⟫ γy ≡ γx} {eq-γ' : Γ ⟪ f' ⟫ γy ≡ γx}
          {t : T ⟨ y , γy ⟩}
        → T ⟪ f , eq-γ ⟫ t ≡ T ⟪ f' , eq-γ' ⟫ t
ty-cong {Γ = Γ} T eq-hom {eq-γ = eq-γ} {eq-γ' = eq-γ'} {t} i =
  T ⟪ (eq-hom i) , sqFill (Γ ⟨ _ ⟩) eq-γ eq-γ' (cong (Γ ⟪_⟫ _) eq-hom) refl i ⟫ t

strong-ty-id : (T : Ty Γ) {γ : Γ ⟨ x ⟩} {eγ : Γ ⟪ hom-id ⟫ γ ≡ γ} {t : T ⟨ x , γ ⟩}
             → T ⟪ hom-id , eγ ⟫ t ≡ t
strong-ty-id T = ty-cong T refl ∙ ty-id T

strong-ty-comp : (T : Ty Γ) {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
                {eγ-zx : Γ ⟪ g · f ⟫ γz ≡ γx} {eγ-zy : Γ ⟪ g ⟫ γz ≡ γy} {eγ-yx : Γ ⟪ f ⟫ γy ≡ γx}
                {t : T ⟨ z , γz ⟩} →
                T ⟪ g · f , eγ-zx ⟫ t ≡ T ⟪ f , eγ-yx ⟫ T ⟪ g , eγ-zy ⟫ t
strong-ty-comp T = ty-cong T refl ∙ ty-comp T

ty-cong-2-1 : (T : Ty Γ)
              {f : Hom x y} {g : Hom y z} {h : Hom x z} (e-hom : g · f ≡ h)
              {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
              {ef : Γ ⟪ f ⟫ γy ≡ γx} {eg : Γ ⟪ g ⟫ γz ≡ γy} {eh : Γ ⟪ h ⟫ γz ≡ γx}
              {t : T ⟨ z , γz ⟩} →
              T ⟪ f , ef ⟫ (T ⟪ g , eg ⟫ t) ≡ T ⟪ h , eh ⟫ t
ty-cong-2-1 T {f}{g}{h} e-hom {t = t} = 
    T ⟪ f , _ ⟫ T ⟪ g , _ ⟫ t
  ≡⟨ sym (ty-comp T) ⟩
    T ⟪ g · f , _ ⟫ t
  ≡⟨ ty-cong T e-hom ⟩
    T ⟪ h , _ ⟫ t ∎

ty-cong-2-2 : (T : Ty Γ)
              {f : Hom x y} {f' : Hom x z} {g : Hom y w} {g' : Hom z w} (e-hom : g · f ≡ g' · f')
              {γw : Γ ⟨ w ⟩} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
              {ef : Γ ⟪ f ⟫ γy ≡ γx} {ef' : Γ ⟪ f' ⟫ γz ≡ γx}
              {eg : Γ ⟪ g ⟫ γw ≡ γy} {eg' : Γ ⟪ g' ⟫ γw ≡ γz}
              {t : T ⟨ w , γw ⟩} →
              T ⟪ f , ef ⟫ (T ⟪ g , eg ⟫ t) ≡ T ⟪ f' , ef' ⟫ (T ⟪ g' , eg' ⟫ t)
ty-cong-2-2 T {f}{f'}{g}{g'} e-hom {t = t} = 
    T ⟪ f , _ ⟫ T ⟪ g , _ ⟫ t
  ≡⟨ sym (ty-comp T) ⟩
    T ⟪ g · f , _ ⟫ t
  ≡⟨ ty-cong T e-hom ⟩
    T ⟪ g' · f' , _ ⟫ t
  ≡⟨ ty-comp T ⟩
    T ⟪ f' , _ ⟫ T ⟪ g' , _ ⟫ t ∎

ty-ctx-subst : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} → γ ≡ γ' → T ⟨ x , γ ⟩ → T ⟨ x , γ' ⟩
ty-ctx-subst {Γ = Γ} T eq-γ t = T ⟪ hom-id , ctx-id Γ ∙ eq-γ ⟫ t

ty-ctx-subst-inverse-l : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} {eγ : γ ≡ γ'} {t : T ⟨ x , γ ⟩} →
                        ty-ctx-subst T (sym eγ) (ty-ctx-subst T eγ t) ≡ t
ty-ctx-subst-inverse-l T = (ty-cong-2-1 T hom-id-l) ∙ (ty-id T)

ty-ctx-subst-inverse-r : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} {eγ : γ ≡ γ'} {t : T ⟨ x , γ' ⟩} →
                        ty-ctx-subst T eγ (ty-ctx-subst T (sym eγ) t) ≡ t
ty-ctx-subst-inverse-r T = (ty-cong-2-1 T hom-id-l) ∙ (ty-id T)

to-Σ-ty-eq : ∀ {ℓ} {A : Set ℓ} (T : Ty Γ)
          {a b : A} (e : a ≡ b)
          {γ : A → Γ ⟨ x ⟩}
          {ta : T ⟨ x , γ a ⟩} {tb : T ⟨ x , γ b ⟩} → ty-ctx-subst T (cong γ e) ta ≡ tb
        → [ a , ta ] ≡ [ b , tb ]
to-Σ-ty-eq T {a = a} e {γ = γ} {ta = ta} et =
  J (λ b' e' → (tb' : T ⟨ _ , γ b' ⟩) (et' : ty-ctx-subst T (cong γ e') ta ≡ tb') → [ a , ta ] ≡ [ b' , tb' ])
    (λ tb et' → cong ([ a ,_]) (sym (ty-id T) ∙ ty-cong T refl ∙ et'))
    e _ et

from-Σ-ty-eq : ∀ {ℓ} {A : Set ℓ} (T : Ty Γ)
               {a b : A} {γ : A → Γ ⟨ x ⟩}
               {ta : T ⟨ x , γ a ⟩} {tb : T ⟨ x , γ b ⟩} →
               [ a , ta ] ≡ [ b , tb ] →
               Σ[ e ∈ a ≡ b ] (ty-ctx-subst T (cong γ e) ta ≡ tb)
from-Σ-ty-eq {Γ = Γ} {x = x} {A = A} T {a = a} {b = b} {γ = γ} {ta = ta} {tb = tb} eq =
  J (λ (p : Σ[ b' ∈ A ] (T ⟨ x , γ b' ⟩)) (eq' : [ a , ta ] ≡ p) →
       Σ[ e ∈ a ≡ fst p ] (ty-ctx-subst T (cong γ e) ta ≡ snd p))
    [ refl , strong-ty-id T ]
    eq

_[_] : Ty Γ → Δ ⇒ Γ → Ty Δ
T [ σ ] ⟨ x , δ ⟩ = T ⟨ x , func σ δ ⟩
_⟪_,_⟫_ (_[_] {Γ = Γ} T σ) f {δy}{δx} eγ-yx t = T ⟪ f , proof ⟫ t
  where
    proof : Γ ⟪ f ⟫ func σ δy ≡ func σ δx
    proof = (naturality σ) ∙ (cong (func σ) eγ-yx)
ty-id (T [ σ ]) = strong-ty-id T
ty-comp (T [ σ ]) = strong-ty-comp T

ty-subst-id : (T : Ty Γ) → T [ id-subst Γ ] ≡ T
ty-subst-id T i .ty-cell x γ = T ⟨ x , γ ⟩
ty-subst-id T i .ty-hom f eγ t =
  ty-cong T refl {eq-γ = refl ∙ cong id eγ} {eq-γ' = eγ} {t = t} i
ty-subst-id {Γ = Γ} T i .ty-id {t = t} =
  sqFill (T ⟨ _ , _ ⟩)
         (ty-id (T [ id-subst Γ ]))
         (ty-id T)
         (λ j → ty-subst-id T j .ty-hom hom-id (ctx-id Γ) t)
         refl
         i
ty-subst-id {Γ = Γ} T i .ty-comp {f = f} {g = g} {eq-γ-zy = eq-γ-zy} {eq-γ-yx = eq-γ-yx} {t = t} =
  sqFill (T ⟨ _ , _ ⟩)
         (ty-comp (T [ id-subst Γ ]))
         (ty-comp T)
         (λ j → ty-subst-id T j .ty-hom (g · f) (strong-ctx-comp Γ eq-γ-zy eq-γ-yx) t)
         (λ j → ty-subst-id T j .ty-hom f eq-γ-yx (ty-subst-id T j .ty-hom g eq-γ-zy t))
         i

ty-subst-comp : (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
ty-subst-comp T τ σ i .ty-cell x δ = T ⟨ x , func τ (func σ δ) ⟩
ty-subst-comp T τ σ i .ty-hom f eγ t =
  ty-cong T refl
    {eq-γ  = naturality τ ∙ cong (func τ) (naturality σ ∙ cong (func σ) eγ)}
    {eq-γ' = naturality (τ ⊚ σ) ∙ cong (func (τ ⊚ σ)) eγ}
    {t = t} i
ty-subst-comp {Δ = Δ} T τ σ i .ty-id {t = t} =
  sqFill (T ⟨ _ , _ ⟩)
         (ty-id (T [ τ ] [ σ ]))
         (ty-id (T [ τ ⊚ σ ]))
         (λ j → ty-subst-comp T τ σ j .ty-hom hom-id (ctx-id Δ) t)
         refl
         i
ty-subst-comp {Δ = Δ} T τ σ i .ty-comp {f = f} {g = g} {eq-γ-zy = eq-γ-zy} {eq-γ-yx = eq-γ-yx} {t = t} =
  sqFill (T ⟨ _ , _ ⟩)
         (ty-comp (T [ τ ] [ σ ]))
         (ty-comp (T [ τ ⊚ σ ]))
         (λ j → ty-subst-comp T τ σ j .ty-hom (g · f) (strong-ctx-comp Δ eq-γ-zy eq-γ-yx) t)
         (λ j → ty-subst-comp T τ σ j .ty-hom f eq-γ-yx (ty-subst-comp T τ σ j .ty-hom g eq-γ-zy t))
         i
