{-# OPTIONS --cubical=uip --guardedness #-}

open import Example.Category

module Example.Type {C : Category} where

open import Data.Product renaming (_,_ to [_,_])
open import Example.Context
open import Cubical.Foundations.Prelude hiding (_,_)
open import Example.SubstitutionEquality using (sqFill; uip)

open import Function hiding (_⟨_⟩_; _↣_)

open Category C

infix 10 _↣_
infixl 20 _⊙_

private
  variable
    x y z w : Obj
    Δ Γ Θ : Ctx C

record Ty (Γ : Ctx C) : Set₁ where
  constructor MkTy
  field
    ty-cell : (x : Obj) (γ : Γ ⟨ x ⟩) → Set
    ty-hom : {x y : Obj} (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
           → Γ ⟪ f ⟫ γy ≡ γx → ty-cell y γy → ty-cell x γx
    ty-cong : {f f' : Hom x y} (eq-hom : f ≡ f')
              {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
              {eq-γ : Γ ⟪ f ⟫ γy ≡ γx} {eq-γ' : Γ ⟪ f' ⟫ γy ≡ γx}
              {t : ty-cell y γy}
            → ty-hom f eq-γ t ≡ ty-hom f' eq-γ' t
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

Σ-ty-eq : ∀ {ℓ} {A : Set ℓ} (T : Ty Γ)
          {a b : A} (e : a ≡ b)
          {γ : A → Γ ⟨ x ⟩}
          {ta : T ⟨ x , γ a ⟩} {tb : T ⟨ x , γ b ⟩} → ty-ctx-subst T (cong γ e) ta ≡ tb
        → [ a , ta ] ≡ [ b , tb ]
Σ-ty-eq T {a = a} e {γ = γ} {ta = ta} et =
  J (λ b' e' → (tb' : T ⟨ _ , γ b' ⟩) (et' : ty-ctx-subst T (cong γ e') ta ≡ tb') → [ a , ta ] ≡ [ b' , tb' ])
    (λ tb et' → cong ([ a ,_]) (sym (ty-id T) ∙ ty-cong T refl ∙ et'))
    e _ et

record _↣_ {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) : Set where
  field
    func : ∀ {x} {γ} → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
    naturality : ∀ {x y} {f : Hom x y}
                 {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
                 {eγ : Γ ⟪ f ⟫ γy ≡ γx} {t : T ⟨ y , γy ⟩}
               → S ⟪ f , eγ ⟫ (func t) ≡ func (T ⟪ f , eγ ⟫ t)

open _↣_ public

id-trans : (T : Ty Γ) → T ↣ T
func (id-trans T) = id
naturality (id-trans T) = refl

_⊙_ : S ↣ T → R ↣ S → R ↣ T
(φ ⊙ η) .func = func φ ∘ func η
(φ ⊙ η) .naturality = naturality φ ∙ cong (func φ) (naturality η)

_[_] : Ty Γ → Δ ⇒ Γ → Ty Δ
(T [ σ ]) .ty-cell x δ = T ⟨ x , func σ δ ⟩
(T [ σ ]) .ty-hom {x} {y} f {γy} {γx} eγ-yx t = T ⟪ f , (naturality σ) ∙ (cong (func σ) eγ-yx) ⟫ t
(T [ σ ]) .ty-cong f = ty-cong T f
(T [ σ ]) .ty-id = strong-ty-id T
(T [ σ ]) .ty-comp = strong-ty-comp T

