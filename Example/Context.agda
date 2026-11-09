{-# OPTIONS --cubical=uip --guardedness #-}

module Example.Context where
open import Example.Category
open import Cubical.Foundations.Prelude
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Agda.Builtin.Cubical.SqFill renaming (prim^sqFill to sqFill)

record Ctx (C : Category) : Set₁ where
  no-eta-equality
  open Category C
  field
    ctx-cell : Obj → Set
    ctx-hom  : {x y : Obj} → Hom x y → ctx-cell y → ctx-cell x
    ctx-id   : {x : Obj} {γ : ctx-cell x} → ctx-hom hom-id γ ≡ γ
    ctx-comp : {x y z : Obj} {f : Hom x y} {g : Hom y z} {γ : ctx-cell z}
             → ctx-hom (g · f) γ ≡ ctx-hom f (ctx-hom g γ)
  
open Ctx public renaming (ctx-cell to _⟨_⟩; ctx-hom to _⟪_⟫_)

module _ {C : Category} where
  infix 10 _⇒_
  infix 20 _⊚_
  open Category C
  private
    variable
      x y z : Obj
      Δ Γ Θ : Ctx C

  strong-ctx-comp : (Γ : Ctx C) {f : Hom x y} {g : Hom y z}
                    {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
                  → (eq-zy : Γ ⟪ g ⟫ γz ≡ γy) (eq-yx : Γ ⟪ f ⟫ γy ≡ γx)
                  → Γ ⟪ g · f ⟫ γz ≡ γx
  strong-ctx-comp Γ {f} {g} {γz} {γy} {γx} eq-zy eq-yx =
      Γ ⟪ g · f ⟫ γz
    ≡⟨ ctx-comp Γ ⟩
      Γ ⟪ f ⟫ (Γ ⟪ g ⟫ γz)
    ≡⟨ cong (Γ ⟪ f ⟫_) eq-zy ⟩
      Γ ⟪ f ⟫ γy
    ≡⟨ eq-yx ⟩
      γx ∎

  record _⇒_ (Δ : Ctx C) (Γ : Ctx C) : Set where
    no-eta-equality
    field
      func       : {x : Obj} → Δ ⟨ x ⟩ → Γ ⟨ x ⟩
      naturality : {x y : Obj} {f : Hom x y} {δ : Δ ⟨ y ⟩}
                 → Γ ⟪ f ⟫ (func δ) ≡ func (Δ ⟪ f ⟫ δ)

  ctx-cong-2-2 : (Γ : Ctx C) {x y y' z : Obj}
                 {f : Hom x y} {g : Hom y z} {f' : Hom x y'} {g' : Hom y' z} →
                 g · f ≡ g' · f' →
                 {γ : Γ ⟨ z ⟩} →
                 Γ ⟪ f ⟫ (Γ ⟪ g ⟫ γ) ≡ Γ ⟪ f' ⟫ (Γ ⟪ g' ⟫ γ)
  ctx-cong-2-2 Γ e = sym (ctx-comp Γ) ∙ (cong (Γ ⟪_⟫ _) e) ∙ (ctx-comp Γ)

  -- naturality condition for substitutions: let σ : Δ ⇒ Γ
  --
  --             func
  --     Δ(x) ----------> Γ(x)
  --      ∧                ∧
  --      |                |
  --      |Δ(f)            |Γ(f)
  --      |                |
  --      |                |
  -- δ ∈ Δ(y) ----------> Γ(y)
  --             func

  open _⇒_ public

  id-subst : (Γ : Ctx C) → Γ ⇒ Γ
  id-subst Γ .func = id
  id-subst Γ .naturality = refl

  -- composition of substitutions: let f : x → y (in Hom(C)), σ : Δ ⇒ Γ, τ : Γ → θ (in Psh(C))
  --
  --           func σ           func τ
  -- δ ∈ Δ(y) ----------> Γ(y) ----------> Θ(y)
  --      |                |                |
  --      |                |                |
  --      |Δ(f)            |Γ(f)            |Θ(f)
  --      |                |                |
  --      ∨                |                ∨
  --     Δ(x) ----------> Γ(x) ----------> Θ(x)
  --           func σ           func τ

  _⊚_ : Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
  func (τ ⊚ σ) = func τ ∘ func σ
  naturality (_⊚_ {Γ = Γ}{Θ = Θ}{Δ = Δ} τ σ) {f = f} {δ = δ} =
      Θ ⟪ f ⟫ (func τ (func σ δ))
    ≡⟨ naturality τ ⟩
      func τ (Γ ⟪ f ⟫ func σ δ)
    ≡⟨ cong (func τ) (naturality σ) ⟩
      func τ (func σ (Δ ⟪ f ⟫ δ)) ∎

  -- postulate
  --   uip : ∀{ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
  uip : ∀{ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
  uip {A = A} p q = sqFill A p q refl refl

  id-subst-unitʳ : (σ : Δ ⇒ Γ) → σ ⊚ id-subst Δ ≡ σ
  id-subst-unitʳ σ i .func = func σ
  id-subst-unitʳ {Δ = Δ} σ i .naturality = uip (naturality (σ ⊚ id-subst Δ)) (naturality σ) i

  id-subst-unitˡ : (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≡ σ
  id-subst-unitˡ σ i .func = func σ
  id-subst-unitˡ {Γ = Γ} σ i .naturality = uip (naturality (id-subst Γ ⊚ σ)) (naturality σ) i

  ⊚-assoc : {Γ₁ : Ctx C} {Γ₂ : Ctx C} {Γ₃ : Ctx C} {Γ₄ : Ctx C}
            {σ₃₄ : Γ₃ ⇒ Γ₄} {σ₂₃ : Γ₂ ⇒ Γ₃} {σ₁₂ : Γ₁ ⇒ Γ₂}
          → (σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂ ≡ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
  ⊚-assoc {σ₃₄ = σ₃₄} {σ₂₃ = σ₂₃} {σ₁₂ = σ₁₂} i .func z =
    func σ₃₄ (func σ₂₃ (func σ₁₂ z))
  ⊚-assoc {σ₃₄ = σ₃₄} {σ₂₃ = σ₂₃} {σ₁₂ = σ₁₂} i .naturality =
    uip (naturality ((σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂)) (naturality (σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂))) i

  ⊚-congʳ : {τ : Γ ⇒ Θ} {σ σ' : Δ ⇒ Γ} → σ ≡ σ' → τ ⊚ σ ≡ τ ⊚ σ'
  ⊚-congʳ {τ = τ} σ=σ' i = τ ⊚ (σ=σ' i)

  ⊚-congˡ : {τ τ' : Γ ⇒ Θ} {σ : Δ ⇒ Γ} → τ ≡ τ' → τ ⊚ σ ≡ τ' ⊚ σ
  ⊚-congˡ {σ = σ} τ=τ' i = (τ=τ' i) ⊚ σ
  
  ◇ : Ctx C
  ◇ ⟨ _ ⟩ = ⊤
  ◇ ⟪ _ ⟫ _ = tt
  ◇ .ctx-id = refl
  ◇ .ctx-comp = refl

  !◇ : (Γ : Ctx C) → Γ ⇒ ◇
  !◇ Γ .func _ = tt
  !◇ Γ .naturality _ = tt

  ◇-terminal : (Γ : Ctx C) (σ τ : Γ ⇒ ◇) → σ ≡ τ
  ◇-terminal Γ σ τ _ .func _ = tt
  ◇-terminal Γ σ τ _ .naturality = refl
