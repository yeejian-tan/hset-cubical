{-# OPTIONS --cubical=uip --guardedness #-}

open import Example.Category

module Example.Function {C : Category} where

open import Cubical.Foundations.Prelude renaming (_,_ to [_,_])
open import Function.Base using (_∘_)
open import Agda.Builtin.Cubical.SqFill renaming (prim^sqFill to sqFill)

open import Example.Context
open import Example.Type
open import Example.Term
open import Example.ContextExtension
open Category C

private
  variable
    x y z : Obj
    Γ Δ : Ctx C
    T T' S S' : Ty Γ

infixr 12 _⇛_
-- infixr 4 lam[_∈_]_

record PshFun {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) (z : Obj) (γ : Γ ⟨ z ⟩) : Set where
  constructor MkFun
  field
    _$⟨_,_⟩_ : ∀ {y} (ρ : Hom y z) {γ' : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ ⟫ γ ≡ γ') →
               T ⟨ y , γ' ⟩ → S ⟨ y , γ' ⟩
    naturality : ∀ {x y} {ρ-xy : Hom x y} {ρ-yz : Hom y z} {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} →
                 {eγ-zy : Γ ⟪ ρ-yz ⟫ γ ≡ γy} {eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx} {t : T ⟨ y , γy ⟩} →
                 _$⟨_,_⟩_ (ρ-yz · ρ-xy) (strong-ctx-comp Γ eγ-zy eγ-yx) (T ⟪ ρ-xy , eγ-yx ⟫ t) ≡
                   S ⟪ ρ-xy , eγ-yx ⟫ (_$⟨_,_⟩_ ρ-yz eγ-zy t)
  infix 13 _$⟨_,_⟩_
open PshFun public

$-cong : {T : Ty Γ} {S : Ty Γ}
         {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} (f : PshFun T S y γy)
         {ρ ρ' : Hom x y} (eρ : ρ ≡ ρ')
         {eγ : Γ ⟪ ρ ⟫ γy ≡ γx} {eγ' : Γ ⟪ ρ' ⟫ γy ≡ γx}
         {t : T ⟨ x , γx ⟩} →
         f $⟨ ρ , eγ ⟩ t ≡ f $⟨ ρ' , eγ' ⟩ t
$-cong {Γ = Γ} {γx = γx} {γy = γy} f eρ {eγ = eγ} {eγ' = eγ'} {t = t} i =
  f $⟨ eρ i , sqFill (Γ ⟨ _ ⟩) eγ eγ' (cong (Γ ⟪_⟫ γy) eρ) refl i ⟩ t

-- ExtensionalityImplicit : (a b : Level) → Set _
-- ExtensionalityImplicit a b =
--   {A : Set a} {B : A → Set b} {f g : {x : A} → B x} →
--   (∀ {x} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

-- funextI : ∀ {ℓ ℓ'} → ExtensionalityImplicit ℓ ℓ'
-- funextI e i {x} = e {x} i

to-pshfun-eq : {T : Ty Γ} {S : Ty Γ}
               {γ : Γ ⟨ y ⟩} {f g : PshFun T S y γ} →
               (∀ {x} (ρ : Hom x y) {γ'} (eγ : Γ ⟪ ρ ⟫ γ ≡ γ') t →
                   f $⟨ ρ , eγ ⟩ t ≡ g $⟨ ρ , eγ ⟩ t) →
               f ≡ g
_$⟨_,_⟩_ (to-pshfun-eq e i) {y} ρ {γ'} eγ t = e ρ eγ t i
to-pshfun-eq {Γ = Γ} {T = T} {S = S} {f = f} {g = g} e i .naturality
  {ρ-xy = ρ-xy} {ρ-yz = ρ-yz} {eγ-zy = eγ-zy} {eγ-yx = eγ-yx} {t = t} =
  sqFill (S ⟨ _ , _ ⟩)
         (naturality f)
         (naturality g)
         (e (ρ-yz · ρ-xy) (strong-ctx-comp Γ eγ-zy eγ-yx) (T ⟪ ρ-xy , eγ-yx ⟫ t))
         (cong (S ⟪ ρ-xy , eγ-yx ⟫_) (e ρ-yz eγ-zy t))
         i

lower-presheaffunc : {T : Ty Γ} {S : Ty Γ} (ρ-yz : Hom y z)
                     {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ-yz ⟫ γz ≡ γy) →
                     PshFun T S z γz → PshFun T S y γy
lower-presheaffunc {Γ = Γ}{y = y}{z = z}{T = T}{S = S} ρ-yz {γz}{γy} eγ-zy f = MkFun g g-nat
  where
    g : ∀ {x} (ρ-xy : Hom x y) {γx} (eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx) →
        T ⟨ x , γx ⟩ → S ⟨ x , γx ⟩
    g ρ-xy eγ-yx = f $⟨ ρ-yz · ρ-xy , strong-ctx-comp Γ eγ-zy eγ-yx ⟩_
    g-nat : ∀ {w x} {ρ-wx : Hom w x} {ρ-xy : Hom x y} {γx : Γ ⟨ x ⟩} {γw : Γ ⟨ w ⟩}
            {eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx} {eγ-xw : Γ ⟪ ρ-wx ⟫ γx ≡ γw} {t : T ⟨ x , γx ⟩} → _
    g-nat {ρ-wx = ρ-wx}{ρ-xy}{eγ-yx = eγ-yx}{eγ-xw}{t = t} =
        f $⟨ ρ-yz · (ρ-xy · ρ-wx) , strong-ctx-comp Γ eγ-zy (strong-ctx-comp Γ eγ-yx eγ-xw) ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≡⟨ sym ($-cong f ·-assoc) ⟩
        f $⟨ (ρ-yz · ρ-xy) · ρ-wx , strong-ctx-comp Γ (strong-ctx-comp Γ eγ-zy eγ-yx) eγ-xw ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≡⟨ naturality f ⟩
        (S ⟪ ρ-wx , eγ-xw ⟫ (f $⟨ ρ-yz · ρ-xy , strong-ctx-comp Γ eγ-zy eγ-yx ⟩ t)) ∎

_⇛_ : {Γ : Ctx C} → Ty Γ → Ty Γ → Ty Γ
_⇛_ {Γ = Γ} T S ⟨ z , γ ⟩ = PshFun T S z γ
_⟪_,_⟫_ (T ⇛ S) = lower-presheaffunc
ty-id (_⇛_ {Γ = Γ} T S) {t = f} = to-pshfun-eq (λ _ eγ _ → $-cong f hom-id-l)
ty-comp (_⇛_ {Γ = Γ} T S) {t = f} = to-pshfun-eq (λ _ _ _ → $-cong f ·-assoc)

lam : (T : Ty Γ) → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
lam {S = S} T b ⟨ z , γz ⟩' = MkFun (λ ρ-yz {γy} eγ t → b ⟨ _ , [ γy , t ] ⟩')
                                    (λ {x = x}{y}{ρ-xy}{_}{γx}{γy}{eγ-zy}{eγ-yx}{t} →
    b ⟨ x , [ γx , T ⟪ ρ-xy , eγ-yx ⟫ t ] ⟩'
  ≡⟨ sym (naturality b ρ-xy (to-Σ-ty-eq T eγ-yx (ty-cong-2-1 T hom-id-r))) ⟩
    S ⟪ ρ-xy , _ ⟫ b ⟨ y , [ γy , t ] ⟩'
  ≡⟨ ty-cong S refl ⟩
    S ⟪ ρ-xy , eγ-yx ⟫ b ⟨ y , [ γy , t ] ⟩' ∎)
naturality (lam T b) _ _ = to-pshfun-eq (λ _ _ _ → refl)

_€⟨_,_⟩_ : Tm Γ (T ⇛ S) → (x : Obj) (γ : Γ ⟨ x ⟩) → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
_€⟨_,_⟩_ {Γ = Γ} f x γ t = f ⟨ x , γ ⟩' $⟨ hom-id , ctx-id Γ ⟩ t

€-natural : (f : Tm Γ (T ⇛ S)) {ρ : Hom x y}
            {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ ρ ⟫ γy ≡ γx}
            {t : T ⟨ y , γy ⟩} →
            S ⟪ ρ , eγ ⟫ (f €⟨ y , γy ⟩ t) ≡ f €⟨ x , γx ⟩ (T ⟪ ρ , eγ ⟫ t)
€-natural {Γ = Γ}{T = T}{S = S} f {ρ}{γy}{γx}{eγ}{t} =
    S ⟪ ρ , eγ ⟫ (f ⟨ _ , γy ⟩' $⟨ hom-id , ctx-id Γ ⟩ t)
  ≡⟨ sym (naturality (f ⟨ _ , γy ⟩')) ⟩
    f ⟨ _ , γy ⟩' $⟨ hom-id · ρ , strong-ctx-comp Γ (ctx-id Γ) eγ ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ $-cong (f ⟨ _ , γy ⟩') (hom-id-l ∙ (sym hom-id-r)) ⟩
    f ⟨ _ , γy ⟩' $⟨ ρ · hom-id , strong-ctx-comp Γ eγ (ctx-id Γ) ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ cong (λ x → x $⟨ _ , _ ⟩ _) (naturality f ρ eγ) ⟩
    f ⟨ _ , γx ⟩' $⟨ hom-id , ctx-id Γ ⟩ (T ⟪ ρ , eγ ⟫ t) ∎

app : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
app f t ⟨ y , γ ⟩' = f €⟨ y , γ ⟩ (t ⟨ y , γ ⟩')
naturality (app {Γ = Γ}{T = T}{S = S} f t) {γy = γy}{γx} ρ eγ =
    S ⟪ ρ , eγ ⟫ (f €⟨ _ , γy ⟩ (t ⟨ _ , γy ⟩'))
  ≡⟨ €-natural f ⟩
    f €⟨ _ , γx ⟩ (T ⟪ ρ , eγ ⟫ (t ⟨ _ , γy ⟩'))
  ≡⟨ cong (f €⟨ _ , γx ⟩_) (naturality t ρ eγ) ⟩
    f €⟨ _ , γx ⟩ (t ⟨ _ , γx ⟩') ∎

infixl 10 _$_
_$_ = app

-- ap : Tm Γ (T ⇛ S) → Tm (Γ ,, T) (S [ π ])
-- ap f ⟨ x , [ γ , t ] ⟩' = f €⟨ x , γ ⟩ t
-- naturality (ap {T = T} f) ρ refl = {!!} -- trans (€-natural f) (cong (f €⟨ _ , _ ⟩_) (ty-cong T refl))

module _ (σ : Δ ⇒ Γ) (T : Ty Γ) (S : Ty Γ) {δ : Δ ⟨ z ⟩} where
  pshfun-subst-from : PshFun T S z (func σ δ) → PshFun (T [ σ ]) (S [ σ ]) z δ
  _$⟨_,_⟩_ (pshfun-subst-from f) ρ-yz eδ t = f $⟨ ρ-yz , (naturality σ) ∙ (cong (func σ) eδ) ⟩ t
  naturality (pshfun-subst-from f) = ($-cong f refl) ∙ (naturality f)

  pshfun-subst-to : PshFun (T [ σ ]) (S [ σ ]) z δ → PshFun T S z (func σ δ)
  _$⟨_,_⟩_ (pshfun-subst-to f) ρ-yz {γ'} eδ t = ty-ctx-subst S proof (
                                                 f $⟨ ρ-yz , refl ⟩
                                                 ty-ctx-subst T (sym proof) t)
    where
      proof : func σ (Δ ⟪ ρ-yz ⟫ δ) ≡ γ'
      proof = (sym (naturality σ)) ∙ eδ
  naturality (pshfun-subst-to f) {ρ-xy = ρ-xy}{ρ-yz} {eγ-yx = eγ-yx} {t = t} =
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz · ρ-xy , refl ⟩ (T ⟪ hom-id , _ ⟫ T ⟪ ρ-xy , eγ-yx ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫_ ∘ f $⟨ ρ-yz · ρ-xy , refl ⟩_) (ty-cong-2-2 T (hom-id-r ∙ (sym hom-id-l))) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz · ρ-xy , refl ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f refl) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz · ρ-xy , _ ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) (naturality f {eγ-yx = sym (ctx-comp Δ)}) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ ρ-xy , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡⟨ ty-cong-2-2 S (hom-id-r ∙ (sym hom-id-l)) ⟩
      S ⟪ ρ-xy , eγ-yx ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t) ∎
    where
      α = _
      β = _

module _ {T : Ty Γ} {S : Ty Γ} (σ : Δ ⇒ Γ) where
  pshfun-subst-from-natural :
    {x y : Obj} {ρ-yz : Hom x y} {δy : Δ ⟨ y ⟩} {δx : Δ ⟨ x ⟩} {eδ : Δ ⟪ ρ-yz ⟫ δy ≡ δx}
    (f : PshFun T S y (func σ δy)) →
    ((T [ σ ]) ⇛ (S [ σ ])) ⟪ ρ-yz , eδ ⟫ (pshfun-subst-from σ T S f) ≡
    pshfun-subst-from σ T S (((T ⇛ S) [ σ ]) ⟪ ρ-yz , eδ ⟫ f)
  pshfun-subst-from-natural f = to-pshfun-eq (λ _ _ _ → $-cong f refl)

  pshfun-subst-to-natural :
    {x y : Obj} {ρ-yz : Hom x y} {δy : Δ ⟨ y ⟩} {δx : Δ ⟨ x ⟩} {eδ : Δ ⟪ ρ-yz ⟫ δy ≡ δx}
    (f : PshFun (T [ σ ]) (S [ σ ]) y δy) →
    ((T ⇛ S) [ σ ]) ⟪ ρ-yz , eδ ⟫ (pshfun-subst-to σ T S f) ≡
    pshfun-subst-to σ T S (((T [ σ ]) ⇛ (S [ σ ])) ⟪ ρ-yz , eδ ⟫ f)
  pshfun-subst-to-natural {ρ-yz = ρ-yz} f = to-pshfun-eq λ ρ-xy eγ t →
    let α = _
        β = _
        ζ = _
        α' = _
        β' = _
        ζ' = _
    in
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz · ρ-xy , β ⟩ (T ⟪ hom-id , ζ ⟫ t)
    ≡⟨ sym (cong (S ⟪ hom-id , α ⟫_ ∘ f $⟨ ρ-yz · ρ-xy , β ⟩_) (ty-cong-2-1 T hom-id-l)) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz · ρ-xy , β ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f (sym hom-id-r)) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ (ρ-yz · ρ-xy) · hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) (naturality f {eγ-yx = (ctx-id Δ) ∙ (sym β')}) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz · ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t)
    ≡⟨ ty-cong-2-1 S hom-id-r ⟩
      S ⟪ hom-id , α' ⟫ f $⟨ ρ-yz · ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t) ∎

  ⇛-natural-from : Tm Δ ((T ⇛ S) [ σ ]) → Tm Δ ((T [ σ ]) ⇛ (S [ σ ]))
  ⇛-natural-from t ⟨ z , δ ⟩' = pshfun-subst-from σ T S (t ⟨ z , δ ⟩')
  ⇛-natural-from t .naturality ρ eδ =
    pshfun-subst-from-natural (t ⟨ _ , _ ⟩') ∙ cong (pshfun-subst-from σ T S) (naturality t ρ eδ)

  ⇛-natural-to : Tm Δ ((T [ σ ]) ⇛ (S [ σ ])) → Tm Δ ((T ⇛ S) [ σ ])
  ⇛-natural-to t ⟨ z , δ ⟩' = pshfun-subst-to σ T S (t ⟨ z , δ ⟩')
  ⇛-natural-to t .naturality ρ eδ =
    pshfun-subst-to-natural (t ⟨ _ , _ ⟩') ∙ cong (pshfun-subst-to σ T S) (naturality t ρ eδ)

-- example from pp. 206 of Joris Ceulemans' PhD thesis
apply-twice : {A : Ty Γ} → Tm Γ ((A ⇛ A) ⇛ A ⇛ A)
apply-twice {A = A} =
  lam (A ⇛ A)
    (⇛-natural-to π
      (lam (A [ π ])
        (let f = ⇛-natural-from π ((⇛-natural-from π ξ) [ π ]')
         in app f (app f ξ))))

module Test {Γ : Ctx C} {X : Set} (h : X → X) (v : X) where

  ConstTy : Ty Γ
  ConstTy ⟨ _ , _ ⟩ = X
  ConstTy ⟪ _ , _ ⟫ x = x
  ConstTy .ty-id = refl
  ConstTy .ty-comp = refl

  const-tm : Tm Γ ConstTy
  const-tm ⟨ _ , _ ⟩' = v
  const-tm .naturality _ _ = refl

  const-fun : Tm Γ (ConstTy ⇛ ConstTy)
  const-fun ⟨ _ , _ ⟩' $⟨ _ , _ ⟩ x = h x
  (const-fun ⟨ _ , _ ⟩') .naturality = refl
  const-fun .naturality _ _ = to-pshfun-eq (λ _ _ _ → refl)

  test-apply-twice : ∀ {z} {γ : Γ ⟨ z ⟩}
                   → (app (app apply-twice const-fun) const-tm) ⟨ z , γ ⟩' ≡ h (h v)
  test-apply-twice = refl
