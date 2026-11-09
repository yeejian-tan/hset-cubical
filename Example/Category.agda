{-# OPTIONS --cubical=no-glue --guardedness #-}

module Example.Category where

open import Cubical.Foundations.Prelude

record Category : Set₁ where
  field
    Obj    : Set
    Hom    : Obj → Obj → Set
    hom-id : {x : Obj} → Hom x x
    _·_    : {x y z : Obj} → Hom y z → Hom x y → Hom x z
  infixr 9 _·_
  field
    ·-assoc  : {x y z w : Obj} (f : Hom x y) (g : Hom y z) (h : Hom z w)
             → (h · g) · f ≡ h · (g · f)
    hom-id-r : {x y : Obj} {f : Hom x y} → f · hom-id ≡ f
    hom-id-l : {x y : Obj} {f : Hom x y} → hom-id · f ≡ f

open Category
category-composition : (C : Category) {x y z : Obj C} →
                       Hom C y z → Hom C x y → Hom C x z
category-composition = _·_
syntax category-composition C g f = g ·[ C ] f

_^op : Category → Category
(C ^op) .Obj = Obj C 
(C ^op) .Hom x y = Hom C y x
(C ^op) .hom-id  = hom-id C
(C ^op) ._·_ f g = _·_ C g f
(C ^op) .·-assoc f g h = sym (·-assoc C h g f)
(C ^op) .hom-id-r = hom-id-l C 
(C ^op) .hom-id-l = hom-id-r C

record Functor (C D : Category) : Set where
  open Category
  field
    obj      : Obj C → Obj D
    hom      : {x y : Obj C} → Hom C x y → Hom D (obj x) (obj y)
    id-law   : {x : Obj C} → hom (hom-id C {x}) ≡ hom-id D {obj x}
    comp-law : {x y z : Obj C} {f : Hom C x y} {g : Hom C y z}
             → hom (g ·[ C ] f) ≡ (hom g) ·[ D ] (hom f)

id-functor : {C : Category} → Functor C C
id-functor .Functor.obj x  = x
id-functor .Functor.hom f  = f
id-functor .Functor.id-law   = refl
id-functor .Functor.comp-law = refl

record NatTransf {C D : Category} (F G : Functor C D) : Set where
  open Category
  open Functor
  field
    op         : (x : Obj C) → Hom D (obj F x) (obj G x)
    naturality : {x y : Obj C} (f : Hom C x y)
               → op y ·[ D ] hom F f ≡ hom G f ·[ D ] op x

module _ {C D : Category} where
  id-nattransf : {F : Functor C D} → NatTransf F F
  id-nattransf .NatTransf.op x = hom-id D
  id-nattransf .NatTransf.naturality f = (hom-id-l D) ∙ (sym (hom-id-r D))
