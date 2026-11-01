{-# OPTIONS --without-K --safe #-}
module A2bEqp where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public

_×_ : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
A × B = Σ A (λ _ → B)

ap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
ap f refl = refl

ap-binary : {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} (f : A → B → C)
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') → f x y ＝ f x' y'
ap-binary f refl refl = refl

_∙_ : {l : Level} {A : Set l} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
refl ∙ q = q

tr : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x y : A} → x ＝ y → B x → B y
tr B refl b = b

module _ {l1 l2 : Level} {A : Set l1} {B : A → Set l2} where

  eq-pair-eq-fiber : {x : A} {s t : B x} → s ＝ t → pair x s ＝ pair x t
  eq-pair-eq-fiber {x} = ap {B = Σ A B} (pair x)

  eq-pair-Σ :
    {s t : Σ A B} (α : pr1 s ＝ pr1 t) → tr B α (pr2 s) ＝ pr2 t → s ＝ t
  eq-pair-Σ refl = eq-pair-eq-fiber

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} where

  Eq-product : (s t : A × B) → Set (l1 ⊔ l2)
  Eq-product s t = (pr1 s ＝ pr1 t) × (pr2 s ＝ pr2 t)

  eq-pair' : {s t : A × B} → Eq-product s t → s ＝ t
  eq-pair' (pair p q) = ap-binary pair p q

  eq-pair : {s t : A × B} → pr1 s ＝ pr1 t → pr2 s ＝ pr2 t → s ＝ t
  eq-pair p q = eq-pair' (pair p q)

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) where

  fiber : Set (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ b)

  Eq-fiber : fiber → fiber → Set (l1 ⊔ l2)
  Eq-fiber s t = Σ (pr1 s ＝ pr1 t) (λ α → (ap f α ∙ pr2 t) ＝ pr2 s)

  eq-Eq-fiber-uncurry : {s t : fiber} → Eq-fiber s t → s ＝ t
  eq-Eq-fiber-uncurry (pair refl refl) = refl
