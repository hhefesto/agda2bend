{-# OPTIONS --without-K --safe #-}
module A2bEqq where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor _,_
  field
    pr1 : A
    pr2 : B pr1
open Σ public
infixr 3 _,_

id : {l : Level} {A : Set l} → A → A
id a = a

_∘_ : {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

_~_ : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (f g : (x : A) → B x) → Set (l1 ⊔ l2)
f ~ g = (x : _) → f x ＝ g x

refl-htpy : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

inv : {l : Level} {A : Set l} {x y : A} → x ＝ y → y ＝ x
inv refl = refl

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) where
  section : Set (l1 ⊔ l2)
  section = Σ (B → A) (λ g → (f ∘ g) ~ id)
  retraction : Set (l1 ⊔ l2)
  retraction = Σ (B → A) (λ h → (h ∘ f) ~ id)
  is-equiv : Set (l1 ⊔ l2)
  is-equiv = Σ section (λ _ → retraction)

module _ {l : Level} {A : Set l} where
  is-equiv-id : is-equiv (id {l} {A})
  pr1 (pr1 is-equiv-id) = id
  pr2 (pr1 is-equiv-id) = refl-htpy
  pr1 (pr2 is-equiv-id) = id
  pr2 (pr2 is-equiv-id) = refl-htpy

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (y : B) where
  fiber : Set (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ y)
  fiber' : Set (l1 ⊔ l2)
  fiber' = Σ A (λ x → y ＝ f x)

  map-equiv-fiber : fiber → fiber'
  pr1 (map-equiv-fiber (x , _)) = x
  pr2 (map-equiv-fiber (x , p)) = inv p

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) where
  map-equiv-total-fiber : Σ B (fiber f) → A
  map-equiv-total-fiber t = pr1 (pr2 t)

  map-inv-equiv-total-fiber : A → Σ B (fiber f)
  map-inv-equiv-total-fiber x = (f x , x , refl)

  is-retraction-map-inv-equiv-total-fiber :
    (map-inv-equiv-total-fiber ∘ map-equiv-total-fiber) ~ id
  is-retraction-map-inv-equiv-total-fiber (.(f x) , x , refl) = refl
