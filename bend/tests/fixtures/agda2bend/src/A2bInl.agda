{-# OPTIONS --without-K --exact-split --no-postfix-projections --safe #-}
module A2bInl where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public
{-# BUILTIN SIGMA Σ #-}
{-# INLINE pair #-}
infixr 3 _,_
pattern _,_ a b = pair a b

id : {l : Level} {A : Set l} → A → A
id a = a

_∘_ :
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : (a : A) → B a → Set l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)

_~_ : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (f g : (x : A) → B x) → Set (l1 ⊔ l2)
f ~ g = (x : _) → f x ＝ g x

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) where
  fiber : Set (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ b)

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3}
  (f : (x : A) → B x → C x)
  where

  tot : Σ A B → Σ A C
  tot (x , y) = (x , f x y)

  map-compute-fiber-tot :
    (t : Σ A C) → fiber tot t → fiber (f (pr1 t)) (pr2 t)
  map-compute-fiber-tot .(tot (x , y)) ((x , y) , refl) = (y , refl)

  map-inv-compute-fiber-tot :
    (t : Σ A C) → fiber (f (pr1 t)) (pr2 t) → fiber tot t
  map-inv-compute-fiber-tot (a , .(f a y)) (y , refl) = ((a , y) , refl)

  is-section-map-inv-compute-fiber-tot :
    (t : Σ A C) → (map-compute-fiber-tot t ∘ map-inv-compute-fiber-tot t) ~ id
  is-section-map-inv-compute-fiber-tot (x , .(f x y)) (y , refl) = refl

  is-retraction-map-inv-compute-fiber-tot :
    (t : Σ A C) → (map-inv-compute-fiber-tot t ∘ map-compute-fiber-tot t) ~ id
  is-retraction-map-inv-compute-fiber-tot ._ ((x , y) , refl) = refl

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} (f : A → B) (C : B → Set l3)
  where

  map-Σ-map-base : Σ A (λ x → C (f x)) → Σ B C
  map-Σ-map-base (x , y) = (f x , y)

  fiber-map-Σ-map-base-fiber :
    (t : Σ B C) → fiber f (pr1 t) → fiber map-Σ-map-base t
  fiber-map-Σ-map-base-fiber (.(f x) , z) (x , refl) = ((x , z) , refl)

  fiber-fiber-map-Σ-map-base :
    (t : Σ B C) → fiber map-Σ-map-base t → fiber f (pr1 t)
  fiber-fiber-map-Σ-map-base ._ ((x , z) , refl) = (x , refl)

  is-section-fiber-fiber-map-Σ-map-base :
    (t : Σ B C) →
    (fiber-map-Σ-map-base-fiber t ∘ fiber-fiber-map-Σ-map-base t) ~ id
  is-section-fiber-fiber-map-Σ-map-base .(f x , z) ((x , z) , refl) = refl

  is-retraction-fiber-fiber-map-Σ-map-base :
    (t : Σ B C) →
    (fiber-fiber-map-Σ-map-base t ∘ fiber-map-Σ-map-base-fiber t) ~ id
  is-retraction-fiber-fiber-map-Σ-map-base (.(f x) , z) (x , refl) = refl
