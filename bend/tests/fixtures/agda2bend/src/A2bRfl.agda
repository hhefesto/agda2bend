{-# OPTIONS --without-K --exact-split --no-postfix-projections --safe #-}
module A2bRfl where

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

infixr 15 _∘_
_∘_ :
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : (a : A) → B a → Set l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)

infix 6 _~_
_~_ : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (f g : (x : A) → B x) → Set (l1 ⊔ l2)
f ~ g = (x : _) → f x ＝ g x

ap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
ap f refl = refl

tr : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x y : A} (p : x ＝ y) → B x → B y
tr B refl b = b

tr-ap :
  {l1 l2 l3 l4 : Level} {A : Set l1} {B : A → Set l2} {C : Set l3} {D : C → Set l4}
  (f : A → C) (g : (x : A) → B x → D (f x))
  {x y : A} (p : x ＝ y) (z : B x) →
  tr D (ap f p) (g x z) ＝ g y (tr B p z)
tr-ap f g refl z = refl

dependent-identification :
  {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → Set l2
dependent-identification B p u v = (tr B p u ＝ v)

_∙_ : {l : Level} {A : Set l} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
refl ∙ q = q
infixl 15 _∙_

ap-binary :
  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} (f : A → B → C)
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') → f x y ＝ f x' y'
ap-binary f refl refl = refl

_×_ : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
A × B = Σ A (λ _ → B)
infixr 15 _×_

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} where

  Eq-product : (s t : A × B) → Set (l1 ⊔ l2)
  Eq-product s t = ((pr1 s) ＝ (pr1 t)) × ((pr2 s) ＝ (pr2 t))

  eq-pair' : {s t : A × B} → Eq-product s t → s ＝ t
  eq-pair' (p , q) = ap-binary pair p q

  pair-eq : {s t : A × B} → s ＝ t → Eq-product s t
  pr1 (pair-eq α) = ap pr1 α
  pr2 (pair-eq α) = ap pr2 α

  is-retraction-pair-eq :
    {s t : A × B} → pair-eq {s} {t} ∘ eq-pair' {s} {t} ~ id
  is-retraction-pair-eq (refl , refl) = refl

  is-section-pair-eq :
    {s t : A × B} → eq-pair' {s} {t} ∘ pair-eq {s} {t} ~ id
  is-section-pair-eq refl = refl

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) where
  fiber : Set (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ b)

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} {b : B} where

  Eq-fiber : fiber f b → fiber f b → Set (l1 ⊔ l2)
  Eq-fiber s t = Σ (pr1 s ＝ pr1 t) (λ α → ap f α ∙ pr2 t ＝ pr2 s)

  refl-Eq-fiber : (s : fiber f b) → Eq-fiber s s
  pr1 (refl-Eq-fiber s) = refl
  pr2 (refl-Eq-fiber s) = refl

  Eq-eq-fiber : {s t : fiber f b} → s ＝ t → Eq-fiber s t
  Eq-eq-fiber {s} refl = refl-Eq-fiber s

  eq-Eq-fiber-uncurry : {s t : fiber f b} → Eq-fiber s t → s ＝ t
  eq-Eq-fiber-uncurry (refl , refl) = refl

  is-section-eq-Eq-fiber :
    {s t : fiber f b} → (Eq-eq-fiber {s} {t} ∘ eq-Eq-fiber-uncurry {s} {t}) ~ id
  is-section-eq-Eq-fiber (refl , refl) = refl

  is-retraction-eq-Eq-fiber :
    {s t : fiber f b} → (eq-Eq-fiber-uncurry {s} {t} ∘ Eq-eq-fiber {s} {t}) ~ id
  is-retraction-eq-Eq-fiber refl = refl

  inv : {l : Level} {A : Set l} {x y : A} → x ＝ y → y ＝ x
  inv refl = refl

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) where

  is-section : (g : B → A) → Set l2
  is-section g = (f ∘ g) ~ id

  is-retraction : (g : B → A) → Set l1
  is-retraction g = (g ∘ f) ~ id

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) where

  map-equiv-total-fiber : Σ B (fiber f) → A
  map-equiv-total-fiber t = pr1 (pr2 t)

  map-inv-equiv-total-fiber : A → Σ B (fiber f)
  map-inv-equiv-total-fiber x = (f x , x , refl)

  is-retraction-map-inv-equiv-total-fiber :
    is-retraction map-equiv-total-fiber map-inv-equiv-total-fiber
  is-retraction-map-inv-equiv-total-fiber (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber :
    is-section map-equiv-total-fiber map-inv-equiv-total-fiber
  is-section-map-inv-equiv-total-fiber x = refl

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
  where

  Eq-Σ : (s t : Σ A B) → Set (l1 ⊔ l2)
  Eq-Σ s t =
    Σ (pr1 s ＝ pr1 t) (λ α → dependent-identification B α (pr2 s) (pr2 t))

  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  refl-Eq-Σ s = refl , refl

  eq-base-eq-pair : {s t : Σ A B} → s ＝ t → pr1 s ＝ pr1 t
  eq-base-eq-pair = ap pr1

  dependent-identification-eq-pair :
    {s t : Σ A B} (p : s ＝ t) →
    dependent-identification B (eq-base-eq-pair p) (pr2 s) (pr2 t)
  dependent-identification-eq-pair {s} p = tr-ap pr1 (λ x _ → pr2 x) p (pr1 s)

  pair-eq-Σ : {s t : Σ A B} → s ＝ t → Eq-Σ s t
  pair-eq-Σ p = eq-base-eq-pair p , dependent-identification-eq-pair p

  eq-pair-eq-fiber :
    {x : A} {s t : B x} → s ＝ t → (x , s) ＝ (x , t)
  eq-pair-eq-fiber {x} = ap {B = Σ A B} (pair x)

  eq-pair-Σ :
    {s t : Σ A B}
    (α : pr1 s ＝ pr1 t) →
    dependent-identification B α (pr2 s) (pr2 t) → s ＝ t
  eq-pair-Σ refl = eq-pair-eq-fiber

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → s ＝ t
  eq-pair-Σ' p = eq-pair-Σ (pr1 p) (pr2 p)

  is-retraction-pair-eq-Σ :
    (s t : Σ A B) → pair-eq-Σ {s} {t} ∘ eq-pair-Σ' {s} {t} ~ id {A = Eq-Σ s t}
  is-retraction-pair-eq-Σ (x , y) (.x , .y) (refl , refl) = refl

  is-section-pair-eq-Σ :
    (s t : Σ A B) → eq-pair-Σ' {s} {t} ∘ pair-eq-Σ {s} {t} ~ id
  is-section-pair-eq-Σ (x , y) .(x , y) refl = refl

  η-pair : (t : Σ A B) → (pr1 t , pr2 t) ＝ t
  η-pair t = refl
