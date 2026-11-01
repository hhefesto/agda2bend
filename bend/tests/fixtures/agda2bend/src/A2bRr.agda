-- agda2bend fixture (2026-11-01): a refl whose equation's side is a call that
-- reduces to a dotted variable only once an earlier refl is in (inv-tr D refl v
-- is v; refl ∙ q is q): map-inv-fiber-map-Σ's and is-section-map-inv-fiber-map-Σ's
-- second refl, is-section-is-injective-concat's second.
{-# OPTIONS --without-K --exact-split --no-postfix-projections --safe #-}
module A2bRr where

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

inv' : {l : Level} {A : Set l} {x y : A} → x ＝ y → y ＝ x
inv' refl = refl

inv-tr : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x y : A} → x ＝ y → B y → B x
inv-tr B p = tr B (inv' p)

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) where
  fiber' : Set (l1 ⊔ l2)
  fiber' = Σ A (λ x → b ＝ f x)

module _
  {l1 l2 l3 l4 : Level} {A : Set l1} {B : Set l2} {C : A → Set l3}
  (D : B → Set l4)
  where

  map-Σ : (f : A → B) (g : (x : A) → C x → D (f x)) → Σ A C → Σ B D
  map-Σ f g (x , y) = (f x , g x y)

module _
  {l1 l2 l3 l4 : Level} {A : Set l1} {B : Set l2} {C : A → Set l3} (D : B → Set l4)
  (f : A → B) (g : (x : A) → C x → D (f x)) (t : Σ B D)
  where

  fiber-map-Σ : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiber-map-Σ =
    Σ (fiber f (pr1 t)) (λ s → fiber (g (pr1 s)) (inv-tr D (pr2 s) (pr2 t)))

  map-fiber-map-Σ : fiber (map-Σ D f g) t → fiber-map-Σ
  map-fiber-map-Σ ((a , c) , refl) = (a , refl) , (c , refl)

  map-inv-fiber-map-Σ : fiber-map-Σ → fiber (map-Σ D f g) t
  map-inv-fiber-map-Σ ((a , refl) , c , refl) = ((a , c) , refl)

  is-section-map-inv-fiber-map-Σ :
    is-section map-fiber-map-Σ map-inv-fiber-map-Σ
  is-section-map-inv-fiber-map-Σ ((a , refl) , (c , refl)) = refl

  is-retraction-map-inv-fiber-map-Σ :
    is-retraction map-fiber-map-Σ map-inv-fiber-map-Σ
  is-retraction-map-inv-fiber-map-Σ ((a , c) , refl) = refl

module _
  {l : Level} {A : Set l}
  where

  is-injective-concat : {x y z : A} (p : x ＝ y) {q r : y ＝ z} → p ∙ q ＝ p ∙ r → q ＝ r
  is-injective-concat refl s = s

  is-section-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} (s : (p ∙ q) ＝ (p ∙ r)) →
    ap (p ∙_) (is-injective-concat p s) ＝ s
  is-section-is-injective-concat refl refl = refl

module _
  {l : Level} {A : Set l}
  where

  right-unit : {x y : A} {p : x ＝ y} → p ∙ refl ＝ p
  right-unit {p = refl} = refl

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} {b : B}
  where

  Eq-fiber' : fiber' f b → fiber' f b → Set (l1 ⊔ l2)
  Eq-fiber' s t = Σ (pr1 s ＝ pr1 t) (λ α → pr2 t ＝ pr2 s ∙ ap f α)

  eq-Eq-fiber-uncurry' : {s t : fiber' f b} → Eq-fiber' s t → s ＝ t
  eq-Eq-fiber-uncurry' {x , p} (refl , refl) = ap (pair _) (inv' right-unit)
