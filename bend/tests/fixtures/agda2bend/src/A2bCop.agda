{-# OPTIONS --without-K --safe #-}
-- agda2bend's fixture for agda-unimath's shapes (2026-10-31): Pis behind a
-- clause-defined family (is-trunc) and behind a copattern field (_⊆_);
-- is-contr, a record of a function family, whose value used twice is a
-- template; a copattern clause matching after its projection behind a
-- type-valued definition (is-prop-is-contr, is-prop-all-elements-equal);
-- copattern clauses in groups, and beside plain clauses.
module A2bCop where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public

data ⊥ : Set where

ex-falso : {l : Level} {A : Set l} → ⊥ → A
ex-falso ()

infixl 15 _∙_
_∙_ : {l : Level} {A : Set l} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
refl ∙ q = q

inv : {l : Level} {A : Set l} {x y : A} → x ＝ y → y ＝ x
inv refl = refl

left-inv : {l : Level} {A : Set l} {x y : A} (p : x ＝ y) → inv p ∙ p ＝ refl
left-inv refl = refl

is-contr : {l : Level} → Set l → Set l
is-contr A = Σ A (λ a → (x : A) → a ＝ x)

abstract
  center : {l : Level} {A : Set l} → is-contr A → A
  center (pair c C) = c

eq-is-contr' : {l : Level} {A : Set l} → is-contr A → (x y : A) → x ＝ y
eq-is-contr' (pair c C) x y = inv (C x) ∙ C y

eq-is-contr : {l : Level} {A : Set l} → is-contr A → {x y : A} → x ＝ y
eq-is-contr C {x} {y} = eq-is-contr' C x y

abstract
  contraction : {l : Level} {A : Set l} (C : is-contr A) (x : A) → center C ＝ x
  contraction C x = eq-is-contr C

is-prop-is-contr : {l : Level} {A : Set l} → is-contr A → (x y : A) → is-contr (x ＝ y)
pr1 (is-prop-is-contr H x y) = eq-is-contr H
pr2 (is-prop-is-contr H x .x) refl = left-inv (pr2 H x)

is-prop : {l : Level} → Set l → Set l
is-prop A = (x y : A) → is-contr (x ＝ y)

all-elements-equal : {l : Level} → Set l → Set l
all-elements-equal A = (x y : A) → x ＝ y

is-prop-all-elements-equal : {l : Level} {A : Set l} → all-elements-equal A → is-prop A
pr1 (is-prop-all-elements-equal H x y) = inv (H x x) ∙ H x y
pr2 (is-prop-all-elements-equal H x .x) refl = left-inv (H x x)

data 𝕋 : Set where
  neg-two : 𝕋
  succ : 𝕋 → 𝕋

is-trunc : {l : Level} (k : 𝕋) → Set l → Set l
is-trunc neg-two A = is-contr A
is-trunc (succ k) A = (x y : A) → is-trunc k (x ＝ y)

is-trunc-app : {l : Level} (k : 𝕋) (A : Set l) → is-trunc (succ k) A → is-trunc (succ k) A
is-trunc-app k A H x y = H x y

Prop : (l : Level) → Set (lsuc l)
Prop l = Σ (Set l) (λ A → A → A)

type-Prop : {l : Level} → Prop l → Set l
type-Prop P = pr1 P

Π-Prop : {l1 l2 : Level} (A : Set l1) → (A → Prop l2) → Prop (l1 ⊔ l2)
pr1 (Π-Prop A P) = (x : A) → type-Prop (P x)
pr2 (Π-Prop A P) = λ f → f

hom-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (hom-Prop P Q) = type-Prop P → type-Prop Q
pr2 (hom-Prop P Q) = λ f → f

leq-prop-subtype : {l1 l2 : Level} {A : Set l1} → (A → Prop l2) → (A → Prop l2) → Prop (l1 ⊔ l2)
leq-prop-subtype {A = A} P Q = Π-Prop A (λ x → hom-Prop (P x) (Q x))

_⊆_ : {l1 l2 : Level} {A : Set l1} → (A → Prop l2) → (A → Prop l2) → Set (l1 ⊔ l2)
P ⊆ Q = type-Prop (leq-prop-subtype P Q)

refl-leq-subtype : {l1 l2 : Level} {A : Set l1} (P : A → Prop l2) → P ⊆ P
refl-leq-subtype P x p = p

two : Nat → Σ Nat (λ _ → Nat)
pr1 (two zero) = zero
pr2 (two zero) = suc zero
pr1 (two (suc n)) = n
pr2 (two (suc n)) = suc (suc zero)

¬' : Set → Set
¬' A = A → ⊥

is-successor-is-nonzero : (x : Nat) → ¬' (x ＝ zero) → Σ Nat (λ y → x ＝ suc y)
is-successor-is-nonzero zero H = ex-falso (H refl)
pr1 (is-successor-is-nonzero (suc x) H) = x
pr2 (is-successor-is-nonzero (suc x) H) = refl

least : Σ Nat (λ _ → Nat) → Σ Nat (λ _ → Nat)
pr1 (least (pair zero p)) = p
pr2 (least (pair zero p)) = zero
least (pair (suc n) p) = least (pair n p)

-- is-equiv-comp: record patterns whose fields go to templates (section-comp's)
infixr 16 _∘_
_∘_ : {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

id : {l : Level} {A : Set l} → A → A
id x = x

_~_ : {l1 l2 : Level} {A : Set l1} {B : Set l2} → (A → B) → (A → B) → Set (l1 ⊔ l2)
f ~ g = (x : _) → f x ＝ g x

ap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
ap f refl = refl

is-section : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → (B → A) → Set l2
is-section f g = (f ∘ g) ~ id

section : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → Set (l1 ⊔ l2)
section f = Σ _ (is-section f)

is-retraction : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → (B → A) → Set l1
is-retraction f g = (g ∘ f) ~ id

retraction : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → Set (l1 ⊔ l2)
retraction f = Σ _ (is-retraction f)

is-equiv : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → Set (l1 ⊔ l2)
is-equiv f = Σ (section f) (λ _ → retraction f)

module _ {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {X : Set l3} (g : B → X) (h : A → B) where

  section-comp : section h → section g → section (g ∘ h)
  pr1 (section-comp t s) = pr1 t ∘ pr1 s
  pr2 (section-comp t s) x = ap g (pr2 t (pr1 s x)) ∙ pr2 s x

  retraction-comp : retraction g → retraction h → retraction (g ∘ h)
  pr1 (retraction-comp r q) = pr1 q ∘ pr1 r
  pr2 (retraction-comp r q) x = ap (pr1 q) (pr2 r (h x)) ∙ pr2 q x

  is-equiv-comp : is-equiv h → is-equiv g → is-equiv (g ∘ h)
  pr1 (is-equiv-comp (pair sh rh) (pair sg rg)) = section-comp sh sg
  pr2 (is-equiv-comp (pair sh rh) (pair sg rg)) = retraction-comp rg rh
