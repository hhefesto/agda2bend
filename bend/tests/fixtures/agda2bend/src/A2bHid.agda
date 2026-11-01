{-# OPTIONS --without-K --safe #-}
module A2bHid where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

_∙_ : {l : Level} {A : Set l} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
refl ∙ q = q

ap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
ap f refl = refl

right-unit : {l : Level} {A : Set l} {x y : A} {p : x ＝ y} → (p ∙ refl) ＝ p
right-unit {p = refl} = refl

_~_ : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (f g : (x : A) → B x) → Set (l1 ⊔ l2)
f ~ g = (x : _) → f x ＝ g x

nat-htpy :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) → (H x ∙ ap g p) ＝ (ap f p ∙ H y)
nat-htpy H refl = right-unit

module _ {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : (x : A) → B x → Set l3} where

  right-whisker-comp :
    {g h : {x : A} (y : B x) → C x y} (H : {x : A} → g {x} ~ h {x})
    (f : (x : A) → B x) → (λ x → g (f x)) ~ (λ x → h (f x))
  right-whisker-comp H f x = H (f x)

  _·r_ = right-whisker-comp

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3}
  {f f' : (x : A) → B x} {g g' : {x : A} → B x → C x}
  (G : {x : A} → g {x} ~ g' {x}) (F : f ~ f')
  where

  coh-hid : (λ x → G (f x) ∙ ap g' (F x)) ~ (λ x → ap g (F x) ∙ G (f' x))
  coh-hid = nat-htpy G ·r F

  coh-hid-explicit : (λ x → G (f x) ∙ ap g' (F x)) ~ (λ x → ap g (F x) ∙ G (f' x))
  coh-hid-explicit x = nat-htpy G (F x)
