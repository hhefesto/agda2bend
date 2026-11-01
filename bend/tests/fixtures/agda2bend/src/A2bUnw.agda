{-# OPTIONS --without-K --safe #-}
module A2bUnw where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

_∙_ : {l : Level} {A : Set l} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
refl ∙ q = q

id : {l : Level} {A : Set l} → A → A
id a = a

module _ {l : Level} {A : Set l} {x y z w : A} where

  coh : (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) → Set l
  coh top left right bottom = left ∙ bottom ＝ top ∙ right

module _ {l : Level} {A : Set l} {x y z w u : A} where

  whisk :
    (p : u ＝ x) (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coh top left right bottom → coh (p ∙ top) (p ∙ left) right bottom
  whisk refl top left right bottom = id

  whisk2 :
    (p : u ＝ x) (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coh top left right bottom → coh (p ∙ top) (p ∙ left) right bottom
  whisk2 refl top left right bottom H = H

  unwhisk :
    (p : u ＝ x) (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coh (p ∙ top) (p ∙ left) right bottom → coh top left right bottom
  unwhisk refl top left right bottom = id
