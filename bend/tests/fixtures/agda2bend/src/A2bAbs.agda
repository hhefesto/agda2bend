{-# OPTIONS --without-K --safe #-}
-- agda2bend's fixture for constructors applied to fewer than their fields
-- and absurd patterns on constructors of types other than Bool and Nat
-- (bend/tests/agda2bend.bend); export it with agda-export into the parent
-- directory, which holds Agda.Primitive's and Agda.Builtin.Equality's.
module A2bAbs where

open import Agda.Builtin.Equality

data Void : Set where

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- a constructor as a function: eta-expanded over its fields
justs : {A : Set} → List A → List (Maybe A)
justs = map just

cons : {A : Set} → A → List A → List A
cons = _∷_

-- the stdlib's _IsRelatedTo_ and IsStrict (Relation.Binary.Reasoning.Base.Triple)
data Rel (A : Set) : Set where
  strict : A → Rel A
  nonstrict : A → Rel A
  equals : A → Rel A

data IsStrict {A : Set} : Rel A → Set where
  isStrict : ∀ x → IsStrict (strict x)

-- absurd: the family's index (nonstrict x) clashes with isStrict's (strict _)
notStrict : {A : Set} (x : A) → IsStrict (nonstrict x) → Void
notStrict x ()

data NonEmpty {A : Set} : List A → Set where
  ne : ∀ {x xs} → NonEmpty (x ∷ xs)

emptyNot : {A : Set} → NonEmpty {A} [] → Void
emptyNot ()

-- absurd: an equation between two constructors
consNil : {A : Set} (x : A) (xs : List A) → x ∷ xs ≡ [] → Void
consNil x xs ()
