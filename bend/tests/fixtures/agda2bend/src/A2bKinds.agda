{-# OPTIONS --without-K #-}
module A2bKinds where

data Ty : Set where
  star : Ty

data Ctx : Set where
  nil : Ctx
  _,_ : Ctx → Ty → Ctx

data Even : Set
data Odd : Set

data Even where
  ez : Even
  es : Odd → Even

data Odd where
  os : Even → Odd

data Fn : Set where
  fn : (Ty → Ty) → Fn

data Holds : Set where
  holds : Fn → Holds

app : Ctx → Ctx → Ctx
app a nil = a
app a (b , t) = app a b , t

both : Ctx → Ctx
both c = app c c
