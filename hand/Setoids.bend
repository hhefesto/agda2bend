# Setoids and the category of setoids, written by hand in Bend (2026-10-30).
#
# The user (10-29/30): "there should be a sane way to implement Setoid in bend (even if we have
# to hand build it)"; "do a handwritten bend version that proofs Setoid in a more natural way for
# bend".
#
# Why Agda's encoding does not fit Bend, and what this one does instead:
# 1. A law's points are erased.  Agda's `trans : ∀ {i j k} → i ≈ j → j ≈ k → i ≈ k` takes its
#    elements as hidden arguments; translated, they are run-time arguments, and a point like
#    `h (i x)` uses the morphisms h and i at run time.  A morphism is a record of functions (Type),
#    which Bend never copies, so the category of setoids' `∘-resp-≈` (h and i in three points)
#    cannot check.  Here every point is erased (`@-x`): a proof never computes with the elements it
#    talks about, so they live in types only.
# 2. A proof matches the morphisms it composes.  Bend has no record eta: `comp(g, f)` matches its
#    arguments, so it only computes once they are constructors.  Agda's proofs never match (eta
#    does it for them); here `assoc`, the identities and `comp_resp_eq` take their morphisms live
#    and match them, after which both sides of each law compute to the same term.
import Base

# A setoid: a carrier, an equivalence on it, and the three laws, each over erased points.
type Setoid<-c: Quant, -l: Quant> is Type:
  Setoid{Carrier: Kind(c), eq: Carrier -> Carrier -> Kind(l), refl: @-x:Carrier -> eq(x, x), sym: @-x:Carrier -> @-y:Carrier -> eq(x, y) -> eq(y, x), trans: @-x:Carrier -> @-y:Carrier -> @-z:Carrier -> eq(x, y) -> eq(y, z) -> eq(x, z)}

def Setoid.Carrier(-c: Quant, -l: Quant, s: Setoid<c, l>) -> Kind(c):
  match s:
    case Setoid{C, e, r, sy, t}:
      C

def Setoid.eq(-c: Quant, -l: Quant, s: Setoid<c, l>) -> Setoid.Carrier(c, l, s) -> Setoid.Carrier(c, l, s) -> Kind(l):
  match s:
    case Setoid{C, e, r, sy, t}:
      e

def Setoid.refl(-c: Quant, -l: Quant, s: Setoid<c, l>) -> @-x:Setoid.Carrier(c, l, s) -> Setoid.eq(c, l, s)(x, x):
  match s:
    case Setoid{C, e, r, sy, t}:
      r

def Setoid.sym(-c: Quant, -l: Quant, s: Setoid<c, l>) -> @-x:Setoid.Carrier(c, l, s) -> @-y:Setoid.Carrier(c, l, s) -> Setoid.eq(c, l, s)(x, y) -> Setoid.eq(c, l, s)(y, x):
  match s:
    case Setoid{C, e, r, sy, t}:
      sy

def Setoid.trans(-c: Quant, -l: Quant, s: Setoid<c, l>) -> @-x:Setoid.Carrier(c, l, s) -> @-y:Setoid.Carrier(c, l, s) -> @-z:Setoid.Carrier(c, l, s) -> Setoid.eq(c, l, s)(x, y) -> Setoid.eq(c, l, s)(y, z) -> Setoid.eq(c, l, s)(x, z):
  match s:
    case Setoid{C, e, r, sy, t}:
      t

# A setoid morphism: a function that respects the equivalences (over erased points).
type Func<-a: Quant, -l1: Quant, -b: Quant, -l2: Quant, -A: Setoid<a, l1>, -B: Setoid<b, l2>> is Type:
  Func{to: Setoid.Carrier(a, l1, A) -> Setoid.Carrier(b, l2, B), cong: @-x:Setoid.Carrier(a, l1, A) -> @-y:Setoid.Carrier(a, l1, A) -> Setoid.eq(a, l1, A)(x, y) -> Setoid.eq(b, l2, B)(to(x), to(y))}

def Func.to(-a: Quant, -l1: Quant, -b: Quant, -l2: Quant, -A: Setoid<a, l1>, -B: Setoid<b, l2>, f: Func<a, l1, b, l2, A, B>) -> Setoid.Carrier(a, l1, A) -> Setoid.Carrier(b, l2, B):
  match f:
    case Func{t, cg}:
      t

def Func.cong(-a: Quant, -l1: Quant, -b: Quant, -l2: Quant, -A: Setoid<a, l1>, -B: Setoid<b, l2>, f: Func<a, l1, b, l2, A, B>) -> @-x:Setoid.Carrier(a, l1, A) -> @-y:Setoid.Carrier(a, l1, A) -> Setoid.eq(a, l1, A)(x, y) -> Setoid.eq(b, l2, B)(Func.to(a, l1, b, l2, A, B, f)(x), Func.to(a, l1, b, l2, A, B, f)(y)):
  match f:
    case Func{t, cg}:
      cg

# A category whose laws quantify their morphisms the Bend way: erased where a proof only
# mentions them (the hom equivalence), live where a proof may match them (composition's laws).
type Category<-o: Quant, -l: Quant, -e: Quant> is Type:
  Category{Obj: Kind(o), Arr: Obj -> Obj -> Kind(l), eq: @-A:Obj -> @-B:Obj -> Arr(A, B) -> Arr(A, B) -> Kind(e), id: @-A:Obj -> Arr(A, A), comp: @-A:Obj -> @-B:Obj -> @-C:Obj -> Arr(B, C) -> Arr(A, B) -> Arr(A, C), assoc: @-A:Obj -> @-B:Obj -> @-C:Obj -> @D:Obj -> @f:Arr(A, B) -> @g:Arr(B, C) -> @h:Arr(C, D) -> eq(A, D, comp(A, B, D, comp(B, C, D, h, g), f), comp(A, C, D, h, comp(A, B, C, g, f))), identity_l: @-A:Obj -> @B:Obj -> @f:Arr(A, B) -> eq(A, B, comp(A, B, B, id(B), f), f), identity_r: @-A:Obj -> @B:Obj -> @f:Arr(A, B) -> eq(A, B, comp(A, A, B, f, id(A)), f), refl: @-A:Obj -> @B:Obj -> @-f:Arr(A, B) -> eq(A, B, f, f), sym: @-A:Obj -> @B:Obj -> @-f:Arr(A, B) -> @-g:Arr(A, B) -> eq(A, B, f, g) -> eq(A, B, g, f), trans: @-A:Obj -> @B:Obj -> @-f:Arr(A, B) -> @-g:Arr(A, B) -> @-h:Arr(A, B) -> eq(A, B, f, g) -> eq(A, B, g, h) -> eq(A, B, f, h), comp_resp_eq: @-A:Obj -> @-B:Obj -> @C:Obj -> @f:Arr(B, C) -> @h:Arr(B, C) -> @g:Arr(A, B) -> @i:Arr(A, B) -> eq(B, C, f, h) -> eq(A, B, g, i) -> eq(A, C, comp(A, B, C, f, g), comp(A, B, C, h, i))}

# The category of setoids: objects setoids, arrows setoid morphisms, equal when pointwise equal.
def Setoids.eq(-c: Quant, -l: Quant, -A: Setoid<c, l>, -B: Setoid<c, l>, -f: Func<c, l, c, l, A, B>, -g: Func<c, l, c, l, A, B>) -> Type:
  @-x:Setoid.Carrier(c, l, A) -> Setoid.eq(c, l, B)(Func.to(c, l, c, l, A, B, f)(x), Func.to(c, l, c, l, A, B, g)(x))

def Setoids.id(-c: Quant, -l: Quant, -A: Setoid<c, l>) -> Func<c, l, c, l, A, A>:
  Func{x => x, x => y => p => p}

def Setoids.comp(-c: Quant, -l: Quant, -A: Setoid<c, l>, -B: Setoid<c, l>, -C: Setoid<c, l>, g: Func<c, l, c, l, B, C>, f: Func<c, l, c, l, A, B>) -> Func<c, l, c, l, A, C>:
  match g f:
    case Func{gt, gc} Func{ft, fc}:
      Func{x => gt(ft(x)), x => y => p => gc(ft(x), ft(y), fc(x, y, p))}

def Setoids.assoc(-c: Quant, -l: Quant, -A: Setoid<c, l>, -B: Setoid<c, l>, -C: Setoid<c, l>, D: Setoid<c, l>, f: Func<c, l, c, l, A, B>, g: Func<c, l, c, l, B, C>, h: Func<c, l, c, l, C, D>) -> Setoids.eq(c, l, A, D, Setoids.comp(c, l, A, B, D, Setoids.comp(c, l, B, C, D, h, g), f), Setoids.comp(c, l, A, C, D, h, Setoids.comp(c, l, A, B, C, g, f))):
  match f g h:
    case Func{ft, fc} Func{gt, gc} Func{ht, hc}:
      x => Setoid.refl(c, l, D)(ht(gt(ft(x))))

def Setoids.identity_l(-c: Quant, -l: Quant, -A: Setoid<c, l>, B: Setoid<c, l>, f: Func<c, l, c, l, A, B>) -> Setoids.eq(c, l, A, B, Setoids.comp(c, l, A, B, B, Setoids.id(c, l, B), f), f):
  match f:
    case Func{ft, fc}:
      x => Setoid.refl(c, l, B)(ft(x))

def Setoids.identity_r(-c: Quant, -l: Quant, -A: Setoid<c, l>, B: Setoid<c, l>, f: Func<c, l, c, l, A, B>) -> Setoids.eq(c, l, A, B, Setoids.comp(c, l, A, A, B, f, Setoids.id(c, l, A)), f):
  match f:
    case Func{ft, fc}:
      x => Setoid.refl(c, l, B)(ft(x))

def Setoids.refl(-c: Quant, -l: Quant, -A: Setoid<c, l>, B: Setoid<c, l>, -f: Func<c, l, c, l, A, B>) -> Setoids.eq(c, l, A, B, f, f):
  x => Setoid.refl(c, l, B)(Func.to(c, l, c, l, A, B, f)(x))

def Setoids.sym(-c: Quant, -l: Quant, -A: Setoid<c, l>, B: Setoid<c, l>, -f: Func<c, l, c, l, A, B>, -g: Func<c, l, c, l, A, B>) -> Setoids.eq(c, l, A, B, f, g) -> Setoids.eq(c, l, A, B, g, f):
  p => x => Setoid.sym(c, l, B)(Func.to(c, l, c, l, A, B, f)(x), Func.to(c, l, c, l, A, B, g)(x), p(x))

def Setoids.trans(-c: Quant, -l: Quant, -A: Setoid<c, l>, B: Setoid<c, l>, -f: Func<c, l, c, l, A, B>, -g: Func<c, l, c, l, A, B>, -h: Func<c, l, c, l, A, B>) -> Setoids.eq(c, l, A, B, f, g) -> Setoids.eq(c, l, A, B, g, h) -> Setoids.eq(c, l, A, B, f, h):
  p => q => x => Setoid.trans(c, l, B)(Func.to(c, l, c, l, A, B, f)(x), Func.to(c, l, c, l, A, B, g)(x), Func.to(c, l, c, l, A, B, h)(x), p(x), q(x))

# Agda's ∘-resp-≈: f ≈ h and g ≈ i give f ∘ g ≈ h ∘ i.  The points f(g x), f(i x), h(i x) are
# erased, so f, g, h and i are each matched once and used nowhere else at run time.
def Setoids.comp_resp_eq(-c: Quant, -l: Quant, -A: Setoid<c, l>, -B: Setoid<c, l>, C: Setoid<c, l>, f: Func<c, l, c, l, B, C>, h: Func<c, l, c, l, B, C>, g: Func<c, l, c, l, A, B>, i: Func<c, l, c, l, A, B>) -> Setoids.eq(c, l, B, C, f, h) -> Setoids.eq(c, l, A, B, g, i) -> Setoids.eq(c, l, A, C, Setoids.comp(c, l, A, B, C, f, g), Setoids.comp(c, l, A, B, C, h, i)):
  match f h g i:
    case Func{ft, fc} Func{ht, hc} Func{gt, gc} Func{it, ic}:
      fh => gi => x => Setoid.trans(c, l, C)(ft(gt(x)), ft(it(x)), ht(it(x)), fc(gt(x), it(x), gi(x)), fh(it(x)))

def Setoids(-c: Quant, -l: Quant) -> Category<&1, &1, &1>:
  Category{Setoid<c, l>, A => B => Func<c, l, c, l, A, B>, A => B => f => g => Setoids.eq(c, l, A, B, f, g), A => Setoids.id(c, l, A), A => B => C => g => f => Setoids.comp(c, l, A, B, C, g, f), A => B => C => D => f => g => h => Setoids.assoc(c, l, A, B, C, D, f, g, h), A => B => f => Setoids.identity_l(c, l, A, B, f), A => B => f => Setoids.identity_r(c, l, A, B, f), A => B => f => Setoids.refl(c, l, A, B, f), A => B => f => g => Setoids.sym(c, l, A, B, f, g), A => B => f => g => h => Setoids.trans(c, l, A, B, f, g, h), A => B => C => f => h => g => i => Setoids.comp_resp_eq(c, l, A, B, C, f, h, g, i)}
