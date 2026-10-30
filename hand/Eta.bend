# Record eta, the Bend way (2026-10-30).  `bend Eta.bend --verdict`: ALL PROOFS CHECK.
#
# Agda gets record eta from its conversion check: a variable p of record type is equal to the
# record of its projections.  Bend's conversion has eta for functions (f == x => f(x) holds by
# {==}) but not for constructors, and a projection that matches its argument is stuck on a
# variable.  So a law about a variable record, like composition in a product category, is stuck.
# With Agda's encoding (a constructor record, the way agda2bend translates it):
#     type Two is Type:
#       Two{l: Nat -> Nat, r: Nat -> Nat}
#     def Two.l(p: Two) -> Nat -> Nat: (match p: case Two{a, b}: a)
#     def Two.comp(g: Two, f: Two) -> Two: (match g f: case Two{g1, g2} Two{f1, f2}: ...)
#     def Two.pi_l_hom(-f: Two, -g: Two) -> {Two.l(Two.comp(g, f)) == (x => Two.l(f)(Two.l(g)(x)))}: {==}
# Bend says "expected Two.l(Two.comp(g, f)), observed x => Two.l(f, Two.l(g, x))".
#
# The Bend way: a record with non-dependent fields is a function of its field names.
#   - a projection is an application, p(L{}), so it computes on a variable p;
#   - eta is function eta: p == (s => p(s)) holds by {==};
#   - a record built from p's projections is p, field by field (a match on the field name);
#   - fields may share a resource: the cases of a match count once, not added, so comp(g, f)
#     uses g and f in both fields (a constructor would use each twice, which Bend refuses).
# With every morphism erased, this file proves the laws that agda-categories' Category.Product
# needs eta for: the category laws, the projection functors pi_l and pi_r, Swap, and the
# uniqueness of pairing.  Morphisms are equal when they agree on every side and every point,
# as in agda-categories (a setoid of functions, pointwise).
import Base

type Side is Data:
  L{}
  R{}

# A pair of endofunctions on Nat, as a function of the side.
def Hom2F(s: Side) -> Type:
  match s:
    case L{}:
      Nat -> Nat
    case R{}:
      Nat -> Nat

def Hom2() -> Type:
  @s:Side -> Hom2F(s)

def Hom2.pick(s: Side, a: Nat -> Nat, b: Nat -> Nat) -> Hom2F(s):
  match s:
    case L{}:
      a
    case R{}:
      b

def Hom2.mk(a: Nat -> Nat, b: Nat -> Nat) -> Hom2():
  s => Hom2.pick(s, a, b)

# Composition in diagram order (g, then f), field by field: g and f appear in both cases.
def Hom2.cside(s: Side, g: Hom2(), f: Hom2()) -> Hom2F(s):
  match s:
    case L{}:
      x => f(L{})(g(L{})(x))
    case R{}:
      x => f(R{})(g(R{})(x))

def Hom2.comp(g: Hom2(), f: Hom2()) -> Hom2():
  s => Hom2.cside(s, g, f)

def Hom2.id() -> Hom2():
  s => Hom2.pick(s, x => x, x => x)

# Two sides equal through a common normal form.  (BendTT's kernel, which --verdict runs, compares
# two calls of the same def by their arguments only, so a law whose sides share a head goes
# through the term both compute to.)
def via(-T: Type, -a: T, -n: T, -b: T, an: {a == n : T}, bn: {b == n : T}) -> {a == b : T}:
  Equal.trans(T, a, n, b, an, Equal.sym(T, b, n, bn))

# Morphisms agree on side s at every point (agda-categories' Product category: componentwise).
def Hom2.At(s: Side, u: Hom2F(s), v: Hom2F(s)) -> Type:
  match s:
    case L{}:
      @-x:Nat -> {u(x) == v(x) : Nat}
    case R{}:
      @-x:Nat -> {u(x) == v(x) : Nat}

# Eta: a variable morphism is the record of its projections.
def Hom2.eta(-p: Hom2()) -> {p == (s => p(s)) : Hom2()}:
  {==}

def Hom2.eta_mk(-p: Hom2(), s: Side) -> Hom2.At(s, Hom2.mk(p(L{}), p(R{}))(s), p(s)):
  match s:
    case L{}:
      x => {==}
    case R{}:
      x => {==}

# The category laws, over erased morphisms.

def Hom2.assoc(-f: Hom2(), -g: Hom2(), -h: Hom2(), s: Side) -> Hom2.At(s, Hom2.comp(Hom2.comp(h, g), f)(s), Hom2.comp(h, Hom2.comp(g, f))(s)):
  match s:
    case L{}:
      x => via(Nat, Hom2.comp(Hom2.comp(h, g), f)(L{})(x), f(L{})(g(L{})(h(L{})(x))), Hom2.comp(h, Hom2.comp(g, f))(L{})(x), {==}, {==})
    case R{}:
      x => via(Nat, Hom2.comp(Hom2.comp(h, g), f)(R{})(x), f(R{})(g(R{})(h(R{})(x))), Hom2.comp(h, Hom2.comp(g, f))(R{})(x), {==}, {==})


def Hom2.idl(-f: Hom2(), s: Side) -> Hom2.At(s, Hom2.comp(f, Hom2.id())(s), f(s)):
  match s:
    case L{}:
      x => {==}
    case R{}:
      x => {==}


def Hom2.idr(-f: Hom2(), s: Side) -> Hom2.At(s, Hom2.comp(Hom2.id(), f)(s), f(s)):
  match s:
    case L{}:
      x => {==}
    case R{}:
      x => {==}

# The projection functor pi_l: its laws hold by computation, with no case at all.

def Hom2.pi_l(f: Hom2()) -> Nat -> Nat:
  f(L{})

def Hom2.pi_l_hom(-f: Hom2(), -g: Hom2(), -x: Nat) -> {Hom2.pi_l(Hom2.comp(g, f))(x) == Hom2.pi_l(f)(Hom2.pi_l(g)(x)) : Nat}:
  via(Nat, Hom2.pi_l(Hom2.comp(g, f))(x), f(L{})(g(L{})(x)), Hom2.pi_l(f)(Hom2.pi_l(g)(x)), {==}, {==})

def Hom2.pi_l_id(-x: Nat) -> {Hom2.pi_l(Hom2.id())(x) == x : Nat}:
  {==}

def Hom2.pi_r_hom(-f: Hom2(), -g: Hom2(), -x: Nat) -> {Hom2.comp(g, f)(R{})(x) == f(R{})(g(R{})(x)) : Nat}:
  {==}

# Swap, and its laws: an involution and a functor.
def Hom2.sw(s: Side, p: Hom2()) -> Hom2F(s):
  match s:
    case L{}:
      p(R{})
    case R{}:
      p(L{})

def Hom2.swap(p: Hom2()) -> Hom2():
  s => Hom2.sw(s, p)

def Hom2.swap_swap(-p: Hom2(), s: Side) -> Hom2.At(s, Hom2.swap(Hom2.swap(p))(s), p(s)):
  match s:
    case L{}:
      x => {==}
    case R{}:
      x => {==}


def Hom2.swap_hom(-f: Hom2(), -g: Hom2(), s: Side) -> Hom2.At(s, Hom2.swap(Hom2.comp(g, f))(s), Hom2.comp(Hom2.swap(g), Hom2.swap(f))(s)):
  match s:
    case L{}:
      x => via(Nat, Hom2.swap(Hom2.comp(g, f))(L{})(x), f(R{})(g(R{})(x)), Hom2.comp(Hom2.swap(g), Hom2.swap(f))(L{})(x), {==}, {==})
    case R{}:
      x => via(Nat, Hom2.swap(Hom2.comp(g, f))(R{})(x), f(L{})(g(L{})(x)), Hom2.comp(Hom2.swap(g), Hom2.swap(f))(R{})(x), {==}, {==})

# Pairing is unique (the universal property): if pi_l(h) = a and pi_r(h) = b, then h = <a, b>.

def Hom2.unique(-h: Hom2(), -a: Nat -> Nat, -b: Nat -> Nat, el: @-y:Nat -> {h(L{})(y) == a(y) : Nat}, er: @-y:Nat -> {h(R{})(y) == b(y) : Nat}, s: Side) -> Hom2.At(s, h(s), Hom2.mk(a, b)(s)):
  match s:
    case L{}:
      x => Equal.trans(Nat, h(L{})(x), a(x), Hom2.mk(a, b)(L{})(x), el(x), {==})
    case R{}:
      x => Equal.trans(Nat, h(R{})(x), b(x), Hom2.mk(a, b)(R{})(x), er(x), {==})


def main() -> Nat:
  Hom2.comp(Hom2.mk(x => 1n+x, x => x), Hom2.swap(Hom2.mk(x => 1n+1n+x, x => 1n+1n+1n+x)))(L{})(0n)
