# The Yoneda lemma for setoid-enriched categories, the Bend way (2026-10-30).
# `bend YonedaSetoid.bend --verdict`: ALL PROOFS CHECK (Bend's checker, then the BendTT kernel).
#
# This is the statement agda-categories proves (Categories.Yoneda, yoneda-inverse): for a
# category C whose hom-sets are setoids, an object A and a setoid-valued presheaf F, the
# natural transformations from Hom(-, A) to F and the setoid F(A) are inverse to each other:
# to(a) = a_A(id), from(x)_X(h) = F(h)(x), both respect equality, to . from = id and
# from . to = id.
#
# What is done the Bend way, and why:
# 1. No records of functions are built in a proof.  A closure is affine in Bend, so a natural
#    transformation is a raw family of functions, and being natural and respecting equality
#    are separate propositions about it (the PER / P-category style of Cubric, Dybjer and
#    Scott, who use it to do Yoneda constructively).  A structure (C, F, a setoid) is matched
#    once per proof, and each of its laws is used at most once.
# 2. No record eta.  Every equation is between elements (pointwise), so it holds by computation
#    or by one law; nothing compares functions.
# 3. A setoid-valued presheaf is flattened: carriers and equalities are families, and their
#    laws are uniform in the object, which stays erased.  They are used through one helper,
#    euclid (a ~ b, a ~ c give b ~ c), which matches F once and uses sym and trans once each.
# Every point a law talks about is erased: it lives in types, where Bend lets it appear any
# number of times.
import Base

# A category whose hom-sets are setoids.
type SCat is Type:
  SCat{Obj: Type, Arr: Obj -> Obj -> Type, eq: @-A:Obj -> @-B:Obj -> Arr(A, B) -> Arr(A, B) -> Type, id: @-A:Obj -> Arr(A, A), comp: @-A:Obj -> @-B:Obj -> @-X:Obj -> Arr(B, X) -> Arr(A, B) -> Arr(A, X), idl: @-A:Obj -> @-B:Obj -> @-f:Arr(A, B) -> eq(A, B, comp(A, B, B, id(B), f), f), idr: @-A:Obj -> @-B:Obj -> @-f:Arr(A, B) -> eq(A, B, comp(A, A, B, f, id(A)), f), assoc: @-A:Obj -> @-B:Obj -> @-X:Obj -> @-D:Obj -> @-f:Arr(A, B) -> @-g:Arr(B, X) -> @-h:Arr(X, D) -> eq(A, D, comp(A, B, D, comp(B, X, D, h, g), f), comp(A, X, D, h, comp(A, B, X, g, f))), hsym: @-A:Obj -> @-B:Obj -> @-f:Arr(A, B) -> @-g:Arr(A, B) -> eq(A, B, f, g) -> eq(A, B, g, f), htrans: @-A:Obj -> @-B:Obj -> @-f:Arr(A, B) -> @-g:Arr(A, B) -> @-h:Arr(A, B) -> eq(A, B, f, g) -> eq(A, B, g, h) -> eq(A, B, f, h)}

def SCat.Obj(C: SCat) -> Type:
  match C:
    case SCat{o, ar, e, i, c, l, r, s, hs, ht}:
      o

def SCat.Arr(C: SCat) -> SCat.Obj(C) -> SCat.Obj(C) -> Type:
  match C:
    case SCat{o, ar, e, i, c, l, r, s, hs, ht}:
      ar

def SCat.Eq(C: SCat) -> @-A:SCat.Obj(C) -> @-B:SCat.Obj(C) -> SCat.Arr(C)(A, B) -> SCat.Arr(C)(A, B) -> Type:
  match C:
    case SCat{o, ar, e, i, c, l, r, s, hs, ht}:
      e

def SCat.id(C: SCat) -> @-A:SCat.Obj(C) -> SCat.Arr(C)(A, A):
  match C:
    case SCat{o, ar, e, i, c, l, r, s, hs, ht}:
      i

def SCat.comp(C: SCat) -> @-A:SCat.Obj(C) -> @-B:SCat.Obj(C) -> @-X:SCat.Obj(C) -> SCat.Arr(C)(B, X) -> SCat.Arr(C)(A, B) -> SCat.Arr(C)(A, X):
  match C:
    case SCat{o, ar, e, i, c, l, r, s, hs, ht}:
      c

def SCat.idl(C: SCat) -> @-A:SCat.Obj(C) -> @-B:SCat.Obj(C) -> @-f:SCat.Arr(C)(A, B) -> SCat.Eq(C)(A, B, SCat.comp(C)(A, B, B, SCat.id(C)(B), f), f):
  match C:
    case SCat{o, ar, e, i, c, l, r, s, hs, ht}:
      l

# f . id ~ id . f, from one match of C: both identity laws, hom sym and trans, once each.
def SCat.idlr(C: SCat, -A: SCat.Obj(C), -B: SCat.Obj(C), -f: SCat.Arr(C)(A, B)) -> SCat.Eq(C)(A, B, SCat.comp(C)(A, A, B, f, SCat.id(C)(A)), SCat.comp(C)(A, B, B, SCat.id(C)(B), f)):
  match C:
    case SCat{o, ar, e, i, c, l, r, s, hs, ht}:
      ht(A, B, c(A, A, B, f, i(A)), f, c(A, B, B, i(B), f), r(A, B, f), hs(A, B, c(A, B, B, i(B), f), f, l(A, B, f)))

# A setoid-valued presheaf on C, flattened: a family of carriers and a family of equalities
# with their laws uniform in the object (erased), then the contravariant action, which respects
# both equalities and keeps identities and composites.  (A family of Setoid records would need
# the object at run time to reach a law; here every law takes it erased.)
type SPsh<-C: SCat> is Type:
  SPsh{Car: SCat.Obj(C) -> Type, eq: @-X:SCat.Obj(C) -> Car(X) -> Car(X) -> Type, refl: @-X:SCat.Obj(C) -> @-x:Car(X) -> eq(X, x, x), sym: @-X:SCat.Obj(C) -> @-x:Car(X) -> @-y:Car(X) -> eq(X, x, y) -> eq(X, y, x), trans: @-X:SCat.Obj(C) -> @-x:Car(X) -> @-y:Car(X) -> @-z:Car(X) -> eq(X, x, y) -> eq(X, y, z) -> eq(X, x, z), F1: @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> SCat.Arr(C)(X, Y) -> Car(Y) -> Car(X), cong: @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> @-f:SCat.Arr(C)(X, Y) -> @-x:Car(Y) -> @-y:Car(Y) -> eq(Y, x, y) -> eq(X, F1(X, Y, f, x), F1(X, Y, f, y)), resp: @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> @-f:SCat.Arr(C)(X, Y) -> @-g:SCat.Arr(C)(X, Y) -> SCat.Eq(C)(X, Y, f, g) -> @-x:Car(Y) -> eq(X, F1(X, Y, f, x), F1(X, Y, g, x)), fid: @-X:SCat.Obj(C) -> @-x:Car(X) -> eq(X, F1(X, X, SCat.id(C)(X), x), x), fcomp: @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> @-Z:SCat.Obj(C) -> @-f:SCat.Arr(C)(X, Y) -> @-g:SCat.Arr(C)(Y, Z) -> @-z:Car(Z) -> eq(X, F1(X, Z, SCat.comp(C)(X, Y, Z, g, f), z), F1(X, Y, f, F1(Y, Z, g, z)))}

def SPsh.Car(-C: SCat, F: SPsh<C>) -> SCat.Obj(C) -> Type:
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b0

def SPsh.Eq(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> SPsh.Car(C, F)(X) -> SPsh.Car(C, F)(X) -> Type:
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b1

def SPsh.refl(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-x:SPsh.Car(C, F)(X) -> SPsh.Eq(C, F)(X, x, x):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b2

def SPsh.sym(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-x:SPsh.Car(C, F)(X) -> @-y:SPsh.Car(C, F)(X) -> SPsh.Eq(C, F)(X, x, y) -> SPsh.Eq(C, F)(X, y, x):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b3

def SPsh.trans(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-x:SPsh.Car(C, F)(X) -> @-y:SPsh.Car(C, F)(X) -> @-z:SPsh.Car(C, F)(X) -> SPsh.Eq(C, F)(X, x, y) -> SPsh.Eq(C, F)(X, y, z) -> SPsh.Eq(C, F)(X, x, z):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b4

def SPsh.F1(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> SCat.Arr(C)(X, Y) -> SPsh.Car(C, F)(Y) -> SPsh.Car(C, F)(X):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b5

def SPsh.cong(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> @-f:SCat.Arr(C)(X, Y) -> @-x:SPsh.Car(C, F)(Y) -> @-y:SPsh.Car(C, F)(Y) -> SPsh.Eq(C, F)(Y, x, y) -> SPsh.Eq(C, F)(X, SPsh.F1(C, F)(X, Y, f, x), SPsh.F1(C, F)(X, Y, f, y)):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b6

def SPsh.resp(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> @-f:SCat.Arr(C)(X, Y) -> @-g:SCat.Arr(C)(X, Y) -> SCat.Eq(C)(X, Y, f, g) -> @-x:SPsh.Car(C, F)(Y) -> SPsh.Eq(C, F)(X, SPsh.F1(C, F)(X, Y, f, x), SPsh.F1(C, F)(X, Y, g, x)):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b7

def SPsh.fid(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-x:SPsh.Car(C, F)(X) -> SPsh.Eq(C, F)(X, SPsh.F1(C, F)(X, X, SCat.id(C)(X), x), x):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b8

def SPsh.fcomp(-C: SCat, F: SPsh<C>) -> @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> @-Z:SCat.Obj(C) -> @-f:SCat.Arr(C)(X, Y) -> @-g:SCat.Arr(C)(Y, Z) -> @-z:SPsh.Car(C, F)(Z) -> SPsh.Eq(C, F)(X, SPsh.F1(C, F)(X, Z, SCat.comp(C)(X, Y, Z, g, f), z), SPsh.F1(C, F)(X, Y, f, SPsh.F1(C, F)(Y, Z, g, z))):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b9

# a ~ b and a ~ c give b ~ c in F(X): sym and trans, each once, from one match of F.
def SPsh.euclid(-C: SCat, F: SPsh<C>, -X: SCat.Obj(C), -a: SPsh.Car(C, F)(X), -b: SPsh.Car(C, F)(X), -c: SPsh.Car(C, F)(X), p: SPsh.Eq(C, F)(X, a, b), q: SPsh.Eq(C, F)(X, a, c)) -> SPsh.Eq(C, F)(X, b, c):
  match F:
    case SPsh{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9}:
      b4(X, b, a, c, b3(X, a, b, p), q)

# Families from Hom(-, A) to F, and the three propositions about them.
def SFam(C: SCat, F: SPsh<C>, A: SCat.Obj(C)) -> Type:
  @-X:SCat.Obj(C) -> SCat.Arr(C)(X, A) -> SPsh.Car(C, F)(X)

def SNatural(C: SCat, F: SPsh<C>, A: SCat.Obj(C), a: SFam(C, F, A)) -> Type:
  @-X:SCat.Obj(C) -> @-Y:SCat.Obj(C) -> @-f:SCat.Arr(C)(X, Y) -> @-h:SCat.Arr(C)(Y, A) -> SPsh.Eq(C, F)(X, a(X, SCat.comp(C)(X, Y, A, h, f)), SPsh.F1(C, F)(X, Y, f, a(Y, h)))

def SResp(C: SCat, F: SPsh<C>, A: SCat.Obj(C), a: SFam(C, F, A)) -> Type:
  @-X:SCat.Obj(C) -> @-h:SCat.Arr(C)(X, A) -> @-k:SCat.Arr(C)(X, A) -> SCat.Eq(C)(X, A, h, k) -> SPsh.Eq(C, F)(X, a(X, h), a(X, k))

# Equality of natural transformations: componentwise (agda-categories' Presheaves hom-setoid).
def SNatEq(C: SCat, F: SPsh<C>, A: SCat.Obj(C), a: SFam(C, F, A), b: SFam(C, F, A)) -> Type:
  @-X:SCat.Obj(C) -> @-h:SCat.Arr(C)(X, A) -> SPsh.Eq(C, F)(X, a(X, h), b(X, h))

# The two directions.
def SYoneda.to(C: SCat, -F: SPsh<C>, -A: SCat.Obj(C), a: SFam(C, F, A)) -> SPsh.Car(C, F)(A):
  a(A, SCat.id(C)(A))

def SYoneda.from(-C: SCat, F: SPsh<C>, -A: SCat.Obj(C), x: SPsh.Car(C, F)(A)) -> SFam(C, F, A):
  X => h => SPsh.F1(C, F)(X, A, h, x)

# from(x) is a natural transformation: natural (F's composition law) and respecting equality
# of arrows (F's resp).
def SYoneda.from_natural(-C: SCat, F: SPsh<C>, -A: SCat.Obj(C), -x: SPsh.Car(C, F)(A)) -> SNatural(C, F, A, SYoneda.from(C, F, A, x)):
  X => Y => f => h => SPsh.fcomp(C, F)(X, Y, A, f, h, x)

def SYoneda.from_resp(-C: SCat, F: SPsh<C>, -A: SCat.Obj(C), -x: SPsh.Car(C, F)(A)) -> SResp(C, F, A, SYoneda.from(C, F, A, x)):
  X => h => k => e => SPsh.resp(C, F)(X, A, h, k, e, x)

# Both directions respect equality.
def SYoneda.to_cong(-C: SCat, -F: SPsh<C>, -A: SCat.Obj(C), -a: SFam(C, F, A), -b: SFam(C, F, A), e: SNatEq(C, F, A, a, b)) -> SPsh.Eq(C, F)(A, SYoneda.to(C, F, A, a), SYoneda.to(C, F, A, b)):
  e(A, SCat.id(C)(A))

def SYoneda.from_cong(-C: SCat, F: SPsh<C>, -A: SCat.Obj(C), -x: SPsh.Car(C, F)(A), -y: SPsh.Car(C, F)(A), e: SPsh.Eq(C, F)(A, x, y)) -> SNatEq(C, F, A, SYoneda.from(C, F, A, x), SYoneda.from(C, F, A, y)):
  X => h => SPsh.cong(C, F)(X, A, h, x, y, e)

# to . from = id: F's identity law.
def SYoneda.to_from(-C: SCat, F: SPsh<C>, -A: SCat.Obj(C), -x: SPsh.Car(C, F)(A)) -> SPsh.Eq(C, F)(A, SYoneda.to(C, F, A, SYoneda.from(C, F, A, x)), x):
  SPsh.fid(C, F)(A, x)

# from . to = id on natural transformations: naturality at (h, id), the left identity law under
# a, and one euclid step in F(X).
def SYoneda.from_to(C: SCat, F: SPsh<C>, -A: SCat.Obj(C), -a: SFam(C, F, A), nat: SNatural(C, F, A, a), resp: SResp(C, F, A, a)) -> SNatEq(C, F, A, SYoneda.from(C, F, A, SYoneda.to(C, F, A, a)), a):
  X => h => SPsh.euclid(C, F, X, a(X, SCat.comp(C)(X, A, A, SCat.id(C)(A), h)), SPsh.F1(C, F)(X, A, h, a(A, SCat.id(C)(A))), a(X, h), nat(X, A, h, SCat.id(C)(A)), resp(X, SCat.comp(C)(X, A, A, SCat.id(C)(A), h), h, SCat.idl(C)(X, A, h)))

# Naturality in A: precomposing a with g : B -> A, then taking to, is F(g) after to.
def SYoneda.pre(C: SCat, -F: SPsh<C>, -A: SCat.Obj(C), -B: SCat.Obj(C), g: SCat.Arr(C)(B, A), a: SFam(C, F, A)) -> SFam(C, F, B):
  X => h => a(X, SCat.comp(C)(X, B, A, g, h))

def SYoneda.to_natural_A(C: SCat, F: SPsh<C>, -A: SCat.Obj(C), -B: SCat.Obj(C), -g: SCat.Arr(C)(B, A), -a: SFam(C, F, A), nat: SNatural(C, F, A, a), resp: SResp(C, F, A, a)) -> SPsh.Eq(C, F)(B, SYoneda.to(C, F, B, SYoneda.pre(C, F, A, B, g, a)), SPsh.F1(C, F)(B, A, g, SYoneda.to(C, F, A, a))):
  SPsh.trans(C, F)(B, a(B, SCat.comp(C)(B, B, A, g, SCat.id(C)(B))), a(B, SCat.comp(C)(B, A, A, SCat.id(C)(A), g)), SPsh.F1(C, F)(B, A, g, a(A, SCat.id(C)(A))), resp(B, SCat.comp(C)(B, B, A, g, SCat.id(C)(B)), SCat.comp(C)(B, A, A, SCat.id(C)(A), g), SCat.idlr(C, B, A, g)), nat(B, A, g, SCat.id(C)(A)))

# Naturality in F: for a map b from F to G, to after composing with b is b after to.
def SPshMap(C: SCat, F: SPsh<C>, G: SPsh<C>) -> Type:
  @-X:SCat.Obj(C) -> SPsh.Car(C, F)(X) -> SPsh.Car(C, G)(X)

def SYoneda.post(-C: SCat, -F: SPsh<C>, -G: SPsh<C>, -A: SCat.Obj(C), b: SPshMap(C, F, G), a: SFam(C, F, A)) -> SFam(C, G, A):
  X => h => b(X, a(X, h))

def SYoneda.to_natural_F(-C: SCat, -F: SPsh<C>, G: SPsh<C>, -A: SCat.Obj(C), -b: SPshMap(C, F, G), -a: SFam(C, F, A)) -> SPsh.Eq(C, G)(A, SYoneda.to(C, G, A, SYoneda.post(C, F, G, A, b, a)), b(A, SYoneda.to(C, F, A, a))):
  SPsh.refl(C, G)(A, b(A, a(A, SCat.id(C)(A))))
