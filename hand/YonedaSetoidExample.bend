# YonedaSetoid.bend at a concrete category, checked and run.
import Base
import ./YonedaSetoid.bend as Y

type One is Data:
  One{}

# One object, the functions Nat -> Nat, composed in diagram order (comp(g, f) runs f after g),
# equal when equal at every point.  Its laws hold pointwise by computation.
def Endo() -> Y.SCat:
  Y.SCat{One, A => B => Nat -> Nat, A => B => f => g => @-x:Nat -> {f(x) == g(x) : Nat}, A => x => x, A => B => X => g => f => x => f(g(x)), A => B => f => x => {==}, A => B => f => x => {==}, A => B => X => D => f => g => h => x => {==}, A => B => f => g => e => x => Equal.sym(Nat, f(x), g(x), e(x)), A => B => f => g => h => e1 => e2 => x => Equal.trans(Nat, f(x), g(x), h(x), e1(x), e2(x))}

# A presheaf on it: Nat with its equality, acted on by application.
def Apply() -> Y.SPsh<Endo()>:
  Y.SPsh{X => Nat, X => a => b => {a == b : Nat}, X => x => {==}, X => x => y => e => Equal.sym(Nat, x, y, e), X => x => y => z => e1 => e2 => Equal.trans(Nat, x, y, z, e1, e2), X => Y => f => z => f(z), X => Y => f => x => y => e => Equal.cong(Nat, Nat, f, x, y, e), X => Y => f => g => e => x => e(x), X => x => {==}, X => Y => Z => f => g => z => {==}}

# The general theorems at this category and presheaf.
def example_to_from() -> {Y.SYoneda.to(Endo(), Apply(), One{}, Y.SYoneda.from(Endo(), Apply(), One{}, 5n)) == 5n : Nat}:
  Y.SYoneda.to_from(Endo(), Apply(), One{}, 5n)

def example_from_to(-a: Y.SFam(Endo(), Apply(), One{}), nat: Y.SNatural(Endo(), Apply(), One{}, a), resp: Y.SResp(Endo(), Apply(), One{}, a)) -> Y.SNatEq(Endo(), Apply(), One{}, Y.SYoneda.from(Endo(), Apply(), One{}, Y.SYoneda.to(Endo(), Apply(), One{}, a)), a):
  Y.SYoneda.from_to(Endo(), Apply(), One{}, a, nat, resp)

def example_nat_A(-a: Y.SFam(Endo(), Apply(), One{}), nat: Y.SNatural(Endo(), Apply(), One{}, a), resp: Y.SResp(Endo(), Apply(), One{}, a)) -> {Y.SYoneda.to(Endo(), Apply(), One{}, Y.SYoneda.pre(Endo(), Apply(), One{}, One{}, x => 1n+x, a)) == Y.SPsh.F1(Endo(), Apply())(One{}, One{}, x => 1n+x, Y.SYoneda.to(Endo(), Apply(), One{}, a)) : Nat}:
  Y.SYoneda.to_natural_A(Endo(), Apply(), One{}, One{}, x => 1n+x, a, nat, resp)

# from(5) is the family h => h(5): at the successor it gives 6; to(from(5)) is 5.
def main() -> Nat:
  Nat.add(Y.SYoneda.from(Endo(), Apply(), One{}, 5n)(One{}, x => 1n+x), Y.SYoneda.to(Endo(), Apply(), One{}, Y.SYoneda.from(Endo(), Apply(), One{}, 5n)))
