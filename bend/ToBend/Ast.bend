import Base
import ../Sys.bend as S

# Ast: the Bend 2 syntax agda2bend (and later lean2bend) writes: the target
# of the translation, a fold over the parsed Agda (Agda2Bend/Cata.bend),
# rewritten by the Bend-side passes and printed by ToBend/Print.bend.  It
# holds only what the printer needs: names are final (a local name, or an
# import's alias and the name, `C.Category.comp`), and every binder carries
# its quantity mode.
#
# Like Agda2Bend/Ast.bend it is one recursive type with spines for lists,
# so a pass over it is one def that recurses on pattern-bound parts.
# Every def is prefixed `tba.`; types and constructors `B`.

# A binder's mode: live (x), erased (-x: dead positions only), copied (+x:
# a Data value used more than once), a template (~x: syntax substituted at
# compile time, a closed term, used any number of times).
type BMode is Data:
  BmLive{}
  BmErased{}
  BmCopy{}
  BmTpl{}

type Bt is Data:
  # A variable or a name in scope, printed as it is.
  BtVar{x: List<&2, U32>}
  # f(a, b, ...): args is a BtArgs spine (f(a)(b) is an application of an
  # application).  An argument for a template parameter is a BtTplArg.
  BtApp{f: Bt, args: Bt}
  BtTplArg{t: Bt}
  # x => b, +x => b
  BtLam{m: BMode, x: List<&2, U32>, b: Bt}
  # @x:A -> B, @-x:A -> B, and A -> B when dep is False (B does not use x)
  BtPi{m: BMode, x: List<&2, U32>, dep: Bool, a: Bt, b: Bt}
  BtType{}
  # C{a, b}: a constructor and its own arguments (a datatype's parameters
  # are never written at a constructor)
  BtCon{c: List<&2, U32>, args: Bt}
  # D<A, B>: a datatype applied to its parameters (D alone when it has none)
  BtTyApp{t: List<&2, U32>, args: Bt}
  # {a == b : T} and {==}
  BtEq{t: Bt, a: Bt, b: Bt}
  BtRefl{}
  # 3n, 1n+t, "s", {t : T}
  BtNat{s: List<&2, U32>}
  BtSucc{t: Bt}
  BtStr{s: List<&2, U32>}
  BtAnn{t: Bt, ty: Bt}
  # match a b: and its cases (a BtCase spine).  The scrutinees are a BtArgs
  # spine of variables, in parameter order (Bend refuses any other order);
  # a case's patterns are a BtArgs spine, one per scrutinee: a BtCon of
  # patterns, a variable, BtNat, BtSucc of a pattern, or BtWild.  A body (a
  # def's, a case's) is a BtMatch or a BtExpr.
  BtMatch{xs: Bt, cs: Bt}
  # a def's or a case's body that is one expression, not a match
  BtExpr{e: Bt}
  # statements before a body: a rewrite (%e : P, then the body), a let
  # (x = v, then the body)
  BtRw{e: Bt, p: Bt, b: Bt}
  BtLet{x: List<&2, U32>, v: Bt, b: Bt}
  BtCase{p: Bt, b: Bt, rest: Bt}
  BtCEnd{}
  BtWild{}
  # An argument at an erased parameter, or at one whose mode is unknown (a
  # variable applied): printed as itself, its variables' uses not counted
  # by the quantity pass (ToBend/Copy.bend).
  BtDead{t: Bt}
  # A pattern variable with its mode (+x when the case uses it twice).
  BtPv{m: BMode, x: List<&2, U32>}
  # A place the translation could not fill, and why (printed as ?TODO with
  # the reason in a comment beside the def: a def holding one fails the
  # gate, and the reason is its cause in the ledger).
  BtTodo{why: List<&2, U32>}
  # argument spines
  BtArgs{a: Bt, rest: Bt}
  BtANil{}

# a parameter of a def or a datatype: its mode, name and type
type BParam is Data:
  BParam{m: BMode, x: List<&2, U32>, ty: Bt}

# a constructor field, and a constructor
type BField is Data:
  BField{x: List<&2, U32>, ty: Bt}

type BCtor is Data:
  BCtor{c: List<&2, U32>, fs: List<&2, BField>}

# A top-level item, each with its comment lines (without the `# `).
type BItem is Data:
  BiDef{name: List<&2, U32>, ps: List<&2, BParam>, ret: Bt, body: Bt, doc: List<&2, List<&2, U32>>}
  BiType{name: List<&2, U32>, ps: List<&2, BParam>, kind: Bt, cs: List<&2, BCtor>, doc: List<&2, List<&2, U32>>}
  BiComment{doc: List<&2, List<&2, U32>>}

# An import: the file's path (relative, `./`-led) and its alias.
type BImport is Data:
  BImport{path: List<&2, U32>, alias: List<&2, U32>}

# A file: its header comment lines, imports (Base is always first) and items.
type BFile is Data:
  BFile{head: List<&2, List<&2, U32>>, imports: List<&2, BImport>, items: List<&2, BItem>}

# Building --------------------------------------------------------------------

# an argument spine from a list
def tba.args(xs: List<&2, Bt>) -> Bt:
  match xs:
    case Nil{}:
      BtANil{}
    case h <> t:
      BtArgs{h, tba.args(t)}

# f applied to xs (a def of no parameters is still called: f())
def tba.call(f: Bt, xs: List<&2, Bt>) -> Bt:
  BtApp{f, tba.args(xs)}

# the number of arguments in a spine
def tba.args.len(a: Bt) -> Nat:
  match a:
    case BtArgs{h, t}:
      1n+tba.args.len(t)
    case _:
      0n

# Reading a tree -----------------------------------------------------------------

# Every name a term mentions (variables, calls, constructors, datatypes),
# in front of acc: what a file must import is read off these.
def tba.refs(t: Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case BtRw{e, p, b}:
      tba.refs(e, tba.refs(p, tba.refs(b, acc)))
    case BtLet{x, v, b}:
      tba.refs(v, tba.refs(b, acc))
    case BtDead{a}:
      tba.refs(a, acc)
    case BtVar{x}:
      x <> acc
    case BtApp{f, a}:
      tba.refs(f, tba.refs(a, acc))
    case BtTplArg{a}:
      tba.refs(a, acc)
    case BtLam{m, x, b}:
      tba.refs(b, acc)
    case BtPi{m, x, d, a, b}:
      tba.refs(a, tba.refs(b, acc))
    case BtCon{c, a}:
      c <> tba.refs(a, acc)
    case BtTyApp{n, a}:
      n <> tba.refs(a, acc)
    case BtEq{ty, a, b}:
      tba.refs(ty, tba.refs(a, tba.refs(b, acc)))
    case BtSucc{a}:
      tba.refs(a, acc)
    case BtAnn{a, ty}:
      tba.refs(a, tba.refs(ty, acc))
    case BtMatch{xs, cs}:
      tba.refs(cs, acc)
    case BtExpr{e}:
      tba.refs(e, acc)
    case BtCase{p, b, rest}:
      tba.refs(p, tba.refs(b, tba.refs(rest, acc)))
    case BtArgs{a, rest}:
      tba.refs(a, tba.refs(rest, acc))
    case _:
      acc

# the reasons of the places a term could not be filled, in front of acc
def tba.todos(t: Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case BtRw{e, p, b}:
      tba.todos(e, tba.todos(p, tba.todos(b, acc)))
    case BtLet{x, v, b}:
      tba.todos(v, tba.todos(b, acc))
    case BtDead{a}:
      tba.todos(a, acc)
    case BtTodo{why}:
      why <> acc
    case BtApp{f, a}:
      tba.todos(f, tba.todos(a, acc))
    case BtTplArg{a}:
      tba.todos(a, acc)
    case BtLam{m, x, b}:
      tba.todos(b, acc)
    case BtPi{m, x, d, a, b}:
      tba.todos(a, tba.todos(b, acc))
    case BtCon{c, a}:
      tba.todos(a, acc)
    case BtTyApp{n, a}:
      tba.todos(a, acc)
    case BtEq{ty, a, b}:
      tba.todos(ty, tba.todos(a, tba.todos(b, acc)))
    case BtSucc{a}:
      tba.todos(a, acc)
    case BtAnn{a, ty}:
      tba.todos(a, tba.todos(ty, acc))
    case BtMatch{xs, cs}:
      tba.todos(xs, tba.todos(cs, acc))
    case BtExpr{e}:
      tba.todos(e, acc)
    case BtCase{p, b, rest}:
      tba.todos(p, tba.todos(b, tba.todos(rest, acc)))
    case BtArgs{a, rest}:
      tba.todos(a, tba.todos(rest, acc))
    case _:
      acc

def tba.params.fold(~f: Bt -> List<&2, List<&2, U32>> -> List<&2, List<&2, U32>>, ps: List<&2, BParam>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      acc
    case BParam{m, x, ty} <> t:
      f(ty, tba.params.fold(~f, t, acc))

def tba.fields.fold(~f: Bt -> List<&2, List<&2, U32>> -> List<&2, List<&2, U32>>, fs: List<&2, BField>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
      acc
    case BField{x, ty} <> t:
      f(ty, tba.fields.fold(~f, t, acc))

def tba.ctors.fold(~f: Bt -> List<&2, List<&2, U32>> -> List<&2, List<&2, U32>>, cs: List<&2, BCtor>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      acc
    case BCtor{c, fs} <> t:
      tba.fields.fold(~f, fs, tba.ctors.fold(~f, t, acc))

# a fold over every term of an item (its parameters' types, its result
# type and body, its constructors' field types)
def tba.item.fold(~f: Bt -> List<&2, List<&2, U32>> -> List<&2, List<&2, U32>>, it: BItem, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match it:
    case BiDef{n, ps, ret, body, doc}:
      tba.params.fold(~f, ps, f(ret, f(body, acc)))
    case BiType{n, ps, d, cs, doc}:
      tba.params.fold(~f, ps, tba.ctors.fold(~f, cs, acc))
    case BiComment{doc}:
      acc

# the names a case's patterns bind
def tba.pvars(p: Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match p:
    case BtVar{x}:
      x <> acc
    case BtPv{m, x}:
      x <> acc
    case BtCon{c, a}:
      tba.pvars(a, acc)
    case BtArgs{a, rest}:
      tba.pvars(a, tba.pvars(rest, acc))
    case BtSucc{a}:
      tba.pvars(a, acc)
    case BtDead{a}:
      tba.pvars(a, acc)
    case _:
      acc

# the names a term binds (lambda, Pi and let binders, pattern variables)
def tba.binds(t: Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case BtRw{e, p, b}:
      tba.binds(e, tba.binds(p, tba.binds(b, acc)))
    case BtLet{x, v, b}:
      x <> tba.binds(v, tba.binds(b, acc))
    case BtDead{a}:
      tba.binds(a, acc)
    case BtApp{f, a}:
      tba.binds(f, tba.binds(a, acc))
    case BtTplArg{a}:
      tba.binds(a, acc)
    case BtLam{m, x, b}:
      x <> tba.binds(b, acc)
    case BtPi{m, x, d, a, b}:
      x <> tba.binds(a, tba.binds(b, acc))
    case BtCon{c, a}:
      tba.binds(a, acc)
    case BtTyApp{n, a}:
      tba.binds(a, acc)
    case BtEq{ty, a, b}:
      tba.binds(ty, tba.binds(a, tba.binds(b, acc)))
    case BtSucc{a}:
      tba.binds(a, acc)
    case BtAnn{a, ty}:
      tba.binds(a, tba.binds(ty, acc))
    case BtMatch{xs, cs}:
      tba.binds(cs, acc)
    case BtExpr{e}:
      tba.binds(e, acc)
    case BtCase{p, b, rest}:
      tba.pvars(p, tba.binds(b, tba.binds(rest, acc)))
    case BtArgs{a, rest}:
      tba.binds(a, tba.binds(rest, acc))
    case _:
      acc

def tba.params.names(ps: List<&2, BParam>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      acc
    case BParam{m, x, ty} <> t:
      x <> tba.params.names(t, acc)

def tba.fields.names(fs: List<&2, BField>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
      acc
    case BField{x, ty} <> t:
      x <> tba.fields.names(t, acc)

def tba.ctors.names(cs: List<&2, BCtor>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      acc
    case BCtor{c, fs} <> t:
      tba.fields.names(fs, tba.ctors.names(t, acc))

# the names an item binds: its parameters, its constructors' fields, and
# every binder inside its terms
def tba.item.names(it: BItem, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match it:
    case BiDef{n, ps, ret, body, doc}:
      tba.params.names(ps, acc)
    case BiType{n, ps, d, cs, doc}:
      tba.params.names(ps, tba.ctors.names(cs, acc))
    case BiComment{doc}:
      acc

def tba.set(xs: List<&2, List<&2, U32>>, m: Map<&2, Bool>) -> Map<&2, Bool>:
  match xs:
    case Nil{}:
      m
    case x <> t:
      tba.set(t, Map.set(&2, Bool, m, S.str(x), True{}))

def tba.has.got(r: Map<&2, Bool> & Bool) -> Bool:
  (m, b) = r
  b

def tba.keep(b: Bool, x: List<&2, U32>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match b:
    case True{}:
      rest
    case False{}:
      x <> rest

# ns less x, in front of acc
def tba.less(+x: List<&2, U32>, +ns: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      acc
    case n <> t:
      tba.keep(S.eq(n, x), n, tba.less(x, t, acc))

# tba.refs without what the term's own lambdas, Pis and lets bind: the names it
# mentions from outside (`@n:Nat -> P(n)` does not mention an n around it).
# Patterns are not told from what they match, so a case's binders stay in.
def tba.frees(t: Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case BtRw{e, p, b}:
      tba.frees(e, tba.frees(p, tba.frees(b, acc)))
    case BtLet{+x, v, b}:
      tba.frees(v, tba.less(x, tba.frees(b, Nil{}), acc))
    case BtDead{a}:
      tba.frees(a, acc)
    case BtVar{x}:
      x <> acc
    case BtApp{f, a}:
      tba.frees(f, tba.frees(a, acc))
    case BtTplArg{a}:
      tba.frees(a, acc)
    case BtLam{m, +x, b}:
      tba.less(x, tba.frees(b, Nil{}), acc)
    case BtPi{m, +x, d, a, b}:
      tba.frees(a, tba.less(x, tba.frees(b, Nil{}), acc))
    case BtCon{c, a}:
      c <> tba.frees(a, acc)
    case BtTyApp{n, a}:
      n <> tba.frees(a, acc)
    case BtEq{ty, a, b}:
      tba.frees(ty, tba.frees(a, tba.frees(b, acc)))
    case BtSucc{a}:
      tba.frees(a, acc)
    case BtAnn{a, ty}:
      tba.frees(a, tba.frees(ty, acc))
    case BtMatch{xs, cs}:
      tba.frees(cs, acc)
    case BtExpr{e}:
      tba.frees(e, acc)
    case BtCase{p, b, rest}:
      tba.frees(p, tba.frees(b, tba.frees(rest, acc)))
    case BtArgs{a, rest}:
      tba.frees(a, tba.frees(rest, acc))
    case _:
      acc

def tba.minus(xs: List<&2, List<&2, U32>>, +bound: Map<&2, Bool>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      tba.keep(tba.has.got(Map.has(&2, Bool, bound, S.str(x))), x, tba.minus(t, bound))

# The names an item uses from outside itself: a binder (a record field `to`
# named like the def `to`) is not a use, or Order would see a false cycle
# and write the def above the type it names (Bend then refuses the dotted
# type through an import: "a declared datatype (unknown: …)"), and the gate
# would drop the item as a dependent of an unrelated def.
def tba.item.refs(+it: BItem) -> List<&2, List<&2, U32>>:
  tba.minus(tba.item.fold(~tba.refs, it, Nil{}), tba.set(tba.item.names(it, tba.item.fold(~tba.binds, it, Nil{})), Map.new(&2, Bool)))

# whether an item uses n from outside itself, as tba.item.refs would say, without
# building that list (the gate asks this of every item after every repair)
def tba.item.uses(+it: BItem, +n: List<&2, U32>) -> Bool:
  Bool.and(S.mem(n, tba.item.fold(~tba.refs, it, Nil{})), Bool.not(S.mem(n, tba.item.names(it, tba.item.fold(~tba.binds, it, Nil{})))))

# names, each once, in order
def tba.nub.put(has: Bool, +r: List<&2, U32>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match has:
    case True{}:
      rest
    case False{}:
      r <> rest

def tba.nub.go(rs: List<&2, List<&2, U32>>, +seen: Map<&2, Bool>) -> List<&2, List<&2, U32>>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> t:
      tba.nub.put(tba.has.got(Map.has(&2, Bool, seen, S.str(r))), r, tba.nub.go(t, Map.set(&2, Bool, seen, S.str(r), True{})))

def tba.nub(+rs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  tba.nub.go(rs, Map.new(&2, Bool))

def tba.subst.in(+x: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> Bool:
  S.mem(x, xs)

# the names a value mentions, as a set: looked up at every binder the value
# goes under, where a list was a walk of the value per binder (a module's
# whole time on agda-unimath's commutative-algebra)
def tba.subst.fvin(+x: List<&2, U32>, fv: Map<&2, Bool>) -> Bool:
  tba.has.got(Map.has(&2, Bool, fv, S.str(x)))

def tba.subst.isvar(+v: Bt) -> Bool:
  match v:
    case BtVar{y}:
      True{}
    case _:
      False{}

# t with the variable x replaced by v (a binder of x shadows it; names are
# unique within a def, so no binder captures v).  Bodies too: a rewrite, a
# let, a match and its cases (a pattern variable or a let named x shadows
# it; a match's scrutinees only for a variable v, as Bend matches only on
# variables), and an expression body.  Until 2026-10-31 these were left as
# they were, so a rewrite step's "the body has a for b" (Cata's
# act.step.body) and act.alpha's renaming missed a step inside a lambda (a
# second J under the first's generalized parameters kept the header's
# name: `{..}(x_27)` under `x_27_b =>`, agda-unimath's
# left-unsplice-coherence-square-identifications).
# Capture (2026-11-01).  A binder y (a lambda's, a Pi's, a let's) that v
# mentions is renamed under it, y_c fresh against v and the binder's body,
# so v's y is not captured: agda-unimath's is-section-map-inv-fiber-map-Σ,
# whose goal has `λ a → …` and whose second rewrite puts f a, the clause's
# a, there ("expected : A observed : Σ …").  One pass: ren holds the
# renamed binders in scope (innermost first), on whether x is still free
# (a binder of x shadows it).
type TbRen is Data:
  TbRen{a: List<&2, U32>, b: List<&2, U32>}

# y, else y with _c appended until no name of the value's or the body's
def tba.fresh(fuel: Nat, +y: List<&2, U32>, +fv: Map<&2, Bool>, +rb: List<&2, List<&2, U32>>, hit: Bool) -> List<&2, U32>:
  match fuel hit:
    case _ False{}:
      y
    case 0n True{}:
      y
    case 1n+f True{}:
      +y2 = List.append(&2, U32, y, [95, 99])
      tba.fresh(f, y2, fv, rb, Bool.or(tba.subst.fvin(y2, fv), S.mem(y2, rb)))

# a binder's name: y, or a fresh one when y is captured (cap)
def tba.ren.nm(cap: Bool, +y: List<&2, U32>, +fv: Map<&2, Bool>, +b: Bt) -> List<&2, U32>:
  match cap:
    case True{}:
      tba.fresh(12n, y, fv, tba.refs(b, Nil{}), True{})
    case False{}:
      y

# the scope under a binder y named y2: kept empty while nothing is renamed
def tba.ren.push(+y: List<&2, U32>, +y2: List<&2, U32>, ren: List<&2, TbRen>) -> List<&2, TbRen>:
  match ren:
    case Nil{}:
      Bool.pick(List<&2, TbRen>, S.eq(y, y2), Nil{}, [TbRen{y, y2}])
    case ren:
      TbRen{y, y2} <> ren

def tba.ren.get(ren: List<&2, TbRen>, +y: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ren:
    case Nil{}:
      None{}
    case TbRen{+a, +b} <> t:
      Bool.pick(Maybe<&2, List<&2, U32>>, S.eq(a, y), Some{b}, tba.ren.get(t, y))

def tba.ren.var(m: Maybe<&2, List<&2, U32>>, +hit: Bool, +y: List<&2, U32>, +v: Bt) -> Bt:
  match m:
    case Some{z}:
      BtVar{z}
    case None{}:
      Bool.pick(Bt, hit, v, BtVar{y})

def tba.subst.go(t: Bt, +x: List<&2, U32>, +v: Bt, +fv: Map<&2, Bool>, +on: Bool, +ren: List<&2, TbRen>) -> Bt:
  match t:
    case BtExpr{e}:
      BtExpr{tba.subst.go(e, x, v, fv, on, ren)}
    case BtRw{e, p, b}:
      BtRw{tba.subst.go(e, x, v, fv, on, ren), tba.subst.go(p, x, v, fv, on, ren), tba.subst.go(b, x, v, fv, on, ren)}
    case BtLet{+y, w, +b}:
      +on2 = Bool.and(on, Bool.not(S.eq(x, y)))
      +y2 = tba.ren.nm(Bool.and(on2, tba.subst.fvin(y, fv)), y, fv, b)
      BtLet{y2, tba.subst.go(w, x, v, fv, on, ren), tba.subst.go(b, x, v, fv, on2, tba.ren.push(y, y2, ren))}
    case BtMatch{+xs, cs}:
      BtMatch{tba.subst.go(xs, x, v, fv, Bool.and(on, tba.subst.isvar(v)), ren), tba.subst.go(cs, x, v, fv, on, ren)}
    case BtCase{+p, +b, rest}:
      BtCase{p, tba.subst.go(b, x, v, fv, Bool.and(on, Bool.not(tba.subst.in(x, tba.pvars(p, Nil{})))), ren), tba.subst.go(rest, x, v, fv, on, ren)}
    case BtVar{+y}:
      tba.ren.var(tba.ren.get(ren, y), Bool.and(on, S.eq(x, y)), y, v)
    case BtApp{f, a}:
      BtApp{tba.subst.go(f, x, v, fv, on, ren), tba.subst.go(a, x, v, fv, on, ren)}
    case BtTplArg{a}:
      BtTplArg{tba.subst.go(a, x, v, fv, on, ren)}
    case BtLam{m, +y, +b}:
      +on2 = Bool.and(on, Bool.not(S.eq(x, y)))
      +y2 = tba.ren.nm(Bool.and(on2, tba.subst.fvin(y, fv)), y, fv, b)
      BtLam{m, y2, tba.subst.go(b, x, v, fv, on2, tba.ren.push(y, y2, ren))}
    case BtPi{m, +y, d, a, +b}:
      +on2 = Bool.and(on, Bool.not(S.eq(x, y)))
      +y2 = tba.ren.nm(Bool.and(on2, tba.subst.fvin(y, fv)), y, fv, b)
      BtPi{m, y2, d, tba.subst.go(a, x, v, fv, on, ren), tba.subst.go(b, x, v, fv, on2, tba.ren.push(y, y2, ren))}
    case BtCon{c, a}:
      BtCon{c, tba.subst.go(a, x, v, fv, on, ren)}
    case BtTyApp{n, a}:
      BtTyApp{n, tba.subst.go(a, x, v, fv, on, ren)}
    case BtEq{ty, a, b}:
      BtEq{tba.subst.go(ty, x, v, fv, on, ren), tba.subst.go(a, x, v, fv, on, ren), tba.subst.go(b, x, v, fv, on, ren)}
    case BtSucc{a}:
      BtSucc{tba.subst.go(a, x, v, fv, on, ren)}
    case BtAnn{a, ty}:
      BtAnn{tba.subst.go(a, x, v, fv, on, ren), tba.subst.go(ty, x, v, fv, on, ren)}
    case BtDead{a}:
      BtDead{tba.subst.go(a, x, v, fv, on, ren)}
    case BtArgs{a, rest}:
      BtArgs{tba.subst.go(a, x, v, fv, on, ren), tba.subst.go(rest, x, v, fv, on, ren)}
    case t:
      t

def tba.subst(t: Bt, +x: List<&2, U32>, +v: Bt) -> Bt:
  tba.subst.go(t, x, v, tba.set(tba.refs(v, Nil{}), Map.new(&2, Bool)), True{}, Nil{})

