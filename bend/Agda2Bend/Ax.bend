import Base
import ../Sys.bend as S
import ./Ast.bend as A
import ../ToBend/Ast.bend as T
import ./Cata.bend as C

# The postulates as extra inputs (2026-11-03; the user, 11-01: "Add the
# assumptions as extra input").  Bend has no postulate, so agda-unimath's funext,
# univalence and truncations (and all that use them, about 5,500 of the dropped
# items) go in as template parameters of every def that uses one, transitively:
#
#   def a2b_axty_eq_htpy() -> Type:
#     @-l1:Quant -> @-l2:Quant -> ... -> {f == g : @x:A -> B(x)}
#
#   def eq_htpy_use(~a2b_ax_eq_htpy: a2b_axty_eq_htpy(), -f: ..., h: ...) -> ...:
#     a2b_ax_eq_htpy(l1, l2, A, B, f, g, h)
#
# (Cata.bend writes the type as a def in the postulate's own module, through the
# quantity passes like any def, and this pass gives it the assumptions it needs:
# written out in every header, funext's three made a 1.6 KB line and the corpus takes
# lines of at most 2,000.)
#
# A template may be passed the caller's own template (closed), so a def's
# assumptions pass down unchanged: `twice(~a2b_ax_eq_htpy, ...)`.  What a def proves
# is then what it proves under them, which is what the Agda says too.
#
# Cata.bend writes a postulate's use as a call of the free variable a2b_ax_NAME
# (act.ax.call).  This pass runs on a module's items after the quantity passes, so
# those never see the extra parameters and their counts of a header's parameters
# stay true; it reads which assumptions each def needs off the Bend it has (what is
# printed, not what Agda elaborated: a level argument dropped takes its assumption
# with it), reaches a fixed point over the module's items (mutual blocks), adds the
# parameters to each def's header and the arguments to each call.  A def's alternatives
# (NAME__a2b_nu..., the gate's) share its set, so either can stand in.  A type (BiType)
# cannot take a template: one that needs an assumption fails the gate, as it did.
#
# The tables sit in the symbol table's unfoldings (the map that flows through the
# modules): "axp:VAR" a postulate's order, "axm:VAR" its module, "axd:QUALIFIED" (and
# "axd:VAR", the assumptions a postulate's own type needs) the assumptions, by order.
# Every def is prefixed `ax.`.

def ax.is(+x: List<&2, U32>) -> Bool:
  S.prefix(x, S.b("a2b_ax_"))

# Table cells ---------------------------------------------------------------------

def ax.enc(xs: List<&2, List<&2, U32>>) -> A.Ag:
  match xs:
    case Nil{}:
      A.AgNone{}
    case x <> t:
      A.AgDummy{x, ax.enc(t)}

def ax.dec(a: A.Ag) -> List<&2, List<&2, U32>>:
  match a:
    case A.AgDummy{x, t}:
      x <> ax.dec(t)
    case _:
      Nil{}

def ax.cell.got(r: Map<&2, C.ActCopy> & C.ActCopy) -> C.ActCopy:
  (m, c) = r
  c

def ax.cell(+unf: Map<&2, C.ActCopy>, +k: String) -> C.ActCopy:
  ax.cell.got(Map.get(C.ActCopy, C.ActCopy{0n, A.AgNone{}}, unf, k))

def ax.cell.body(c: C.ActCopy) -> A.Ag:
  match c:
    case C.ActCopy{n, b}:
      b

def ax.cell.n(c: C.ActCopy) -> Nat:
  match c:
    case C.ActCopy{n, b}:
      n

def ax.get(+unf: Map<&2, C.ActCopy>, +k: String) -> List<&2, List<&2, U32>>:
  ax.dec(ax.cell.body(ax.cell(unf, k)))

def ax.put(+k: String, xs: List<&2, List<&2, U32>>, unf: Map<&2, C.ActCopy>) -> Map<&2, C.ActCopy>:
  Map.set(&2, C.ActCopy, unf, k, C.ActCopy{0n, ax.enc(xs)})

# a postulate's place in the order of declaration (its assumptions come first)
def ax.idx(+unf: Map<&2, C.ActCopy>, +v: List<&2, U32>) -> Nat:
  ax.cell.n(ax.cell(unf, "axp:" ++ S.str(v)))

# a postulate's symbol: its order and module.  Called on every declaration; a builtin
# (String, under BUILTIN) is Base's, no assumption.
def ax.sym.of(s: C.ActSym, +top: List<&2, U32>, +v: List<&2, U32>, +unf: Map<&2, C.ActCopy>) -> Map<&2, C.ActCopy>:
  match s:
    case C.ActSym{m, n, k, ms, ar, C.AbNone{}, fs, c, cp}:
      +ix = ax.cell.n(ax.cell(unf, "axn"))
      Map.set(&2, C.ActCopy, ax.put("axm:" ++ S.str(v), [top], Map.set(&2, C.ActCopy, unf, "axn", C.ActCopy{1n+ix, A.AgNone{}})), "axp:" ++ S.str(v), C.ActCopy{ix, A.AgNone{}})
    case _:
      unf

def ax.sym(d: A.AgDecl, s: C.ActSym, +top: List<&2, U32>, +nm: List<&2, U32>, +unf: Map<&2, C.ActCopy>) -> Map<&2, C.ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDPost{}}:
      ax.sym.of(s, top, C.act.ax.var(nm), unf)
    case _:
      unf

# Sets of assumptions: lists in the order of declaration --------------------------

def ax.ins(+x: List<&2, U32>, +ix: Nat, xs: List<&2, List<&2, U32>>, +unf: Map<&2, C.ActCopy>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      [x]
    case +h <> +t:
      Bool.pick(List<&2, List<&2, U32>>, S.eq(h, x), h <> t, Bool.pick(List<&2, List<&2, U32>>, Nat.is_lt(ix, ax.idx(unf, h)), x <> (h <> t), h <> ax.ins(x, ix, t, unf)))

def ax.union(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>, +unf: Map<&2, C.ActCopy>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      ys
    case +x <> t:
      ax.ins(x, ax.idx(unf, x), ax.union(t, ys, unf), unf)

# A module's view ----------------------------------------------------------------

# the module's own item names and its alias with the dot
type AxV is Data:
  AxV{names: Map<&2, Bool>, q: List<&2, U32>}

def ax.alt.n(+n: List<&2, U32>) -> Nat:
  Bool.pick(Nat, S.suffix(n, S.b("__a2b_nu")), 8n, Bool.pick(Nat, Bool.or(S.suffix(n, S.b("__a2b_nu2")), S.suffix(n, S.b("__a2b_nu3"))), 9n, 0n))

# an alternative's def
def ax.base(+n: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, n, Nat.sub(S.len(n), ax.alt.n(n)))

def ax.has.got(r: Map<&2, Bool> & Bool) -> Bool:
  (m, b) = r
  b

def ax.local(+v: AxV, +x: List<&2, U32>) -> Bool:
  match v:
    case AxV{+names, q}:
      ax.has.got(Map.has(&2, Bool, names, S.str(x)))

def ax.q(+v: AxV) -> List<&2, U32>:
  match v:
    case AxV{names, q}:
      q

# a postulate's type def, and its postulate
def ax.is.ty(+x: List<&2, U32>) -> Bool:
  S.prefix(x, S.b("a2b_axty_"))

def ax.of.ty(+x: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, S.b("a2b_ax_"), List.drop(&2, U32, x, 9n))

# the cell of a name as this module prints it (matches, not Bool.pick: a pick
# builds all four keys, and this runs for every name of every def)
def ax.key.of(isax: Bool, isty: Bool, here: Bool, +v: AxV, +n: List<&2, U32>) -> String:
  match isax isty here:
    case True{} _ _:
      "axd:" ++ S.str(n)
    case False{} True{} _:
      "axd:" ++ S.str(ax.of.ty(n))
    case False{} False{} True{}:
      "axd:" ++ S.str(List.append(&2, U32, ax.q(v), ax.base(n)))
    case False{} False{} False{}:
      "axd:" ++ S.str(n)

def ax.key(+v: AxV, +n: List<&2, U32>) -> String:
  ax.key.of(ax.is(n), ax.is.ty(n), ax.local(v, n), v, n)

# what a name in a def's text brings: a postulate itself and what its type needs
def ax.of.pick(isax: Bool, +xs: List<&2, List<&2, U32>>, +x: List<&2, U32>, +unf: Map<&2, C.ActCopy>) -> List<&2, List<&2, U32>>:
  match isax:
    case True{}:
      ax.ins(x, ax.idx(unf, x), xs, unf)
    case False{}:
      xs

def ax.of(+v: AxV, +unf: Map<&2, C.ActCopy>, +x: List<&2, U32>) -> List<&2, List<&2, U32>>:
  ax.of.pick(ax.is(x), ax.get(unf, ax.key(v, x)), x, unf)

def ax.of.all(rs: List<&2, List<&2, U32>>, +v: AxV, +unf: Map<&2, C.ActCopy>) -> List<&2, List<&2, U32>>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> t:
      ax.union(ax.of(v, unf, r), ax.of.all(t, v, unf), unf)

# The fixed point ----------------------------------------------------------------

def ax.len(xs: List<&2, List<&2, U32>>) -> Nat:
  List.length(&2, List<&2, U32>, xs)

# a name's cell raised to what its text needs; ch: it rose
type AxP is Data:
  AxP{unf: Map<&2, C.ActCopy>, ch: Bool}

def ax.raise(+k: String, +rs: List<&2, List<&2, U32>>, +v: AxV, p: AxP) -> AxP:
  match p:
    case AxP{+unf, ch}:
      +old = ax.get(unf, k)
      +new = ax.union(ax.of.all(rs, v, unf), old, unf)
      Bool.pick(AxP, Nat.is_eq(ax.len(new), ax.len(old)), AxP{unf, ch}, AxP{ax.put(k, new, unf), True{}})

# each def's cell and the names of its text, each once: read once, not per pass
def ax.refs(+it: T.BItem) -> List<&2, List<&2, U32>>:
  T.tba.nub(T.tba.item.fold(~T.tba.refs, it, Nil{}))

type AxD is Data:
  AxD{k: String, rs: List<&2, List<&2, U32>>}

def ax.defs(its: List<&2, T.BItem>, +v: AxV) -> List<&2, AxD>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{+n, +ps, +ret, +body, +doc} <> t:
      AxD{ax.key(v, n), ax.refs(T.BiDef{n, ps, ret, body, doc})} <> ax.defs(t, v)
    case it <> t:
      ax.defs(t, v)

def ax.pass(ds: List<&2, AxD>, +v: AxV, p: AxP) -> AxP:
  match ds:
    case Nil{}:
      p
    case AxD{+k, +rs} <> t:
      ax.pass(t, v, ax.raise(k, rs, v, p))

def ax.fix.go(fuel: Nat, +ds: List<&2, AxD>, +v: AxV, p: AxP) -> Map<&2, C.ActCopy>:
  match fuel p:
    case _ AxP{unf, False{}}:
      unf
    case 0n AxP{unf, True{}}:
      unf
    case 1n+f AxP{+unf, True{}}:
      ax.fix.go(f, ds, v, ax.pass(ds, v, AxP{unf, False{}}))

# The rewrite ---------------------------------------------------------------------

def ax.mem(+x: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> Bool:
  C.act.ax.mem(x, xs)

def ax.tpls(xs: List<&2, List<&2, U32>>, a: T.Bt) -> T.Bt:
  match xs:
    case Nil{}:
      a
    case x <> t:
      T.BtArgs{T.BtTplArg{T.BtVar{x}}, ax.tpls(t, a)}

# the names of a module's text that need an assumption, with what they need: a
# def's whole text is read per call otherwise, and most modules have none
def ax.need.put(xs: List<&2, List<&2, U32>>, +k: String, need: Map<&2, List<&2, List<&2, U32>>>) -> Map<&2, List<&2, List<&2, U32>>>:
  match xs:
    case Nil{}:
      need
    case +x <> +t:
      Map.set(&2, List<&2, List<&2, U32>>, need, k, x <> t)

def ax.need.go(rs: List<&2, List<&2, U32>>, +v: AxV, +unf: Map<&2, C.ActCopy>, need: Map<&2, List<&2, List<&2, U32>>>) -> Map<&2, List<&2, List<&2, U32>>>:
  match rs:
    case Nil{}:
      need
    case +r <> t:
      ax.need.go(t, v, unf, ax.need.put(ax.get(unf, ax.key(v, r)), S.str(r), need))

def ax.need.got(r: Map<&2, List<&2, List<&2, U32>>> & List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  (m, x) = r
  x

# what a call of f must pass: nothing for a postulate or a local variable
def ax.call.of(xs: List<&2, List<&2, U32>>, +f: List<&2, U32>, +bd: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      Bool.pick(List<&2, List<&2, U32>>, Bool.or(ax.is(f), ax.mem(f, bd)), Nil{}, x <> t)

def ax.call(+f: List<&2, U32>, +bd: List<&2, List<&2, U32>>, +need: Map<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, U32>>:
  ax.call.of(ax.need.got(Map.get(List<&2, List<&2, U32>>, Nil{}, need, S.str(f))), f, bd)

def ax.go(t: T.Bt, +bd: List<&2, List<&2, U32>>, +need: Map<&2, List<&2, List<&2, U32>>>) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+f}, a}:
      T.BtApp{T.BtVar{f}, ax.tpls(ax.call(f, bd, need), ax.go(a, bd, need))}
    case T.BtApp{f, a}:
      T.BtApp{ax.go(f, bd, need), ax.go(a, bd, need)}
    case T.BtTplArg{a}:
      T.BtTplArg{ax.go(a, bd, need)}
    case T.BtLam{m, +x, b}:
      T.BtLam{m, x, ax.go(b, x <> bd, need)}
    case T.BtPi{m, +x, d, a, b}:
      T.BtPi{m, x, d, ax.go(a, bd, need), ax.go(b, x <> bd, need)}
    case T.BtCon{c, a}:
      T.BtCon{c, ax.go(a, bd, need)}
    case T.BtTyApp{c, a}:
      T.BtTyApp{c, ax.go(a, bd, need)}
    case T.BtEq{ty, a, b}:
      T.BtEq{ax.go(ty, bd, need), ax.go(a, bd, need), ax.go(b, bd, need)}
    case T.BtSucc{a}:
      T.BtSucc{ax.go(a, bd, need)}
    case T.BtAnn{a, ty}:
      T.BtAnn{ax.go(a, bd, need), ax.go(ty, bd, need)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, ax.go(cs, bd, need)}
    case T.BtExpr{e}:
      T.BtExpr{ax.go(e, bd, need)}
    case T.BtRw{e, p, b}:
      T.BtRw{ax.go(e, bd, need), ax.go(p, bd, need), ax.go(b, bd, need)}
    case T.BtLet{+x, a, b}:
      T.BtLet{x, ax.go(a, bd, need), ax.go(b, x <> bd, need)}
    case T.BtCase{+p, b, rest}:
      T.BtCase{p, ax.go(b, T.tba.pvars(p, bd), need), ax.go(rest, bd, need)}
    case T.BtDead{a}:
      T.BtDead{ax.go(a, bd, need)}
    case T.BtArgs{a, rest}:
      T.BtArgs{ax.go(a, bd, need), ax.go(rest, bd, need)}
    case t:
      t

# a header's parameters, each in the scope of those before it
def ax.ps(ps: List<&2, T.BParam>, +bd: List<&2, List<&2, U32>>, +need: Map<&2, List<&2, List<&2, U32>>>) -> List<&2, T.BParam>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, +x, ty} <> t:
      T.BParam{m, x, ax.go(ty, bd, need)} <> ax.ps(t, x <> bd, need)

def ax.bound(ps: List<&2, T.BParam>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      acc
    case T.BParam{m, +x, ty} <> t:
      ax.bound(t, x <> acc)

# the name of a postulate's type def: VAR's a2b_ax_ for a2b_axty_
def ax.ty.name(+x: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, S.b("a2b_axty_"), List.drop(&2, U32, x, 7n))

def ax.first(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case x <> t:
      x
    case Nil{}:
      Nil{}

def ax.mod(+unf: Map<&2, C.ActCopy>, +x: List<&2, U32>) -> List<&2, U32>:
  ax.first(ax.get(unf, "axm:" ++ S.str(x)))

# the type of the parameter for x: its type def, given what that needs
def ax.ty.call(+x: List<&2, U32>, +env: C.ActEnv, +unf: Map<&2, C.ActCopy>, +v: AxV) -> T.Bt:
  +m = ax.mod(unf, x)
  T.BtApp{T.BtVar{C.act.ref.of(C.act.is.here(env, m), env, m, ax.ty.name(x))}, ax.tpls(ax.get(unf, ax.key(v, x)), T.BtANil{})}

# the template parameters of a def needing xs
def ax.params(xs: List<&2, List<&2, U32>>, +env: C.ActEnv, +v: AxV, +unf: Map<&2, C.ActCopy>) -> List<&2, T.BParam>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      T.BParam{T.BmTpl{}, x, ax.ty.call(x, env, unf, v)} <> ax.params(t, env, v, unf)

def ax.item(it: T.BItem, +env: C.ActEnv, +v: AxV, +unf: Map<&2, C.ActCopy>, +need: Map<&2, List<&2, List<&2, U32>>>) -> T.BItem:
  match it:
    case T.BiDef{+n, +ps, ret, body, doc}:
      +bd = ax.bound(ps, Nil{})
      T.BiDef{n, List.append(&2, T.BParam, ax.params(ax.get(unf, ax.key(v, n)), env, v, unf), ax.ps(ps, Nil{}, need)), ax.go(ret, bd, need), ax.go(body, bd, need), doc}
    case it:
      it

def ax.items.go(its: List<&2, T.BItem>, +env: C.ActEnv, +v: AxV, +unf: Map<&2, C.ActCopy>, +need: Map<&2, List<&2, List<&2, U32>>>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case it <> t:
      ax.item(it, env, v, unf, need) <> ax.items.go(t, env, v, unf, need)

# the items as they are when nothing they mention needs an assumption
def ax.items(none: Bool, +its: List<&2, T.BItem>, +env: C.ActEnv, +v: AxV, +unf: Map<&2, C.ActCopy>, +need: Map<&2, List<&2, List<&2, U32>>>) -> List<&2, T.BItem>:
  match none:
    case True{}:
      its
    case False{}:
      ax.items.go(its, env, v, unf, need)

# The pass ------------------------------------------------------------------------

def ax.names(its: List<&2, T.BItem>, acc: Map<&2, Bool>) -> Map<&2, Bool>:
  match its:
    case Nil{}:
      acc
    case T.BiDef{+n, ps, ret, body, doc} <> t:
      ax.names(t, Map.set(&2, Bool, acc, S.str(n), True{}))
    case it <> t:
      ax.names(t, acc)

# a module's items and its alternatives with their assumptions, and the table for
# the modules after it.  q: the module's alias with the dot.
type AxOut is Data:
  AxOut{fits: List<&2, T.BItem>, alts: List<&2, T.BItem>, unf: Map<&2, C.ActCopy>}

def ax.names.all(ds: List<&2, AxD>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      acc
    case AxD{k, +rs} <> t:
      ax.names.all(t, List.append(&2, List<&2, U32>, rs, acc))

def ax.need(+ds: List<&2, AxD>, +its: List<&2, T.BItem>, +v: AxV, +unf: Map<&2, C.ActCopy>) -> Map<&2, List<&2, List<&2, U32>>>:
  ax.need.go(T.tba.nub(ax.names.all(ds, Nil{})), v, unf, Map.new(&2, List<&2, List<&2, U32>>))

def ax.none.cell(xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      False{}

# whether no name a def mentions, and no def itself, needs an assumption
def ax.none.go(ds: List<&2, AxD>, +unf: Map<&2, C.ActCopy>, ok: Bool) -> Bool:
  match ds ok:
    case _ False{}:
      False{}
    case Nil{} True{}:
      True{}
    case AxD{+k, rs} <> t True{}:
      ax.none.go(t, unf, ax.none.cell(ax.get(unf, k)))

def ax.none(+ds: List<&2, AxD>, +need: Map<&2, List<&2, List<&2, U32>>>, +v: AxV, +unf: Map<&2, C.ActCopy>) -> Bool:
  Bool.and(Nat.is_eq(Map.size(&2, List<&2, List<&2, U32>>, need), 0n), ax.none.go(ds, unf, True{}))

def ax.module(+m: List<&2, U32>, +q: List<&2, U32>, +tab: Map<&2, C.ActSym>, +al: Map<&2, List<&2, U32>>, +unf0: Map<&2, C.ActCopy>, +fits: List<&2, T.BItem>, +alts: List<&2, T.BItem>) -> AxOut:
  +all = List.append(&2, T.BItem, fits, alts)
  +v : AxV = AxV{ax.names(all, Map.new(&2, Bool)), q}
  +env : C.ActEnv = C.ActEnv{m, tab, al, unf0}
  +ds = ax.defs(all, v)
  +unf = ax.fix.go(16n, ds, v, AxP{unf0, True{}})
  +need = ax.need(ds, all, v, unf)
  +none = ax.none(ds, need, v, unf)
  AxOut{ax.items(none, fits, env, v, unf, need), ax.items(none, alts, env, v, unf, need), unf}
