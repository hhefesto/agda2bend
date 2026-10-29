import Base
import ../Sys.bend as S
import ./Ast.bend as T
import ./Print.bend as P

# Mutual with-functions (2026-10-29) ----------------------------------------------
#
# Agda's `filter P? (x ∷ xs) with does (P? x) ... | true = x ∷ filter P? xs`
# is filter calling with-658 and with-658 calling filter back, and Bend has
# no mutual recursion (a def calls only the ones above it): the gate
# dropped with-658 ("expected a term, observed '~'": filter's template call
# before filter) and every user of filter with it (PLFA: 66 dependents of
# with-658, and takeWhile's, dropWhile's, span's, unalignWith's).
#
# When a def W of the module calls a def P of the module that calls W, and
# every call of P in W is the same call, over W's parameters only, W takes
# that call's value as one more parameter, w_rec, and every call of W in the
# module passes P's call at its own arguments:
#
#     filter's case:  with_658(.., x_5, does(..), xs, filter(.., xs))
#     with_658:       True: cons{x, w_rec}; False: w_rec
#
# The recursive call is filter's own, on xs.  W's type must not mention P,
# and W must not call itself; another module's call of W (a with-function
# of a lemma about filter) keeps W's old arity and fails the gate as before.

# the argument spines of the calls of p in t, in front of acc
def twl.calls(t: T.Bt, +p: List<&2, U32>, +acc: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match t:
    case T.BtApp{T.BtVar{+f}, +a}:
      twl.calls(a, p, Bool.pick(List<&2, T.Bt>, S.eq(f, p), a <> acc, acc))
    case T.BtApp{f, a}:
      twl.calls(f, p, twl.calls(a, p, acc))
    case T.BtRw{e, p2, b}:
      twl.calls(e, p, twl.calls(p2, p, twl.calls(b, p, acc)))
    case T.BtLet{x, v, b}:
      twl.calls(v, p, twl.calls(b, p, acc))
    case T.BtDead{a}:
      twl.calls(a, p, acc)
    case T.BtTplArg{a}:
      twl.calls(a, p, acc)
    case T.BtLam{m, x, b}:
      twl.calls(b, p, acc)
    case T.BtPi{m, x, d, a, b}:
      twl.calls(a, p, twl.calls(b, p, acc))
    case T.BtCon{c, a}:
      twl.calls(a, p, acc)
    case T.BtTyApp{n, a}:
      twl.calls(a, p, acc)
    case T.BtEq{ty, a, b}:
      twl.calls(ty, p, twl.calls(a, p, twl.calls(b, p, acc)))
    case T.BtSucc{a}:
      twl.calls(a, p, acc)
    case T.BtAnn{a, ty}:
      twl.calls(a, p, twl.calls(ty, p, acc))
    case T.BtMatch{xs, cs}:
      twl.calls(cs, p, acc)
    case T.BtExpr{e}:
      twl.calls(e, p, acc)
    case T.BtCase{p2, b, rest}:
      twl.calls(b, p, twl.calls(rest, p, acc))
    case T.BtArgs{a, rest}:
      twl.calls(a, p, twl.calls(rest, p, acc))
    case _:
      acc

# t with every call of p replaced by r
def twl.rep(t: T.Bt, +p: List<&2, U32>, +r: T.Bt) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+f}, a}:
      Bool.pick(T.Bt, S.eq(f, p), r, T.BtApp{T.BtVar{f}, twl.rep(a, p, r)})
    case T.BtApp{f, a}:
      T.BtApp{twl.rep(f, p, r), twl.rep(a, p, r)}
    case T.BtRw{e, p2, b}:
      T.BtRw{twl.rep(e, p, r), twl.rep(p2, p, r), twl.rep(b, p, r)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, twl.rep(v, p, r), twl.rep(b, p, r)}
    case T.BtDead{a}:
      T.BtDead{twl.rep(a, p, r)}
    case T.BtTplArg{a}:
      T.BtTplArg{twl.rep(a, p, r)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, twl.rep(b, p, r)}
    case T.BtPi{m, x, d, a, b}:
      T.BtPi{m, x, d, twl.rep(a, p, r), twl.rep(b, p, r)}
    case T.BtCon{c, a}:
      T.BtCon{c, twl.rep(a, p, r)}
    case T.BtTyApp{n, a}:
      T.BtTyApp{n, twl.rep(a, p, r)}
    case T.BtEq{ty, a, b}:
      T.BtEq{twl.rep(ty, p, r), twl.rep(a, p, r), twl.rep(b, p, r)}
    case T.BtSucc{a}:
      T.BtSucc{twl.rep(a, p, r)}
    case T.BtAnn{a, ty}:
      T.BtAnn{twl.rep(a, p, r), twl.rep(ty, p, r)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, twl.rep(cs, p, r)}
    case T.BtExpr{e}:
      T.BtExpr{twl.rep(e, p, r)}
    case T.BtCase{p2, b, rest}:
      T.BtCase{p2, twl.rep(b, p, r), twl.rep(rest, p, r)}
    case T.BtArgs{a, rest}:
      T.BtArgs{twl.rep(a, p, r), twl.rep(rest, p, r)}
    case t:
      t

# an argument as the term it passes (a template's or a dead one's mark off)
def twl.unwrap(a: T.Bt) -> T.Bt:
  match a:
    case T.BtTplArg{x}:
      x
    case T.BtDead{x}:
      x
    case a:
      a

def twl.snoc(a: T.Bt, x: T.Bt) -> T.Bt:
  match a:
    case T.BtArgs{h, rest}:
      T.BtArgs{h, twl.snoc(rest, x)}
    case _:
      T.BtArgs{x, T.BtANil{}}

def twl.fresh(+n: List<&2, U32>, +k: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, n, k)

# t with each name of ns renamed n ++ k (before a simultaneous substitution)
def twl.ren(ns: List<&2, List<&2, U32>>, t: T.Bt, +k: List<&2, U32>) -> T.Bt:
  match ns:
    case Nil{}:
      t
    case +n <> rest:
      twl.ren(rest, T.tba.subst(t, n, T.BtVar{twl.fresh(n, k)}), k)

# t with each n ++ k of ns replaced by the argument at its place
def twl.sub(ns: List<&2, List<&2, U32>>, a: T.Bt, t: T.Bt, +k: List<&2, U32>) -> T.Bt:
  match ns a:
    case +n <> rest T.BtArgs{x, more}:
      twl.sub(rest, more, T.tba.subst(t, twl.fresh(n, k), twl.unwrap(x)), k)
    case _ _:
      t

def twl.pnames(ps: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      x <> twl.pnames(t)

# a call's arguments with the ones at W's parameters its body no longer
# reads (filter's xs, read only by the call w_rec now holds) dead, so the
# caller's own use of them is the one that counts
def twl.deaden(a: T.Bt, dl: List<&2, Bool>) -> T.Bt:
  match a dl:
    case T.BtArgs{T.BtTplArg{x}, rest} d <> dt:
      T.BtArgs{T.BtTplArg{x}, twl.deaden(rest, dt)}
    case T.BtArgs{T.BtDead{x}, rest} d <> dt:
      T.BtArgs{T.BtDead{x}, twl.deaden(rest, dt)}
    case T.BtArgs{x, rest} True{} <> dt:
      T.BtArgs{T.BtDead{x}, twl.deaden(rest, dt)}
    case T.BtArgs{x, rest} False{} <> dt:
      T.BtArgs{x, twl.deaden(rest, dt)}
    case a _:
      a

# the calls of w in t given one more argument: p's call (rx: its spine over
# w's parameters renamed, ns) at the call's arguments
def twl.add(t: T.Bt, +w: List<&2, U32>, +rx: T.Bt, +ns: List<&2, List<&2, U32>>, +dl: List<&2, Bool>) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+f}, a}:
      +a2 = twl.add(a, w, rx, ns, dl)
      Bool.pick(T.Bt, S.eq(f, w), T.BtApp{T.BtVar{f}, twl.snoc(twl.deaden(a2, dl), twl.sub(ns, a2, rx, S.b("_wl0")))}, T.BtApp{T.BtVar{f}, a2})
    case T.BtApp{f, a}:
      T.BtApp{twl.add(f, w, rx, ns, dl), twl.add(a, w, rx, ns, dl)}
    case T.BtRw{e, p2, b}:
      T.BtRw{twl.add(e, w, rx, ns, dl), twl.add(p2, w, rx, ns, dl), twl.add(b, w, rx, ns, dl)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, twl.add(v, w, rx, ns, dl), twl.add(b, w, rx, ns, dl)}
    case T.BtDead{a}:
      T.BtDead{twl.add(a, w, rx, ns, dl)}
    case T.BtTplArg{a}:
      T.BtTplArg{twl.add(a, w, rx, ns, dl)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, twl.add(b, w, rx, ns, dl)}
    case T.BtPi{m, x, d, a, b}:
      T.BtPi{m, x, d, twl.add(a, w, rx, ns, dl), twl.add(b, w, rx, ns, dl)}
    case T.BtCon{c, a}:
      T.BtCon{c, twl.add(a, w, rx, ns, dl)}
    case T.BtTyApp{n, a}:
      T.BtTyApp{n, twl.add(a, w, rx, ns, dl)}
    case T.BtEq{ty, a, b}:
      T.BtEq{twl.add(ty, w, rx, ns, dl), twl.add(a, w, rx, ns, dl), twl.add(b, w, rx, ns, dl)}
    case T.BtSucc{a}:
      T.BtSucc{twl.add(a, w, rx, ns, dl)}
    case T.BtAnn{a, ty}:
      T.BtAnn{twl.add(a, w, rx, ns, dl), twl.add(ty, w, rx, ns, dl)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, twl.add(cs, w, rx, ns, dl)}
    case T.BtExpr{e}:
      T.BtExpr{twl.add(e, w, rx, ns, dl)}
    case T.BtCase{p2, b, rest}:
      T.BtCase{p2, twl.add(b, w, rx, ns, dl), twl.add(rest, w, rx, ns, dl)}
    case T.BtArgs{a, rest}:
      T.BtArgs{twl.add(a, w, rx, ns, dl), twl.add(rest, w, rx, ns, dl)}
    case t:
      t

def twl.mem(+x: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(S.eq(x, h), twl.mem(x, t))

def twl.any.in(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(twl.mem(h, ys), twl.any.in(t, ys))

def twl.text(t: T.Bt) -> List<&2, U32>:
  P.tpr.t(t, P.TpLoose{}, 0n, Nil{})

def twl.all.same(+x: List<&2, U32>, xs: List<&2, T.Bt>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(S.eq(twl.text(h), x), twl.all.same(x, t))

def twl.ps.refs(ps: List<&2, T.BParam>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      acc
    case T.BParam{m, x, ty} <> t:
      T.tba.refs(ty, twl.ps.refs(t, acc))

# P's call in W: Some(its spine) when every call of p in W is that one, over
# W's parameters only, W calls neither itself nor p in its type, and the
# spine has p's arity
def twl.spine.of(cs: List<&2, T.Bt>, +wn: List<&2, U32>, +wps: List<&2, T.BParam>, +wret: T.Bt, +wbody: T.Bt, +pn: List<&2, U32>, +np: Nat) -> Maybe<&2, T.Bt>:
  match cs:
    case Nil{}:
      None{}
    case +c <> rest:
      +ok = Bool.and(Bool.and(twl.all.same(twl.text(c), rest), Bool.not(twl.any.in(T.tba.refs(c, Nil{}), T.tba.binds(wbody, Nil{})))), Bool.and(Bool.and(Bool.not(twl.mem(wn, T.tba.refs(wbody, Nil{}))), Bool.not(twl.mem(pn, T.tba.refs(wret, twl.ps.refs(wps, Nil{}))))), Nat.is_eq(T.tba.args.len(c), np)))
      Bool.pick(Maybe<&2, T.Bt>, ok, Some{c}, None{})

def twl.spine(+wn: List<&2, U32>, +wps: List<&2, T.BParam>, +wret: T.Bt, +wbody: T.Bt, +pn: List<&2, U32>, +np: Nat) -> Maybe<&2, T.Bt>:
  twl.spine.of(twl.calls(wbody, pn, Nil{}), wn, wps, wret, wbody, pn, np)

# a def of the module by name
type TwlDef is Data:
  TwlDef{n: List<&2, U32>, ps: List<&2, T.BParam>, ret: T.Bt, body: T.Bt}

def twl.def.of(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Maybe<&2, TwlDef>:
  match its:
    case Nil{}:
      None{}
    case T.BiDef{+m, +ps, +ret, +body, doc} <> t:
      Bool.pick(Maybe<&2, TwlDef>, S.eq(m, n), Some{TwlDef{m, ps, ret, body}}, twl.def.of(t, n))
    case i <> t:
      twl.def.of(t, n)

# a pair to rewrite: W, P, P's call in W, P's parameters and return type
type TwlPair is Data:
  TwlPair{w: List<&2, U32>, p: List<&2, U32>, c: T.Bt, pps: List<&2, T.BParam>, pret: T.Bt}

def twl.pair.fin(+wn: List<&2, U32>, +pn: List<&2, U32>, +pps: List<&2, T.BParam>, +pret: T.Bt, m: Maybe<&2, T.Bt>) -> Maybe<&2, TwlPair>:
  match m:
    case Some{c}:
      Some{TwlPair{wn, pn, c, pps, pret}}
    case None{}:
      None{}

def twl.pair.of(+w: TwlDef, m: Maybe<&2, TwlDef>) -> Maybe<&2, TwlPair>:
  match w m:
    case TwlDef{+wn, +wps, +wret, +wbody} Some{TwlDef{+pn, +pps, +pret, +pbody}}:
      Bool.pick(Maybe<&2, TwlPair>, Bool.and(Bool.not(S.eq(wn, pn)), twl.mem(wn, T.tba.refs(pbody, Nil{}))), twl.pair.fin(wn, pn, pps, pret, twl.spine(wn, wps, wret, wbody, pn, List.length(&2, T.BParam, pps))), None{})
    case _ _:
      None{}

# the first def of the module W calls that makes a pair with it
def twl.first(a: Maybe<&2, TwlPair>, b: Maybe<&2, TwlPair>) -> Maybe<&2, TwlPair>:
  match a:
    case Some{p}:
      Some{p}
    case None{}:
      b

def twl.pair.in(+w: TwlDef, rs: List<&2, List<&2, U32>>, +its: List<&2, T.BItem>) -> Maybe<&2, TwlPair>:
  match rs:
    case Nil{}:
      None{}
    case +r <> t:
      twl.first(twl.pair.of(w, twl.def.of(its, r)), twl.pair.in(w, t, its))

def twl.pairs.put(m: Maybe<&2, TwlPair>, rest: List<&2, TwlPair>) -> List<&2, TwlPair>:
  match m:
    case Some{p}:
      p <> rest
    case None{}:
      rest

def twl.pairs(xs: List<&2, T.BItem>, +its: List<&2, T.BItem>) -> List<&2, TwlPair>:
  match xs:
    case Nil{}:
      Nil{}
    case T.BiDef{+n, +ps, +ret, +body, doc} <> t:
      twl.pairs.put(twl.pair.in(TwlDef{n, ps, ret, body}, T.tba.refs(body, Nil{}), its), twl.pairs(t, its))
    case i <> t:
      twl.pairs(t, its)

# one pair's rewrite over the module's items: W gets w_rec (its type P's
# return type at P's call's arguments) and reads it for P's calls; every
# call of W passes P's call at its arguments
def twl.item(it: T.BItem, +pr: TwlPair, +wns: List<&2, List<&2, U32>>, +dl: List<&2, Bool>) -> T.BItem:
  match it pr:
    case T.BiDef{+n, +ps, +ret, +body, +doc} TwlPair{+w, +p, +c, +pps, +pret}:
      +rx : T.Bt = T.BtApp{T.BtVar{p}, twl.ren(wns, c, S.b("_wl0"))}
      +rty : T.Bt = twl.sub(twl.pnames(pps), c, twl.ren(twl.pnames(pps), pret, S.b("_wl1")), S.b("_wl1"))
      Bool.pick(T.BItem, S.eq(n, w), T.BiDef{n, List.append(&2, T.BParam, ps, [T.BParam{T.BmLive{}, S.b("w_rec"), rty}]), ret, twl.rep(body, p, T.BtVar{S.b("w_rec")}), doc}, T.BiDef{n, ps, ret, twl.add(body, w, rx, wns, dl), doc})
    case it pr:
      it

def twl.items.one(its: List<&2, T.BItem>, +pr: TwlPair, +wns: List<&2, List<&2, U32>>, +dl: List<&2, Bool>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case it <> t:
      twl.item(it, pr, wns, dl) <> twl.items.one(t, pr, wns, dl)

def twl.dl.ps(ps: List<&2, T.BParam>, +refs: List<&2, List<&2, U32>>) -> List<&2, Bool>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, +x, ty} <> t:
      Bool.not(twl.mem(x, refs)) <> twl.dl.ps(t, refs)

# W's parameters its body no longer reads once P's calls are w_rec
def twl.dl.of(m: Maybe<&2, TwlDef>, +p: List<&2, U32>) -> List<&2, Bool>:
  match m:
    case Some{TwlDef{n, ps, ret, body}}:
      twl.dl.ps(ps, T.tba.refs(twl.rep(body, p, T.BtVar{S.b("w_rec")}), Nil{}))
    case None{}:
      Nil{}

def twl.wnames.of(m: Maybe<&2, TwlDef>) -> List<&2, List<&2, U32>>:
  match m:
    case Some{TwlDef{n, ps, ret, body}}:
      twl.pnames(ps)
    case None{}:
      Nil{}

def twl.wnames(+its: List<&2, T.BItem>, +w: List<&2, U32>) -> List<&2, List<&2, U32>>:
  twl.wnames.of(twl.def.of(its, w))

def twl.apply(prs: List<&2, TwlPair>, its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match prs:
    case Nil{}:
      its
    case TwlPair{+w, +p, c, pps, pret} <> t:
      +its2 = its
      twl.apply(t, twl.items.one(its2, TwlPair{w, p, c, pps, pret}, twl.wnames(its2, w), twl.dl.of(twl.def.of(its2, w), p)))

# the module's items with their mutual with-functions' cycles broken
def twl.items(+its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  twl.apply(twl.pairs(its, its), its)
