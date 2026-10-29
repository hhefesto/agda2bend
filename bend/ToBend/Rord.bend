import Base
import ../Sys.bend as S
import ./Ast.bend as T
import ./Winl.bend as WL

# Recursion on a later parameter (2026-10-29) ---------------------------------
#
# Bend reads a self-call's arguments left to right: each passed unchanged
# until one shrinks.  `foldl c n (x ∷ xs) = foldl c (c n x) xs` changes n
# before xs shrinks, so the check refused foldl, and with it reverse and
# every user of reverse (PLFA: 49 dependents; iterate, scanl the same).
#
# A def whose body is a match and calls itself is split in two: f_dec, its
# parameters reordered (the templates first, as Copy puts them and a call's
# arguments already are; then the erased ones and the ones a later
# parameter's type reads; then the matched ones; then the rest), its
# self-calls f_dec's at the arguments reordered the same way; and
# f, with its own parameters, calling f_dec.  foldl_dec(~.., ~c, xs, n)
# recurses on xs first.  A def already in that order is left as it was.
#
# The split order too: Bend's match splits its columns left to right, Agda
# splits first where the first clause has a constructor (`m ∸ zero = m`
# splits n), so Bend's `anon(n, 0n)` (∸) was stuck where Agda's computes,
# and every lemma whose type needs it failed (Data.Nat.Properties'
# pred[n]≤n).  The matched parameters are ordered with the first clause's
# constructor columns first, and the match's columns with them.

def tro.len(ps: List<&2, T.BParam>) -> Nat:
  List.length(&2, T.BParam, ps)

# the parameter names a match scrutinizes
def tro.scr(xs: T.Bt) -> List<&2, List<&2, U32>>:
  match xs:
    case T.BtArgs{T.BtVar{x}, rest}:
      x <> tro.scr(rest)
    case T.BtArgs{h, rest}:
      tro.scr(rest)
    case _:
      Nil{}

# the names every match of the body scrutinizes (a nested match's too: a
# parameter matched in a case may be the one that shrinks)
def tro.body.scr(b: T.Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match b:
    case T.BtMatch{xs, cs}:
      List.append(&2, List<&2, U32>, tro.scr(xs), tro.body.scr(cs, acc))
    case T.BtCase{p, cb, rest}:
      tro.body.scr(cb, tro.body.scr(rest, acc))
    case T.BtRw{e, p, rb}:
      tro.body.scr(rb, acc)
    case T.BtLet{x, v, rb}:
      tro.body.scr(rb, acc)
    case _:
      acc

def tro.is.match(+b: T.Bt) -> Bool:
  match b:
    case T.BtMatch{xs, cs}:
      True{}
    case _:
      False{}

def tro.tyrefs(ps: List<&2, T.BParam>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      acc
    case T.BParam{m, x, ty} <> t:
      T.tba.refs(ty, tro.tyrefs(t, acc))

def tro.is.tpl(+m: T.BMode) -> Bool:
  match m:
    case T.BmTpl{}:
      True{}
    case _:
      False{}

def tro.is.erased(+m: T.BMode) -> Bool:
  match m:
    case T.BmErased{}:
      True{}
    case _:
      False{}

# the parameters as Copy orders them (ToBend/Copy.bend tcp.tpl.first: the
# templates first) and as a call's arguments already are
def tro.tpls(ps: List<&2, T.BParam>, +want: Bool) -> List<&2, T.BParam>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{+m, x, ty} <> t:
      +r = tro.tpls(t, want)
      Bool.pick(List<&2, T.BParam>, Bool.pick(Bool, want, tro.is.tpl(m), Bool.not(tro.is.tpl(m))), T.BParam{m, x, ty} <> r, r)

def tro.tplfirst(+ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  List.append(&2, T.BParam, tro.tpls(ps, True{}), tro.tpls(ps, False{}))

# each parameter's group: 0 a template, 1 erased or read by a later type,
# 2 matched, 3 the rest
def tro.groups(ps: List<&2, T.BParam>, +scr: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{+m, +x, ty} <> +t:
      +g = Bool.pick(Nat, tro.is.tpl(m), 0n, Bool.pick(Nat, Bool.or(tro.is.erased(m), WL.twl.mem(x, tro.tyrefs(t, Nil{}))), 1n, Bool.pick(Nat, WL.twl.mem(x, scr), 2n, 3n)))
      g <> tro.groups(t, scr)

# the positions in group g, in order
def tro.pos(gs: List<&2, Nat>, +g: Nat, +i: Nat) -> List<&2, Nat>:
  match gs:
    case Nil{}:
      Nil{}
    case h <> t:
      +r = tro.pos(t, g, 1n+i)
      Bool.pick(List<&2, Nat>, Nat.is_eq(h, g), i <> r, r)

def tro.perm(+gs: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, tro.pos(gs, 0n, 0n), List.append(&2, Nat, tro.pos(gs, 1n, 0n), List.append(&2, Nat, tro.pos(gs, 2n, 0n), tro.pos(gs, 3n, 0n))))

def tro.ident(p: List<&2, Nat>, +i: Nat) -> Bool:
  match p:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Nat.is_eq(h, i), tro.ident(t, 1n+i))

def tro.nth.p(i: Nat, ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match i ps:
    case 0n h <> t:
      [h]
    case 1n+k h <> t:
      tro.nth.p(k, t)
    case _ _:
      Nil{}

def tro.nth.a(i: Nat, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match i xs:
    case 0n h <> t:
      [h]
    case 1n+k h <> t:
      tro.nth.a(k, t)
    case _ _:
      Nil{}

def tro.ps(+ps: List<&2, T.BParam>, p: List<&2, Nat>) -> List<&2, T.BParam>:
  match p:
    case Nil{}:
      Nil{}
    case i <> t:
      List.append(&2, T.BParam, tro.nth.p(i, ps), tro.ps(ps, t))

def tro.as(+xs: List<&2, T.Bt>, p: List<&2, Nat>) -> List<&2, T.Bt>:
  match p:
    case Nil{}:
      Nil{}
    case i <> t:
      List.append(&2, T.Bt, tro.nth.a(i, xs), tro.as(xs, t))

def tro.list(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, rest}:
      h <> tro.list(rest)
    case _:
      Nil{}

# t with its self-calls of f (full ones: n arguments) calls of g at the
# arguments reordered by p
def tro.rec(t: T.Bt, +f: List<&2, U32>, +g: List<&2, U32>, +n: Nat, +p: List<&2, Nat>) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+h}, a}:
      +a2 = tro.rec(a, f, g, n, p)
      Bool.pick(T.Bt, Bool.and(S.eq(h, f), Nat.is_eq(T.tba.args.len(a2), n)), T.BtApp{T.BtVar{g}, T.tba.args(tro.as(tro.list(a2), p))}, T.BtApp{T.BtVar{h}, a2})
    case T.BtApp{h, a}:
      T.BtApp{tro.rec(h, f, g, n, p), tro.rec(a, f, g, n, p)}
    case T.BtRw{e, p2, b}:
      T.BtRw{tro.rec(e, f, g, n, p), tro.rec(p2, f, g, n, p), tro.rec(b, f, g, n, p)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, tro.rec(v, f, g, n, p), tro.rec(b, f, g, n, p)}
    case T.BtDead{a}:
      T.BtDead{tro.rec(a, f, g, n, p)}
    case T.BtTplArg{a}:
      T.BtTplArg{tro.rec(a, f, g, n, p)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, tro.rec(b, f, g, n, p)}
    case T.BtPi{m, x, d, a, b}:
      T.BtPi{m, x, d, tro.rec(a, f, g, n, p), tro.rec(b, f, g, n, p)}
    case T.BtCon{c, a}:
      T.BtCon{c, tro.rec(a, f, g, n, p)}
    case T.BtTyApp{c, a}:
      T.BtTyApp{c, tro.rec(a, f, g, n, p)}
    case T.BtEq{ty, a, b}:
      T.BtEq{tro.rec(ty, f, g, n, p), tro.rec(a, f, g, n, p), tro.rec(b, f, g, n, p)}
    case T.BtSucc{a}:
      T.BtSucc{tro.rec(a, f, g, n, p)}
    case T.BtAnn{a, ty}:
      T.BtAnn{tro.rec(a, f, g, n, p), tro.rec(ty, f, g, n, p)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, tro.rec(cs, f, g, n, p)}
    case T.BtExpr{e}:
      T.BtExpr{tro.rec(e, f, g, n, p)}
    case T.BtCase{p2, b, rest}:
      T.BtCase{p2, tro.rec(b, f, g, n, p), tro.rec(rest, f, g, n, p)}
    case T.BtArgs{a, rest}:
      T.BtArgs{tro.rec(a, f, g, n, p), tro.rec(rest, f, g, n, p)}
    case t:
      t

# a parameter passed on as it was declared
def tro.arg(p: T.BParam) -> T.Bt:
  match p:
    case T.BParam{T.BmErased{}, x, ty}:
      T.BtDead{T.BtVar{x}}
    case T.BParam{T.BmTpl{}, x, ty}:
      T.BtTplArg{T.BtVar{x}}
    case T.BParam{m, x, ty}:
      T.BtVar{x}

def tro.args(ps: List<&2, T.BParam>) -> List<&2, T.Bt>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      tro.arg(p) <> tro.args(t)

def tro.split(+n: List<&2, U32>, +ps: List<&2, T.BParam>, +ret: T.Bt, +body: T.Bt, +doc: List<&2, List<&2, U32>>, +p: List<&2, Nat>) -> List<&2, T.BItem>:
  +g = List.append(&2, U32, n, S.b("_dec"))
  +ps2 = tro.ps(tro.tplfirst(ps), p)
  +gd : List<&2, List<&2, U32>> = [List.append(&2, U32, S.b("agda2bend: "), List.append(&2, U32, n, S.b(" with its matched parameters first (Bend reads a self-call's arguments left to right)")))]
  [T.BiDef{g, ps2, ret, tro.rec(body, n, g, tro.len(ps), p), gd}, T.BiDef{n, ps, ret, T.BtExpr{T.BtApp{T.BtVar{g}, T.tba.args(tro.args(ps2))}}, doc}]

def tro.item.go(skip: Bool, +n: List<&2, U32>, +ps: List<&2, T.BParam>, +ret: T.Bt, +body: T.Bt, +body2: T.Bt, +doc: List<&2, List<&2, U32>>, +p: List<&2, Nat>) -> List<&2, T.BItem>:
  match skip:
    case True{}:
      [T.BiDef{n, ps, ret, body, doc}]
    case False{}:
      tro.split(n, ps, ret, body2, doc, p)

# whether some self-call changes a parameter before the first matched one
# (foldr passes c and n unchanged before xs shrinks: it stays whole)
def tro.same(a: T.Bt, +x: List<&2, U32>) -> Bool:
  match a:
    case T.BtVar{y}:
      S.eq(x, y)
    case T.BtTplArg{T.BtVar{y}}:
      S.eq(x, y)
    case T.BtDead{T.BtVar{y}}:
      S.eq(x, y)
    case _:
      False{}

def tro.prefix.same(a: T.Bt, ns: List<&2, List<&2, U32>>, +scr: List<&2, List<&2, U32>>) -> Bool:
  match a ns:
    case T.BtArgs{h, rest} +n <> nt:
      Bool.or(WL.twl.mem(n, scr), Bool.and(tro.same(h, n), tro.prefix.same(rest, nt, scr)))
    case _ _:
      True{}

def tro.changes(cs: List<&2, T.Bt>, +ns: List<&2, List<&2, U32>>, +scr: List<&2, List<&2, U32>>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      Bool.or(Bool.not(tro.prefix.same(c, ns, scr)), tro.changes(t, ns, scr))

# the top match's scrutinee names, and its first case's patterns
def tro.top.scr(+b: T.Bt) -> List<&2, List<&2, U32>>:
  match b:
    case T.BtMatch{xs, cs}:
      tro.scr(xs)
    case _:
      Nil{}

def tro.first.pats(+b: T.Bt) -> List<&2, T.Bt>:
  match b:
    case T.BtMatch{xs, T.BtCase{p, cb, rest}}:
      tro.list(p)
    case _:
      Nil{}

def tro.is.vpat(p: T.Bt) -> Bool:
  match p:
    case T.BtPv{m, x}:
      True{}
    case T.BtWild{}:
      True{}
    case _:
      False{}

# the scrutinees whose first-case pattern is a constructor (Agda splits
# there first)
def tro.lead(ps: List<&2, T.Bt>, ns: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps ns:
    case p <> pt n <> nt:
      +r = tro.lead(pt, nt)
      Bool.pick(List<&2, List<&2, U32>>, tro.is.vpat(p), r, n <> r)
    case _ _:
      Nil{}

def tro.idx(ns: List<&2, List<&2, U32>>, +x: List<&2, U32>, +i: Nat) -> Maybe<&2, Nat>:
  match ns:
    case Nil{}:
      None{}
    case h <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(h, x), Some{i}, tro.idx(t, x, 1n+i))

def tro.nat.mem(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), tro.nat.mem(x, t))

def tro.g.at(i: Nat, gs: List<&2, Nat>) -> Nat:
  match i gs:
    case 0n h <> t:
      h
    case 1n+k h <> t:
      tro.g.at(k, t)
    case _ _:
      9n

# group 2's positions, in the order of the names l (each once), then the
# rest of group 2 in parameter order
def tro.g2.of(m: Maybe<&2, Nat>, +gs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Some{+i}:
      +acc2 = acc
      Bool.pick(List<&2, Nat>, Bool.and(Nat.is_eq(tro.g.at(i, gs), 2n), Bool.not(tro.nat.mem(i, acc2))), List.append(&2, Nat, acc2, [i]), acc2)
    case None{}:
      acc

def tro.g2(l: List<&2, List<&2, U32>>, +ns: List<&2, List<&2, U32>>, +gs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      acc
    case +x <> t:
      tro.g2(t, ns, gs, tro.g2.of(tro.idx(ns, x, 0n), gs, acc))

def tro.g2.rest(gs: List<&2, Nat>, +have: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match gs:
    case Nil{}:
      Nil{}
    case h <> t:
      +r = tro.g2.rest(t, have, 1n+i)
      Bool.pick(List<&2, Nat>, Bool.and(Nat.is_eq(h, 2n), Bool.not(tro.nat.mem(i, have))), i <> r, r)

def tro.perm2(+gs: List<&2, Nat>, +ns: List<&2, List<&2, U32>>, +l: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  +g2 = tro.g2(l, ns, gs, Nil{})
  List.append(&2, Nat, tro.pos(gs, 0n, 0n), List.append(&2, Nat, tro.pos(gs, 1n, 0n), List.append(&2, Nat, List.append(&2, Nat, g2, tro.g2.rest(gs, g2, 0n)), tro.pos(gs, 3n, 0n))))

# the names of ns that are in keep, in ns's order
def tro.only(ns: List<&2, List<&2, U32>>, +keep: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case +h <> t:
      +r = tro.only(t, keep)
      Bool.pick(List<&2, List<&2, U32>>, WL.twl.mem(h, keep), h <> r, r)

def tro.names.eq(a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case x <> at y <> bt:
      Bool.and(S.eq(x, y), tro.names.eq(at, bt))
    case _ _:
      False{}

def tro.head.in(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case h <> t:
      WL.twl.mem(h, ys)
    case Nil{}:
      False{}

# the column permutation: for each new column, its old index
def tro.cperm.one(m: Maybe<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Some{i}:
      i <> rest
    case None{}:
      rest

def tro.cperm(nw: List<&2, List<&2, U32>>, +old: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  match nw:
    case Nil{}:
      Nil{}
    case +x <> t:
      tro.cperm.one(tro.idx(old, x, 0n), tro.cperm(t, old))

def tro.cases(cs: T.Bt, +cp: List<&2, Nat>) -> T.Bt:
  match cs:
    case T.BtCase{p, b, rest}:
      T.BtCase{T.tba.args(tro.as(tro.list(p), cp)), b, tro.cases(rest, cp)}
    case cs:
      cs

def tro.cols(b: T.Bt, +cp: List<&2, Nat>) -> T.Bt:
  match b:
    case T.BtMatch{xs, cs}:
      T.BtMatch{T.tba.args(tro.as(tro.list(xs), cp)), tro.cases(cs, cp)}
    case b:
      b

def tro.item(it: T.BItem) -> List<&2, T.BItem>:
  match it:
    case T.BiDef{+n, +ps, +ret, +body, +doc}:
      +ps0 = tro.tplfirst(ps)
      +scr = tro.body.scr(body, Nil{})
      +top = tro.top.scr(body)
      +lead = tro.lead(tro.first.pats(body), top)
      +p = tro.perm2(tro.groups(ps0, scr), WL.twl.pnames(ps0), List.append(&2, List<&2, U32>, lead, scr))
      +top2 = tro.only(WL.twl.pnames(tro.ps(ps0, p)), top)
      +moved = Bool.and(Bool.not(tro.names.eq(top2, top)), Bool.and(tro.head.in(top2, lead), Bool.not(tro.head.in(top, lead))))
      +need = Bool.or(tro.changes(WL.twl.calls(body, n, Nil{}), WL.twl.pnames(ps0), scr), moved)
      tro.item.go(Bool.or(Bool.or(tro.ident(p, 0n), Bool.not(tro.is.match(body))), Bool.not(need)), n, ps, ret, body, tro.cols(body, tro.cperm(top2, top)), doc, p)
    case it:
      [it]

# the module's items, each self-recursive def on a later parameter split
def tro.items(its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case it <> t:
      List.append(&2, T.BItem, tro.item(it), tro.items(t))
