import Base
import ../Sys.bend as S
import ../ToBend/Names.bend as N
import ../ToBend/Ast.bend as T
import ./Ast.bend as A

# Cata: the translation of parsed Agda (Agda2Bend/Ast.bend) into the Bend
# syntax tree (ToBend/Ast.bend).  It is a fold: each form's Bend is built
# from its parts' Bend and the form's own data (a name's entry in the
# symbol table, a binder's INFO), with the context of the binders in scope
# passed down.  `act.t(fuel, a, ctx, env)` is the fold over terms; ctx maps
# each de Bruijn index to the Bend term it stands for (index 0 first).
#
# What it maps (the plan of 2026-10-19):
# - Set ℓ, Setω and every sort to Type; Level binders, arguments and
#   level-valued definitions are dropped (Bend has one universe);
# - a Pi to @x:A -> B, erased (@-x) when the binder is hidden, instance,
#   irrelevant or @0, or a type, a type family (a Pi into a sort), or a
#   parameter of a definition whose value is a type;
# - a definition's application to a call grouped by its arity (the
#   parameters its clauses match), dropped arguments left out: f(a, b)(c);
# - constructors to C{..} (Nat's zero and suc to 0n and 1n+n, Bool's to
#   True{} and False{}, ≡'s refl to {==}), ≡ itself to {a == b : A};
# - a module application's copy (agda-export writes only its case tree,
#   FORMAT.md "Copies") to its leaf with the arguments substituted, so the
#   output calls the generic original as agda-categories' source does;
# - clauses to one match on the parameters they split, in parameter order
#   (Bend refuses a match on an earlier parameter inside one on a later),
#   patterns nested as Agda wrote them; copattern clauses to the record's
#   constructor; a record field's projection to a match on the record.
# What it cannot map it writes as a BtTodo with the reason, which fails
# that def at the gate and names the cause in the ledger.  Every def is
# prefixed `act.` (the substitution `asb.`).

# The switch for quantities: OFF since 2026-10-20 07:20.  Mapping every level
# to a quantity was unsound: a type at a variable level may be a function
# type, which Bend makes Type, so `Setoids c ℓ` cannot have homs of kind
# Kind(qc <&> qℓ) (probe: 146 of 2226 items checked).  A quantity argument
# has to be the kind of the type it governs, which needs kind inference;
# until then levels are dropped as before.
def act.quant.on() -> Bool:
  True{}

# Substitution -----------------------------------------------------------------
#
# A copy's leaf is a term in the scope of its own variables; inlining it
# substitutes the use site's arguments for them, shifting each argument's
# free variables over the binders it is put under.  Sorts and levels are
# walked too: with levels as quantities (2026-10-20) a level variable left
# unshifted named the wrong binder (`Rel Carrier ℓ` opened to `Carrier ->
# Carrier -> Kind(Carrier)`).

# the elimination spine es, then more
def asb.elims.cat(es: A.Ag, more: A.Ag) -> A.Ag:
  match es:
    case A.AgEApp{i, t, rest}:
      A.AgEApp{i, t, asb.elims.cat(rest, more)}
    case A.AgEProj{q, rest}:
      A.AgEProj{q, asb.elims.cat(rest, more)}
    case A.AgERaw{x, rest}:
      A.AgERaw{x, asb.elims.cat(rest, more)}
    case _:
      more

def asb.push.head(t: A.Ag, es: A.Ag) -> A.Ag:
  match t:
    case A.AgVar{i, x, es0}:
      A.AgVar{i, x, asb.elims.cat(es0, es)}
    case A.AgDef{q, es0}:
      A.AgDef{q, asb.elims.cat(es0, es)}
    case A.AgCon{q, o, es0}:
      A.AgCon{q, o, asb.elims.cat(es0, es)}
    case A.AgMeta{es0}:
      A.AgMeta{asb.elims.cat(es0, es)}
    case t:
      t

# t applied to the eliminations es: a head takes them; a lambda becomes a
# redex (AgBeta) the copy inlining reduces; anything else is left as it is
def asb.push(t: A.Ag, es: A.Ag) -> A.Ag:
  match t es:
    case t A.AgENil{}:
      t
    case A.AgLam{i, x, d, b} es:
      A.AgBeta{A.AgLam{i, x, d, b}, es}
    case A.AgBeta{f, es0} es:
      A.AgBeta{f, asb.elims.cat(es0, es)}
    case t es:
      asb.push.head(t, es)

# the binder count under a lambda's or a Pi's body: one more when it
# binds (abs), the same when it does not (noabs: FORMAT.md, "binds none")
def asb.under(dep: Bool, +c: Nat) -> Nat:
  match dep:
    case True{}:
      1n+c
    case False{}:
      c

# variables at or above c shifted up by d
def asb.shift(t: A.Ag, +d: Nat, +c: Nat) -> A.Ag:
  match t:
    case A.AgSort{s}:
      A.AgSort{asb.shift(s, d, c)}
    case A.AgSSet{l}:
      A.AgSSet{asb.shift(l, d, c)}
    case A.AgSProp{l}:
      A.AgSProp{asb.shift(l, d, c)}
    case A.AgLevel{l}:
      A.AgLevel{asb.shift(l, d, c)}
    case A.AgLMax{n, ps}:
      A.AgLMax{n, asb.shift(ps, d, c)}
    case A.AgLPlus{k, x, rest}:
      A.AgLPlus{k, asb.shift(x, d, c), asb.shift(rest, d, c)}
    case A.AgBeta{f, es}:
      A.AgBeta{asb.shift(f, d, c), asb.shift(es, d, c)}
    case A.AgVar{+i, x, es}:
      A.AgVar{Bool.pick(Nat, Nat.is_lt(i, c), i, Nat.add(i, d)), x, asb.shift(es, d, c)}
    case A.AgLam{i, x, +dep, b}:
      A.AgLam{i, x, dep, asb.shift(b, d, asb.under(dep, c))}
    case A.AgDef{q, es}:
      A.AgDef{q, asb.shift(es, d, c)}
    case A.AgCon{q, o, es}:
      A.AgCon{q, o, asb.shift(es, d, c)}
    case A.AgPi{i, x, a, +dep, b}:
      A.AgPi{i, x, asb.shift(a, d, c), dep, asb.shift(b, d, asb.under(dep, c))}
    case A.AgEl{s, a}:
      A.AgEl{asb.shift(s, d, c), asb.shift(a, d, c)}
    case A.AgDontCare{a}:
      A.AgDontCare{asb.shift(a, d, c)}
    case A.AgMeta{es}:
      A.AgMeta{asb.shift(es, d, c)}
    case A.AgEApp{i, a, rest}:
      A.AgEApp{i, asb.shift(a, d, c), asb.shift(rest, d, c)}
    case A.AgEProj{q, rest}:
      A.AgEProj{q, asb.shift(rest, d, c)}
    case A.AgERaw{x, rest}:
      A.AgERaw{x, asb.shift(rest, d, c)}
    case t:
      t

# the n-th of xs (a variable past the end is left free)
def asb.nth(n: Nat, xs: List<&2, A.Ag>) -> Maybe<&2, A.Ag>:
  match n xs:
    case 0n h <> t:
      Some{h}
    case 1n+p h <> t:
      asb.nth(p, t)
    case _ Nil{}:
      None{}

def asb.var.of(m: Maybe<&2, A.Ag>, +depth: Nat, +i: Nat, +n: Nat, x: List<&2, U32>, es: A.Ag) -> A.Ag:
  match m:
    case Some{v}:
      asb.push(asb.shift(v, depth, 0n), es)
    case None{}:
      A.AgVar{Nat.sub(i, n), x, es}

# a variable of the substituted term: bound inside it (below depth), one
# of the n substituted, or a free one past them (renumbered)
def asb.subst.var(bound: Bool, +i: Nat, +depth: Nat, +vs: List<&2, A.Ag>, +n: Nat, x: List<&2, U32>, es: A.Ag) -> A.Ag:
  match bound:
    case True{}:
      A.AgVar{i, x, es}
    case False{}:
      asb.var.of(asb.nth(Nat.sub(i, depth), vs), depth, i, n, x, es)

# t (in the scope of n variables, under depth binders of its own) with
# variable depth+j replaced by vs[j]: vs lists the values from index 0 (the
# last variable) up
def asb.subst(t: A.Ag, +depth: Nat, +vs: List<&2, A.Ag>, +n: Nat) -> A.Ag:
  match t:
    case A.AgSort{s}:
      A.AgSort{asb.subst(s, depth, vs, n)}
    case A.AgSSet{l}:
      A.AgSSet{asb.subst(l, depth, vs, n)}
    case A.AgSProp{l}:
      A.AgSProp{asb.subst(l, depth, vs, n)}
    case A.AgLevel{l}:
      A.AgLevel{asb.subst(l, depth, vs, n)}
    case A.AgLMax{n2, ps}:
      A.AgLMax{n2, asb.subst(ps, depth, vs, n)}
    case A.AgLPlus{k, x, rest}:
      A.AgLPlus{k, asb.subst(x, depth, vs, n), asb.subst(rest, depth, vs, n)}
    case A.AgBeta{f, es}:
      A.AgBeta{asb.subst(f, depth, vs, n), asb.subst(es, depth, vs, n)}
    case A.AgVar{+i, x, es}:
      asb.subst.var(Nat.is_lt(i, depth), i, depth, vs, n, x, asb.subst(es, depth, vs, n))
    case A.AgLam{i, x, +dep, b}:
      A.AgLam{i, x, dep, asb.subst(b, asb.under(dep, depth), vs, n)}
    case A.AgDef{q, es}:
      A.AgDef{q, asb.subst(es, depth, vs, n)}
    case A.AgCon{q, o, es}:
      A.AgCon{q, o, asb.subst(es, depth, vs, n)}
    case A.AgPi{i, x, a, +dep, b}:
      A.AgPi{i, x, asb.subst(a, depth, vs, n), dep, asb.subst(b, asb.under(dep, depth), vs, n)}
    case A.AgEl{s, a}:
      A.AgEl{asb.subst(s, depth, vs, n), asb.subst(a, depth, vs, n)}
    case A.AgDontCare{a}:
      A.AgDontCare{asb.subst(a, depth, vs, n)}
    case A.AgMeta{es}:
      A.AgMeta{asb.subst(es, depth, vs, n)}
    case A.AgEApp{i, a, rest}:
      A.AgEApp{i, asb.subst(a, depth, vs, n), asb.subst(rest, depth, vs, n)}
    case A.AgEProj{q, rest}:
      A.AgEProj{q, asb.subst(rest, depth, vs, n)}
    case A.AgERaw{x, rest}:
      A.AgERaw{x, asb.subst(rest, depth, vs, n)}
    case t:
      t

# Symbols ----------------------------------------------------------------------

# A parameter's mode in Bend: dropped (a Level), erased, live, copied (+)
# or a template (~); the last two, and live for a hidden parameter used as
# a value, come from the quantity pass (ToBend/Copy.bend).
type ActM is Data:
  AmDrop{}
  AmErased{}
  AmLive{}
  AmCopy{}
  AmTpl{}

# What a name is in Bend when it is not translated as itself: Nat, Bool,
# Unit, ≡ and their constructors are Base's.  Levels are quantities
# (2026-10-20, so a category's homs may be Data, as Product needs): Level is
# Quant, lzero and lsuc ℓ are &1 (Type), ℓ ⊔ ℓ' the smaller of the two, and
# another level-valued definition (AbLevel) &1.
type ActB is Data:
  AbNone{}
  AbQuant{}
  AbQone{}
  AbQmin{}
  AbNat{}
  AbZero{}
  AbSuc{}
  AbBool{}
  AbTrue{}
  AbFalse{}
  AbEq{}
  AbRefl{}
  AbLevel{}
  AbUnit{}
  AbTt{}
  # Agda.Builtin.String's postulated String (BUILTIN STRING): Bend's String
  # (2026-10-29: PLFA's `Id = String`, 95 dependents)
  AbString{}

# a copy's case-tree leaf: its variable count and term
type ActCopy is Data:
  ActCopy{n: Nat, body: A.Ag}

# A name's entry: the module it lives in and its Bend name there, its kind,
# its parameters' modes (every Pi of its type, in order), its arity (the
# parameters its Bend def or type takes; a call passes the rest in a second
# application), its builtin role, for a record its fields' keys in order
# (for a data type its constructors'), the Bend name of a record's
# constructor, and a copy's leaf.
type ActSym is Data:
  ActSym{mod: List<&2, U32>, name: List<&2, U32>, kind: A.AgKw, modes: List<&2, ActM>, arity: Nat, b: ActB, fields: List<&2, String>, ctor: List<&2, U32>, copy: Maybe<&2, ActCopy>}

# What a translation sees: the module being written, the symbol table (by
# NameId key), each module's import alias, and the leaves of the type-valued
# definitions that unfold (by key: a header unfolds one to reach the Pis
# its clauses take, e.g. `refl : Reflexive _≈_` with a clause on `{x}`).
type ActEnv is Data:
  ActEnv{mod: List<&2, U32>, tab: Map<&2, ActSym>, al: Map<&2, List<&2, U32>>, unf: Map<&2, ActCopy>}

# a name's key in the table: its NameId
def act.key(q: A.AgQ) -> String:
  match q:
    case A.AgQ{s, w, k}:
      S.str(w) ++ ":" ++ S.str(k)

def act.sym0() -> ActSym:
  ActSym{Nil{}, Nil{}, A.AkWord{}, Nil{}, 0n, AbNone{}, Nil{}, Nil{}, None{}}

def act.qs.of(q: A.AgQ) -> List<&2, U32>:
  match q:
    case A.AgQ{s, w, k}:
      s

# the entry of a name the table does not have: of kind AkWord, its module
# `?` and its name Agda's, so the reason of the gap it leaves names it
def act.sym.none(q: A.AgQ) -> ActSym:
  ActSym{S.b("?"), act.qs.of(q), A.AkWord{}, Nil{}, 0n, AbNone{}, Nil{}, Nil{}, None{}}

def act.sym.got(r: Map<&2, ActSym> & ActSym) -> ActSym:
  (m, s) = r
  s

# the entry of q (an empty one, of kind AkWord, when the table has none)
def act.sym(+env: ActEnv, +q: A.AgQ) -> ActSym:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.sym.got(Map.get(ActSym, act.sym.none(q), tab, act.key(q)))

def act.alias.got(r: Map<&2, List<&2, U32>> & List<&2, U32>) -> List<&2, U32>:
  (m, a) = r
  a

def act.is.here(+env: ActEnv, +m: List<&2, U32>) -> Bool:
  match env:
    case ActEnv{mod, tab, al, unf}:
      S.eq(mod, m)

def act.alias(+env: ActEnv, +m: List<&2, U32>) -> List<&2, U32>:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.alias.got(Map.get(List<&2, U32>, m, al, S.str(m)))

def act.ref.of(here: Bool, +env: ActEnv, +m: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  match here:
    case True{}:
      n
    case False{}:
      List.append(&2, U32, act.alias(env, m), 46 <> n)

# how the module being written names a symbol: its own names as they are,
# another module's through that module's alias
def act.ref(+env: ActEnv, s: ActSym) -> List<&2, U32>:
  match s:
    case ActSym{+m, +n, k, ms, ar, b, fs, c, cp}:
      act.ref.of(act.is.here(env, m), env, m, n)

def act.ctor.ref(+env: ActEnv, s: ActSym) -> List<&2, U32>:
  match s:
    case ActSym{+m, n, k, ms, ar, b, fs, +c, cp}:
      act.ref.of(act.is.here(env, m), env, m, c)

# Modes ----------------------------------------------------------------------

def act.q.is(q: A.AgQ, +s: String) -> Bool:
  match q:
    case A.AgQ{qs, w, k}:
      S.eq(qs, S.b(s))

# a TYPE whose values are Levels: its sort is the level universe, or it is
# Agda.Primitive.Level
def act.ty.level(t: A.Ag) -> Bool:
  match t:
    case A.AgEl{A.AgSUniv{A.AkLeveluniv{}}, x}:
      True{}
    case A.AgEl{s, A.AgDef{q, es}}:
      act.q.is(q, "Agda.Primitive.Level")
    case _:
      False{}

# a TYPE that ends, after its Pis, in a sort (Set ℓ itself, or a type family)
def act.ends.sort(t: A.Ag) -> Bool:
  match t:
    case A.AgEl{s, x}:
      act.ends.sort(x)
    case A.AgPi{i, x, a, d, b}:
      act.ends.sort(b)
    case A.AgSort{s}:
      True{}
    case _:
      False{}

# a TYPE that ends, after its Pis, in Level (a level-valued definition)
def act.ends.level(t: A.Ag) -> Bool:
  match t:
    case A.AgEl{A.AgSUniv{A.AkLeveluniv{}}, x}:
      True{}
    case A.AgEl{s, A.AgDef{q, es}}:
      act.q.is(q, "Agda.Primitive.Level")
    case A.AgEl{s, x}:
      act.ends.level(x)
    case A.AgPi{i, x, a, d, b}:
      act.ends.level(b)
    case _:
      False{}

# hidden, instance, irrelevant or @0
def act.info.erased(i: A.AgI) -> Bool:
  match i:
    case A.AgI{+h, r, m}:
      Bool.or(Bool.or(A.aas.kw.eq(h, A.AkHidden{}), A.aas.kw.eq(h, A.AkInstance{})), Bool.or(A.aas.kw.eq(r, A.AkIrrelevant{}), A.aas.kw.eq(m, A.AkQ0{})))

# irrelevant or @0: erased wherever it is; a hidden or instance binder of
# a Pi written as a term (a record's field, Reflexive's body, a function
# value's type) is live (2026-10-29): Agda's implicit arguments are
# relevant, and a def that matches on one (≤-refl {suc n}, ≤-reflexive)
# takes it live, so a field erasing it could hold no such def (≤-isPreorder:
# "expected -eta1 observed eta1", 79 dependents in the stdlib cone).  A
# def's own hidden parameters stay erased until the quantity pass sees a
# live use.
def act.info.erased.v(i: A.AgI) -> Bool:
  match i:
    case A.AgI{h, +r, +m}:
      Bool.or(A.aas.kw.eq(r, A.AkIrrelevant{}), A.aas.kw.eq(m, A.AkQ0{}))

def act.mode.of(lv: Bool, er: Bool) -> ActM:
  match lv er:
    case True{} _:
      Bool.pick(ActM, act.quant.on(), AmErased{}, AmDrop{})
    case False{} True{}:
      AmErased{}
    case False{} False{}:
      AmLive{}

def act.info.hid(i: A.AgI) -> Bool:
  match i:
    case A.AgI{+h, r, m}:
      Bool.or(A.aas.kw.eq(h, A.AkHidden{}), A.aas.kw.eq(h, A.AkInstance{}))

# a Pi-as-a-term binder's mode (act.mode, hidden live: act.info.erased.v);
# a type family's (`C : {x : A} → B x → Set c`, _∘_'s) keeps act.mode, its
# binders being read by types only (live, Qfix lost _∘_'s quantities).
# A hidden binder over an opaque type stays live (2026-10-29): the Pi is
# Congruent's or _⇒_'s body inlined at Setoid's Carrier or a module's
# opaque A, and Bend, opening Congruent or _⇒_ itself, gives the binder
# the definition's own mode, live (Function.Bundles' Func.isCongruent:
# "expected @x observed @-x"; Consequences' total⇒refl, wlog)
def act.mode.v(+i: A.AgI, +a: A.Ag, tylevel: Bool) -> ActM:
  act.mode.of(act.ty.level(a), Bool.or(Bool.or(act.info.erased.v(i), act.ends.sort(a)), Bool.and(tylevel, Bool.not(act.info.hid(i)))))

# a Pi binder's mode: a Level is dropped; it is erased when hidden,
# instance, irrelevant or @0, when it is a type or a type family, or when
# the whole definition is type-valued (tylevel)
def act.mode(i: A.AgI, +a: A.Ag, tylevel: Bool) -> ActM:
  act.mode.of(act.ty.level(a), Bool.or(Bool.or(act.info.erased(i), act.ends.sort(a)), tylevel))

# the modes of every Pi of a TYPE
def act.modes(t: A.Ag, +tylevel: Bool) -> List<&2, ActM>:
  match t:
    case A.AgEl{s, x}:
      act.modes(x, tylevel)
    case A.AgPi{i, x, a, d, b}:
      act.mode(i, a, tylevel) <> act.modes(b, tylevel)
    case A.AgStored{x}:
      act.modes(x, tylevel)
    case _:
      Nil{}

def act.bi(+s: List<&2, U32>, +name: String, b: ActB, other: ActB) -> ActB:
  Bool.pick(ActB, S.eq(s, S.b(name)), b, other)

# agda-unimath's BUILTIN bindings (NATURAL, BOOL, TRUE, FALSE, EQUALITY,
# UNIT; the same shapes as Agda.Builtin's): its identity type Id is the
# equality whose refl a match rewrites by (foundation-core.identity-types'
# ind-Id and _∙_ dropped without it, and 33 of its 39 items after them);
# its _＝_ (x ＝ y = Id x y, the same arguments) is the one the library
# writes, and a match on refl at type x ＝ y rewrites only when that is
# the equality too
def act.builtin.um1(+s: List<&2, U32>) -> ActB:
  act.bi(s, "elementary-number-theory.natural-numbers.ℕ", AbNat{}, act.bi(s, "elementary-number-theory.natural-numbers.ℕ.zero-ℕ", AbZero{},
  act.bi(s, "elementary-number-theory.natural-numbers.ℕ.succ-ℕ", AbSuc{},
  act.bi(s, "foundation-core.booleans.bool", AbBool{}, act.bi(s, "foundation-core.booleans.bool.true", AbTrue{}, act.bi(s, "foundation-core.booleans.bool.false", AbFalse{},
  act.bi(s, "foundation-core.identity-types._.Id", AbEq{}, act.bi(s, "foundation-core.identity-types._.Id.refl", AbRefl{},
  act.bi(s, "foundation.unit-type.unit", AbUnit{}, act.bi(s, "foundation.unit-type.star", AbTt{}, AbNone{}))))))))))

def act.builtin.um(+s: List<&2, U32>) -> ActB:
  act.bi(s, "foundation-core.identity-types._._＝_", AbEq{}, act.builtin.um1(s))

# the builtin role of a name, by its printed name
def act.builtin(+s: List<&2, U32>) -> ActB:
  act.bi(s, "Agda.Builtin.Nat.Nat", AbNat{}, act.bi(s, "Agda.Builtin.Nat.Nat.zero", AbZero{}, act.bi(s, "Agda.Builtin.Nat.Nat.suc", AbSuc{},
  act.bi(s, "Agda.Builtin.Bool.Bool", AbBool{}, act.bi(s, "Agda.Builtin.Bool.Bool.true", AbTrue{}, act.bi(s, "Agda.Builtin.Bool.Bool.false", AbFalse{},
  act.bi(s, "Agda.Builtin.Equality._≡_", AbEq{}, act.bi(s, "Agda.Builtin.Equality._≡_.refl", AbRefl{},
  act.bi(s, "Agda.Builtin.Unit.⊤", AbUnit{}, act.bi(s, "Agda.Builtin.Unit.tt", AbTt{}, act.bi(s, "Agda.Builtin.String.String", AbString{},
  act.bi(s, "Agda.Primitive.Level", AbQuant{}, act.bi(s, "Agda.Primitive.lzero", AbQone{}, act.bi(s, "Agda.Primitive.lsuc", AbQone{},
  act.bi(s, "Agda.Primitive._⊔_", AbQmin{}, act.builtin.um(s))))))))))))))))

# Terms ------------------------------------------------------------------------

def act.level() -> T.Bt:
  T.BtTodo{S.b("level")}

def act.todo(s: String) -> T.Bt:
  T.BtTodo{S.b(s)}

# the term a de Bruijn index stands for
def act.ctx.at(i: Nat, ctx: List<&2, T.Bt>) -> T.Bt:
  match i ctx:
    case 0n h <> t:
      h
    case 1n+p h <> t:
      act.ctx.at(p, t)
    case _ Nil{}:
      act.todo("a variable outside its scope")

# Quantities ------------------------------------------------------------------
#
# A level is a quantity in Bend: a type of sort Set ℓ has kind Kind(qℓ), so
# a type whose level is a variable may be Data where its user needs copies
# (Product's morphism pairs), and `Set ℓ` built from variables only is
# `Kind(…)`.  A constant level or a successor is a universe of sets: Type
# (&1).  The smaller of two quantities is `a <&> b`; &1 absorbs the rest.

def act.q1() -> T.Bt:
  T.BtVar{S.b("&1")}

def act.is.q1(t: T.Bt) -> Bool:
  match t:
    case T.BtVar{n}:
      S.eq(n, S.b("&1"))
    case _:
      False{}

# (quantity terms are names, so the minimum is written as one: "(a <&> b)")
def act.q.name(t: T.Bt) -> List<&2, U32>:
  match t:
    case T.BtVar{n}:
      n
    case _:
      S.b("&1")

def act.q2() -> T.Bt:
  T.BtVar{S.b("&2")}

def act.is.q2(t: T.Bt) -> Bool:
  match t:
    case T.BtVar{n}:
      S.eq(n, S.b("&2"))
    case _:
      False{}

# (&2 is the unit of the minimum, &1 absorbs it)
def act.qmin(+a: T.Bt, +b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, act.is.q2(a), b, Bool.pick(T.Bt, act.is.q2(b), a, Bool.pick(T.Bt, Bool.or(act.is.q1(a), act.is.q1(b)), act.q1(), T.BtVar{List.append(&2, U32, 40 <> act.q.name(a), List.append(&2, U32, S.b(" <&> "), List.append(&2, U32, act.q.name(b), [41])))})))

# ⊔ applied: its two (kept) arguments
def act.qmin.args(args: T.Bt) -> T.Bt:
  match args:
    case T.BtArgs{T.BtDead{a}, T.BtArgs{T.BtDead{b}, T.BtANil{}}}:
      act.qmin(a, b)
    case T.BtArgs{a, T.BtArgs{b, T.BtANil{}}}:
      act.qmin(a, b)
    case _:
      act.q1()

def act.qt.ismin(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, k, ms, ar, AbQmin{}, fs, c, cp}:
      True{}
    case _:
      False{}

# a level term as a quantity
def act.qt(t: A.Ag, +ctx: List<&2, T.Bt>, +env: ActEnv) -> T.Bt:
  match t:
    case A.AgLevel{l}:
      Bool.pick(T.Bt, act.quant.on(), act.qt(l, ctx, env), act.level())
    case A.AgLMax{0n, ps}:
      act.qt(ps, ctx, env)
    case A.AgLMax{1n+n, ps}:
      act.q1()
    case A.AgLPlus{0n, x, A.AgLEnd{}}:
      act.qt(x, ctx, env)
    case A.AgLPlus{0n, x, rest}:
      act.qmin(act.qt(x, ctx, env), act.qt(rest, ctx, env))
    case A.AgLPlus{1n+k, x, rest}:
      act.q1()
    case A.AgVar{+i, x, es}:
      act.ctx.at(i, ctx)
    case A.AgDef{+q, A.AgEApp{i, a, A.AgEApp{i2, b, A.AgENil{}}}}:
      Bool.pick(T.Bt, act.qt.ismin(act.sym(env, q)), act.qmin(act.qt(a, ctx, env), act.qt(b, ctx, env)), act.q1())
    case A.AgDefX{+q, A.AgEApp{i, a, A.AgEApp{i2, b, A.AgENil{}}}}:
      Bool.pick(T.Bt, act.qt.ismin(act.sym(env, q)), act.qmin(act.qt(a, ctx, env), act.qt(b, ctx, env)), act.q1())
    case _:
      act.q1()

# a sort: Set ℓ is Kind(qℓ), unless qℓ is &1 (Type); any other sort is Type
def act.kind.of(+q: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, act.is.q1(q), T.BtType{}, T.BtApp{T.BtVar{S.b("Kind")}, T.BtArgs{q, T.BtANil{}}})

def act.sort(s: A.Ag, +ctx: List<&2, T.Bt>, +env: ActEnv) -> T.Bt:
  match s:
    case A.AgSSet{l}:
      act.kind.of(act.qt(l, ctx, env))
    case _:
      T.BtType{}

# the context entry of a Level binder
def act.is.marker(t: T.Bt) -> Bool:
  match t:
    case T.BtTodo{why}:
      S.eq(why, S.b("level"))
    case _:
      False{}

def act.sym.level(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, k, ms, ar, AbLevel{}, fs, c, cp}:
      True{}
    case _:
      False{}

# is an argument a level expression: a level, a Level-valued definition
# applied, or a level variable (its context entry is the level marker)
def act.is.level(a: A.Ag, +ctx: List<&2, T.Bt>, +env: ActEnv) -> Bool:
  match a:
    case A.AgLevel{l}:
      True{}
    case A.AgDef{q, es}:
      act.sym.level(act.sym(env, q))
    case A.AgDefX{q, es}:
      act.sym.level(act.sym(env, q))
    case A.AgVar{i, x, es}:
      act.is.marker(act.ctx.at(i, ctx))
    case _:
      False{}

# an argument as the fold gives it to an application: a level argument is
# the level marker (an application to a variable drops it; one to a
# definition drops it by the definition's modes)
def act.arg(lv: Bool, t: T.Bt) -> T.Bt:
  match lv:
    case True{}:
      act.level()
    case False{}:
      t

# the names of the binders in scope
def act.names(ctx: List<&2, T.Bt>) -> List<&2, List<&2, U32>>:
  match ctx:
    case Nil{}:
      Nil{}
    case T.BtVar{x} <> t:
      x <> act.names(t)
    case h <> t:
      act.names(t)

def act.used(+x: List<&2, U32>, ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(S.eq(h, x), act.used(x, t))

def act.hint.of(+b: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, S.eq(b, S.b("anon")), S.b("x"), b)

def act.hint(+x: List<&2, U32>) -> List<&2, U32>:
  act.hint.of(S.b(N.tnm.part(S.str(x))))

def act.nth.name(+b: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  List.append(&2, U32, b, 95 <> S.b(Nat.show(n)))

# b_n, or b_(n+1) and so on while that one is taken too (clash: b_n is)
def act.fresh.try(fuel: Nat, clash: Bool, +b: List<&2, U32>, +ns: List<&2, List<&2, U32>>, +n: Nat) -> List<&2, U32>:
  match fuel clash:
    case 1n+f True{}:
      act.fresh.try(f, act.used(act.nth.name(b, 1n+n), ns), b, ns, 1n+n)
    case _ _:
      act.nth.name(b, n)

def act.fresh.of(clash: Bool, +b: List<&2, U32>, +n: Nat, +ns: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match clash:
    case True{}:
      act.fresh.try(64n, act.used(act.nth.name(b, n), ns), b, ns, n)
    case False{}:
      b

def act.fresh.go(+b: List<&2, U32>, +ctx: List<&2, T.Bt>) -> List<&2, U32>:
  +ns = act.names(ctx)
  act.fresh.of(act.used(b, ns), b, List.length(&2, T.Bt, ctx), ns)

def act.fresh.in.of(+b: List<&2, U32>, +ns: List<&2, List<&2, U32>>, +n: Nat) -> List<&2, U32>:
  act.fresh.of(act.used(b, ns), b, n, ns)


# A name for a binder from Agda's hint, distinct from every name in scope
# (a clash gets the scope's depth after an underscore).
# a fresh name against the context and the names seen besides
def act.fresh.in(+x: List<&2, U32>, +ctx: List<&2, T.Bt>, +seen: List<&2, List<&2, U32>>) -> List<&2, U32>:
  act.fresh.in.of(act.hint(x), List.append(&2, List<&2, U32>, act.names(ctx), seen), Nat.add(List.length(&2, T.Bt, ctx), List.length(&2, List<&2, U32>, seen)))

def act.fresh(+x: List<&2, U32>, +ctx: List<&2, T.Bt>) -> List<&2, U32>:
  act.fresh.go(act.hint(x), ctx)
# Copies ------------------------------------------------------------------------

# the first n arguments of an elimination spine (in order) and the rest;
# ok is False when the spine has fewer, or a projection among them
type ActSplit is Data:
  ActSplit{vs: List<&2, A.Ag>, rest: A.Ag, ok: Bool}

def act.split.put(t: A.Ag, s: ActSplit) -> ActSplit:
  match s:
    case ActSplit{vs, rest, ok}:
      ActSplit{t <> vs, rest, ok}

def act.split(n: Nat, es: A.Ag) -> ActSplit:
  match n es:
    case 0n es:
      ActSplit{Nil{}, es, True{}}
    case 1n+p A.AgEApp{i, t, rest}:
      act.split.put(t, act.split(p, rest))
    case 1n+p es:
      ActSplit{Nil{}, es, False{}}

def act.unf.got(r: Map<&2, ActCopy> & ActCopy) -> ActCopy:
  (m, c) = r
  c

def act.unfold.split(+n: Nat, body: A.Ag, s: ActSplit) -> A.Ag:
  match s:
    case ActSplit{vs, rest, True{}}:
      asb.push(asb.subst(body, 0n, List.reverse(&2, A.Ag, vs), n), rest)
    case ActSplit{vs, rest, False{}}:
      A.AgNone{}

# the leaf a type-valued definition unfolds to, with the arguments
# substituted (the rest applied); AgNone when it does not unfold
def act.unfold.of(c: ActCopy, +es: A.Ag) -> A.Ag:
  match c:
    case ActCopy{0n, A.AgNone{}}:
      A.AgNone{}
    case ActCopy{+n, body}:
      act.unfold.split(n, body, act.split(n, es))

# Opaque types: a record field that is a type (Category.Obj C, C [ A , B ],
# Setoid.Carrier S) has elements no clause can split on; the projection's
# symbol carries the mark in its fields.  A visible Pi over such a type
# whose codomain mentions its variable (`η : ∀ X → D [ F₀ X , G₀ X ]`, a
# law's `∀ f → …`) is erased, as the spike erases objects and morphisms:
# Bend cannot copy an element of a Type, and these are used only in types
# and at other erased places (a non-dependent one, `F₁ : C [ A , B ] → …`,
# stays live: it is data).
def act.opaque.mark(srt: Bool) -> List<&2, String>:
  match srt:
    case True{}:
      ["opaque-sort"]
    case False{}:
      Nil{}

def act.opaque.fs(fs: List<&2, String>) -> Bool:
  match fs:
    case h <> Nil{}:
      String.eq(h, "opaque-sort")
    case _:
      False{}

def act.opaque.is(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, None{}}:
      act.opaque.fs(fs)
    case _:
      False{}

def act.opaque.copy(s: ActSym) -> ActCopy:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, Some{cp}}:
      cp
    case _:
      ActCopy{0n, A.AgNone{}}

# whether an elimination spine projects an opaque field (C .Obj)
def act.opaque.es(es: A.Ag, +tab: Map<&2, ActSym>) -> Bool:
  match es:
    case A.AgEProj{+q, rest}:
      Bool.or(act.opaque.is(act.sym.got(Map.get(ActSym, act.sym0(), tab, act.key(q)))), act.opaque.es(rest, tab))
    case A.AgEApp{i, a, rest}:
      act.opaque.es(rest, tab)
    case _:
      False{}

# whether a TYPE is opaque, seen through copies and type-valued definitions
def act.opaque(fuel: Nat, t: A.Ag, +tab: Map<&2, ActSym>, +unf: Map<&2, ActCopy>) -> Bool:
  match fuel t:
    case f A.AgEl{s, x}:
      act.opaque(f, x, tab, unf)
    case 1n+(+f) A.AgDef{+q, +es}:
      +s = act.sym.got(Map.get(ActSym, act.sym0(), tab, act.key(q)))
      Bool.or(act.opaque.is(s), Bool.or(act.opaque(f, act.unfold.of(act.opaque.copy(s), es), tab, unf), act.opaque(f, act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(q))), es), tab, unf)))
    case 1n+(+f) A.AgDefX{+q, +es}:
      +s = act.sym.got(Map.get(ActSym, act.sym0(), tab, act.key(q)))
      Bool.or(act.opaque.is(s), Bool.or(act.opaque(f, act.unfold.of(act.opaque.copy(s), es), tab, unf), act.opaque(f, act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(q))), es), tab, unf)))
    case f A.AgVar{i, x, es}:
      act.opaque.es(es, tab)
    case _ _:
      False{}

# a Pi binder erased as over an opaque type (dep: its codomain mentions it)
def act.opaque.dep(dep: Bool, +a: A.Ag, +tab: Map<&2, ActSym>, +unf: Map<&2, ActCopy>) -> Bool:
  match dep:
    case True{}:
      act.opaque(8n, a, tab, unf)
    case False{}:
      False{}

def act.opaque.env(dep: Bool, +a: A.Ag, +env: ActEnv) -> Bool:
  match env:
    case ActEnv{mod, +tab, al, +unf}:
      act.opaque.dep(dep, a, tab, unf)

def act.expand.copy(+n: Nat, body: A.Ag, q: A.AgQ, +es: A.Ag, s: ActSplit) -> A.Ag:
  match s:
    case ActSplit{vs, rest, True{}}:
      asb.push(asb.subst(body, 0n, List.reverse(&2, A.Ag, vs), n), rest)
    case ActSplit{vs, rest, False{}}:
      A.AgDefX{q, es}

# a definition seen by the inlining: a copy's leaf with the arguments
# substituted (the rest applied to it), anything else marked resolved
def act.expand(s: ActSym, q: A.AgQ, +es: A.Ag) -> A.Ag:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, Some{ActCopy{+nv, body}}}:
      act.expand.copy(nv, body, q, es, act.split(nv, es))
    case _:
      A.AgDefX{q, es}

# a lambda's body with its one argument: put for variable 0 when the
# lambda binds (abs); a constant lambda (noabs) binds none
def act.beta1(d: Bool, b: A.Ag, v: A.Ag) -> A.Ag:
  match d:
    case True{}:
      asb.subst(b, 0n, [v], 1n)
    case False{}:
      b

# Eta unfoldings ---------------------------------------------------------------
#
# A function whose case tree splits only records with eta (Σ's _,_) before
# its one leaf unfolds where its value is a type.  Product's
# `_⇒_ = zipWith C._⇒_ D._⇒_ _×_` matches its two pairs, so `A ⇒ B` stays
# stuck on the variables A B in Bend (which has no record eta), and the
# record's `id` then has no type it fits.  The unfolding (made by
# act.etu.of) writes each split field as the projection of its parameter
# (`proj₁ A`); act.inline takes it only when the call's value is a type (a
# sort, a Pi, a data type or record, a type-valued definition), where every
# place is dead, so the parameters repeat freely.  The unfoldings sit in
# the unfoldings map under "eta:" KEY.

def act.etu.key(q: A.AgQ) -> String:
  "eta:" ++ act.key(q)

def act.etu.get(+env: ActEnv, q: A.AgQ) -> ActCopy:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.etu.key(q)))

# whether an elimination spine is applications only
def act.es.plain(es: A.Ag) -> Bool:
  match es:
    case A.AgEApp{i, t, rest}:
      act.es.plain(rest)
    case A.AgENil{}:
      True{}
    case _:
      False{}

def act.es.apps(es: A.Ag) -> Nat:
  match es:
    case A.AgEApp{i, t, rest}:
      1n+act.es.apps(rest)
    case _:
      0n

# the arguments var k-1 ... var 0
def act.etu.args(k: Nat) -> A.Ag:
  match k:
    case 0n:
      A.AgENil{}
    case 1n+(+p):
      A.AgEApp{A.aas.i.vis(), A.AgVar{p, S.b("eta"), A.AgENil{}}, act.etu.args(p)}

def act.etu.lam(k: Nat, b: A.Ag) -> A.Ag:
  match k:
    case 0n:
      b
    case 1n+p:
      A.AgLam{A.aas.i.vis(), S.b("eta"), True{}, act.etu.lam(p, b)}

def act.etu.short(plain: Bool, +k: Nat, +n: Nat, body: A.Ag, +es: A.Ag) -> A.Ag:
  match plain:
    case True{}:
      act.etu.lam(k, act.unfold.of(ActCopy{n, body}, asb.elims.cat(asb.shift(es, k, 0n), act.etu.args(k))))
    case False{}:
      A.AgNone{}

# the unfolding applied to a call's arguments, under a lambda for each one
# the call leaves out (`zipWith f g h` is a relation); AgNone for none
def act.etu.at(c: ActCopy, +es: A.Ag) -> A.Ag:
  match c:
    case ActCopy{0n, A.AgNone{}}:
      A.AgNone{}
    case ActCopy{+n, body}:
      act.etu.short(Bool.or(Bool.not(Nat.is_lt(act.es.apps(es), n)), act.es.plain(es)), Nat.sub(n, act.es.apps(es)), n, body, es)

def act.unf.has.got(r: Map<&2, ActCopy> & Bool) -> Bool:
  (m, b) = r
  b

# A function definition's own parameters' types (act.params at
# act.item.fun) are read under "sig!": a Pi there (_∘_'s `f : ∀ {x} (y :
# B x) → C x y`, λ-'s) keeps its hidden binders erased, as a def's own
# hidden parameters are, so `f {x} (g x)` does not use x twice and need
# not make A Data (Relation.Unary's ⟨·⟩, Function.Base's golden).  A
# record's fields, a constructor's arguments and a type-valued def's body
# (Reflexive, _⇒_) keep them live.
def act.sig.env(env: ActEnv) -> ActEnv:
  match env:
    case ActEnv{mod, tab, al, unf}:
      ActEnv{mod, tab, al, Map.set(&2, ActCopy, unf, "sig!", ActCopy{0n, A.AgNone{}})}

# a record's projection is no such signature: its type is its field's
def act.sig.when(p: A.AgProj, env: ActEnv) -> ActEnv:
  match p:
    case A.AgPrOf{Some{r}, o, ix}:
      env
    case _:
      act.sig.env(env)

# a `with` helper's header is no such signature either (2026-10-29): Agda
# gives its parameters' types opened (total⇒refl's helper takes
# `{x y} → x ≈ y → x ≤ y` where total⇒refl took `_≈_ ⇒ _≤_`), and its
# caller passes values whose types Bend opens from those definitions, with
# their own (live) hidden binders (Consequences' total⇒refl,
# total∧dec⇒dec, trans∧tri⇒resp: "expected @-x observed @x")
def act.sig.with(w: Maybe<&2, A.AgQ>, p: A.AgProj, env: ActEnv) -> ActEnv:
  match w:
    case Some{q}:
      env
    case None{}:
      act.sig.when(p, env)

def act.sig.on(+env: ActEnv) -> Bool:
  match env:
    case ActEnv{mod, tab, al, +unf}:
      act.unf.has.got(Map.has(&2, ActCopy, unf, "sig!"))

def act.kind.type(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, A.AkRecord{}, ms, ar, b, fs, c, cp}:
      True{}
    case ActSym{m, n, A.AkData{}, ms, ar, b, fs, c, cp}:
      True{}
    case _:
      False{}

def act.type.sym(s: ActSym, +env: ActEnv, q: A.AgQ) -> Bool:
  match env:
    case ActEnv{mod, tab, al, unf}:
      Bool.or(act.kind.type(s), act.unf.has.got(Map.has(&2, ActCopy, unf, act.key(q))))

# whether a term is a type by its head (a copy seen through)
def act.type.head(fuel: Nat, t: A.Ag, +env: ActEnv) -> Bool:
  match fuel t:
    case f A.AgSort{s}:
      True{}
    case f A.AgPi{i, x, a, d, b}:
      True{}
    case f A.AgEl{s, x}:
      True{}
    case f A.AgLam{i, x, d, b}:
      act.type.head(f, b, env)
    case f A.AgBeta{g, es}:
      act.type.head(f, g, env)
    case f A.AgDefX{+q, es}:
      act.type.sym(act.sym(env, q), env, q)
    case 1n+f A.AgDef{+q, +es}:
      Bool.or(act.type.sym(act.sym(env, q), env, q), act.type.head(f, act.expand(act.sym(env, q), q, es), env))
    case _ _:
      False{}

# whether a term builds a constructor (under its lambdas)
def act.con.head(t: A.Ag) -> Bool:
  match t:
    case A.AgLam{i, x, d, b}:
      act.con.head(b)
    case A.AgBeta{g, es}:
      act.con.head(g)
    case A.AgCon{q, o, es}:
      True{}
    case _:
      False{}

def act.etu.n(c: ActCopy) -> Nat:
  match c:
    case ActCopy{n, b}:
      n

def act.etu.pick(+u: A.Ag, d: A.Ag, part: Bool, +env: ActEnv) -> A.Ag:
  Bool.pick(A.Ag, Bool.or(act.type.head(16n, u, env), Bool.and(Bool.and(part, act.quant.on()), act.con.head(u))), u, d)

# a call act.inline resolved as no copy (AgDefX), unfolded instead when it
# has an eta unfolding and its value there is a type, or it is partial and
# builds a pair (Product's `_∘_ = zip C._∘_ D._∘_`: by projections its laws
# reduce on morphism variables; a pair used twice then needs Data homs,
# which the quantity repairs specialise it to).  at: the call is a record
# constructor's argument, under its lambdas (2026-10-21: only there, as
# Product's fields are; `map₁ f = map f id` unfolded used its pair twice
# and needed Data, where the call checks)
def act.etu.none(t: A.Ag) -> Bool:
  match t:
    case A.AgNone{}:
      True{}
    case _:
      False{}

# in a header (ty), any call that has an unfolding takes it
def act.etu.hpick(ty: Bool, +u: A.Ag, d: A.Ag, part: Bool, +env: ActEnv) -> A.Ag:
  match ty:
    case True{}:
      Bool.pick(A.Ag, act.etu.none(u), d, u)
    case False{}:
      act.etu.pick(u, d, part, env)

def act.etu.try(t: A.Ag, +q: A.AgQ, +es: A.Ag, at: Bool, ty: Bool, +env: ActEnv) -> A.Ag:
  match t:
    case A.AgDefX{q2, es2}:
      +c = act.etu.get(env, q)
      act.etu.hpick(ty, act.etu.at(c, es), A.AgDefX{q2, es2}, Bool.and(at, Nat.is_lt(act.es.apps(es), act.etu.n(c))), env)
    case t:
      t

# Combinators (2026-10-22) ------------------------------------------------------
#
# A combinator is a function whose case tree is one leaf (no split), outside
# any mutual block (so not recursive), neither a projection, a copy, a with
# function nor an extended lambda, not type-valued, whose leaf is headed
# (under its lambdas) by a variable applied, or by an earlier combinator,
# and made of variables, constructors and earlier combinators only:
# Function.Base's `_-⟪_⟫-_` (`λ x y → f x y * g x y`), and through it
# `_-⟪_∣`, `_-⟨_⟩-_` and `_on_`.  A combinator's own body is translated with
# the saturated calls of combinators in it unfolded and beta-reduced, as
# Agda reduces them: `_*_ on f` is then `λ x y → f x * f y`, which uses x and
# y once, where through `_-⟪_⟫-_` (which uses them twice, so its A and B are
# Data) its A had to be Data, and a record whose field type says
# `_≈_ on f` over a Kind(a) carrier (Algebra.Structures' `IsGroup`,
# `Congruent₁`) had no Data to pass.  Only combinators' bodies are
# normalised: a lemma's body keeps its calls as Agda wrote them.  The
# leaves sit in the unfoldings under "cmb:" KEY; while a combinator's body
# is translated, the unfoldings carry "cmb!" (act.cmb.env), which
# act.inline reads.  Which definitions are combinators: act.cmb.of, after
# the type-valued openings (it needs act.ends.sort.u).

def act.cmb.key(q: A.AgQ) -> String:
  "cmb:" ++ act.key(q)

# the environment a definition's body is translated in: marked "cmb!" when
# the definition (by key) is a combinator
def act.cmb.mark(on: Bool, unf: Map<&2, ActCopy>) -> Map<&2, ActCopy>:
  match on:
    case True{}:
      Map.set(&2, ActCopy, unf, "cmb!", ActCopy{0n, A.AgNone{}})
    case False{}:
      unf

def act.cmb.env(+key: String, env: ActEnv) -> ActEnv:
  match env:
    case ActEnv{mod, tab, al, +unf}:
      ActEnv{mod, tab, al, act.cmb.mark(act.unf.has.got(Map.has(&2, ActCopy, unf, "cmb:" ++ key)), unf)}

def act.cmb.when(on: Bool, c: ActCopy, +es: A.Ag) -> A.Ag:
  match on:
    case True{}:
      act.unfold.of(c, es)
    case False{}:
      A.AgNone{}

# q applied to es unfolded as a combinator, inside a combinator's body
# (AgNone elsewhere, for no combinator, or a call not saturated)
def act.cmb.at(+env: ActEnv, +q: A.AgQ, +es: A.Ag) -> A.Ag:
  match env:
    case ActEnv{mod, tab, al, +unf}:
      act.cmb.when(act.unf.has.got(Map.has(&2, ActCopy, unf, "cmb!")), act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.cmb.key(q))), es)

def act.cmb.pick(u: A.Ag, d: A.Ag) -> A.Ag:
  match u:
    case A.AgNone{}:
      d
    case u:
      u

# a call act.inline resolved as no copy (AgDefX), unfolded when it is a
# combinator's inside a combinator's body
def act.cmb.try(t: A.Ag, +q: A.AgQ, +es: A.Ag, +env: ActEnv) -> A.Ag:
  match t:
    case A.AgDefX{q2, es2}:
      act.cmb.pick(act.cmb.at(env, q, es), A.AgDefX{q2, es2})
    case t:
      t

# Copattern reductions --------------------------------------------------------
#
# A field projected out of a definition made by copatterns reduces here to
# that field's clause: `isPartialEquivalence (partialSetoid S)` is
# `IsEquivalence.isPartialEquivalence (isEquivalence S)`, and through
# Category's hom-setoid a reasoning lemma's `partialSetoid(~hom-setoid(~C,
# X, Y))` (a template argument, which must be closed: its objects had to be
# templates, and no caller with a lambda's objects could use the lemma)
# becomes C's equiv at X Y, with S or C used once.  Bend would do the same
# when it inlines a template; doing it here also takes non-closed records.
# The clauses sit in the unfoldings under "cop:" DEF "|" FIELD (act.cop.add).

def act.cop.key(f: A.AgQ, q: A.AgQ) -> String:
  "cop:" ++ act.key(f) ++ "|" ++ act.key(q)

def act.ag.none(t: A.Ag) -> Bool:
  match t:
    case A.AgNone{}:
      True{}
    case _:
      False{}

def act.ag.last(xs: List<&2, A.Ag>) -> Maybe<&2, A.Ag>:
  match xs:
    case Nil{}:
      None{}
    case h <> Nil{}:
      Some{h}
    case h <> t:
      act.ag.last(t)

def act.sym.arity(s: ActSym) -> Nat:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, cp}:
      ar

def act.cop.push(u: A.Ag, rest: A.Ag) -> A.Ag:
  match u:
    case A.AgNone{}:
      A.AgNone{}
    case u:
      asb.push(u, rest)

def act.cop.rec(m: Maybe<&2, A.Ag>, +q: A.AgQ, rest: A.Ag, +unf: Map<&2, ActCopy>) -> A.Ag:
  match m:
    case Some{A.AgDef{f, +es}}:
      act.cop.push(act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.cop.key(f, q))), es), rest)
    case Some{A.AgDefX{f, +es}}:
      act.cop.push(act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.cop.key(f, q))), es), rest)
    case _:
      A.AgNone{}

def act.cop.split(s: ActSplit, +q: A.AgQ, +unf: Map<&2, ActCopy>) -> A.Ag:
  match s:
    case ActSplit{vs, rest, True{}}:
      act.cop.rec(act.ag.last(vs), q, rest, unf)
    case _:
      A.AgNone{}

# q applied to es reduced as a copattern definition's field (AgNone when not)
def act.cop.at(+env: ActEnv, +q: A.AgQ, +es: A.Ag) -> A.Ag:
  match env:
    case ActEnv{mod, +tab, al, +unf}:
      act.cop.split(act.split(act.sym.arity(act.sym.got(Map.get(ActSym, act.sym0(), tab, act.key(q)))), es), q, unf)

# Dead arguments (2026-10-25) ---------------------------------------------------
#
# An argument the callee takes erased or dropped is dead, as a header's
# places are, so a call there that has an eta unfolding takes it.  Product's
# πˡ has `homomorphism = refl`, whose point is `proj₁ (zip _∘_ _∘_ g f)`,
# stuck in Bend (no record eta) on the pairs g f; in projection form it is
# `proj₁ g ∘ proj₁ f`, the goal's.  Past the callee's modes (the Pis of a
# type-valued result: refl's {x} under `Reflexive _≈_`) the argument's own
# information decides (hidden, instance, irrelevant or @0).  The inlining
# carries the modes left of a callee's spine (None{}: not a callee's).
def act.m.dead(m: ActM) -> Bool:
  match m:
    case AmErased{}:
      True{}
    case AmDrop{}:
      True{}
    case _:
      False{}

def act.sym.ms(s: ActSym) -> List<&2, ActM>:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, cp}:
      ms

# whether the spine's next argument is dead
def act.ms.dead(ms: Maybe<&2, List<&2, ActM>>, +i: A.AgI) -> Bool:
  match ms:
    case Some{m <> t}:
      act.m.dead(m)
    case Some{Nil{}}:
      act.info.erased(i)
    case None{}:
      False{}

def act.ms.tail(ms: Maybe<&2, List<&2, ActM>>) -> Maybe<&2, List<&2, ActM>>:
  match ms:
    case Some{m <> t}:
      Some{t}
    case ms:
      ms

# Every copy in a term inlined, through chains of copies of copies, and
# the lambda redexes substitution leaves reduced.  Each expansion or
# reduction spends one unit of fuel (a resolved definition too), and the
# fuel bounds the nesting: what is left when it runs out stays as it is
# and fails at the translation as an unknown copy.
def act.inline.go(+fuel: Nat, a: A.Ag, +at: Bool, +ty: Bool, +ms: Maybe<&2, List<&2, ActM>>, +env: ActEnv) -> A.Ag:
  match fuel a:
    case 1n+p A.AgBeta{A.AgLam{i, x, d, b}, A.AgEApp{i2, v, rest}}:
      act.inline.go(p, asb.push(act.beta1(d, b, v), rest), False{}, ty, None{}, env)
    case f A.AgBeta{g, A.AgENil{}}:
      act.inline.go(f, g, at, ty, None{}, env)
    case 1n+p A.AgDef{+q, +es}:
      act.inline.go(p, act.cmb.try(act.etu.try(act.expand(act.sym(env, q), q, es), q, es, at, ty, env), q, es, env), False{}, ty, None{}, env)
    case 1n+p A.AgDefX{+q, es}:
      +es2 = act.inline.go(p, es, False{}, ty, Some{act.sym.ms(act.sym(env, q))}, env)
      +r = act.cop.at(env, q, es2)
      Bool.pick(A.Ag, act.ag.none(r), A.AgDef{q, es2}, act.inline.go(p, r, False{}, ty, None{}, env))
    case f A.AgVar{i, x, es}:
      A.AgVar{i, x, act.inline.go(f, es, False{}, ty, None{}, env)}
    case f A.AgCon{q, o, es}:
      A.AgCon{q, o, act.inline.go(f, es, True{}, ty, None{}, env)}
    case f A.AgLam{i, x, d, b}:
      A.AgLam{i, x, d, act.inline.go(f, b, at, ty, None{}, env)}
    case f A.AgPi{i, x, a2, d, b}:
      A.AgPi{i, x, act.inline.go(f, a2, False{}, ty, None{}, env), d, act.inline.go(f, b, False{}, ty, None{}, env)}
    case f A.AgEl{s, t}:
      A.AgEl{s, act.inline.go(f, t, False{}, ty, None{}, env)}
    case f A.AgDontCare{t}:
      A.AgDontCare{act.inline.go(f, t, False{}, ty, None{}, env)}
    case f A.AgEApp{+i, t, rest}:
      A.AgEApp{i, act.inline.go(f, t, at, Bool.or(ty, act.ms.dead(ms, i)), None{}, env), act.inline.go(f, rest, at, ty, act.ms.tail(ms), env)}
    case f A.AgEProj{q, rest}:
      A.AgEProj{q, act.inline.go(f, rest, False{}, ty, None{}, env)}
    case f a2:
      a2

def act.inline(+fuel: Nat, a: A.Ag, +env: ActEnv) -> A.Ag:
  act.inline.go(fuel, a, False{}, False{}, None{}, env)

# A header's type inlined: every place in it is dead, so a call of a
# function with an eta unfolding is unfolded there (2026-10-22, upstream
# Bend has no record eta: la_cdot_ra's `(Q ∘ uncurry _|>_) x` is stuck on
# uncurry's match of x, where its body's type has `Q (proj₂ x (proj₁ x))`;
# Product's `map f g X` likewise).
def act.inline.hdr(+fuel: Nat, a: A.Ag, +env: ActEnv) -> A.Ag:
  act.inline.go(fuel, a, False{}, True{}, None{}, env)

# Applications ----------------------------------------------------------------

def act.bmode(m: ActM) -> T.BMode:
  match m:
    case AmErased{}:
      T.BmErased{}
    case AmCopy{}:
      T.BmCopy{}
    case AmTpl{}:
      T.BmTpl{}
    case _:
      T.BmLive{}

def act.m.of(m: T.BMode) -> ActM:
  match m:
    case T.BmErased{}:
      AmErased{}
    case T.BmCopy{}:
      AmCopy{}
    case T.BmTpl{}:
      AmTpl{}
    case T.BmLive{}:
      AmLive{}

def act.list.nolevel.put(lv: Bool, h: T.Bt, t: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match lv:
    case True{}:
      t
    case False{}:
      h <> t

# the arguments of a spine as a list, the level markers left out
def act.list.nolevel(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{+h, t}:
      act.list.nolevel.put(act.is.marker(h), h, act.list.nolevel(t))
    case _:
      Nil{}

def act.app.list(f: T.Bt, xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case Nil{}:
      f
    case h <> t:
      T.BtApp{f, T.tba.args(h <> t)}

# a variable applied: its level arguments dropped, and every argument
# marked as at a parameter whose mode is unknown (BtDead): the variable's
# type is not known here, and its Pi often erases the argument, so the
# quantity pass does not count these uses (Bend's check finds a real
# double use); the mark is doubled (BtDead of BtDead) as "unknown", which
# the template test takes as live: a template argument there must be closed
def act.deads(xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BtDead{T.BtDead{h}} <> act.deads(t)

def act.app.var(f: T.Bt, args: T.Bt) -> T.Bt:
  act.app.list(f, act.deads(act.list.nolevel(args)))

# The kept arguments of a call: an argument whose parameter is dropped is
# left out, one at an erased parameter is marked dead, one at a template
# is passed as such; past the type's Pis every argument is kept but a
# level.
def act.keep(args: T.Bt, ms: List<&2, ActM>) -> List<&2, T.Bt>:
  match args ms:
    case T.BtArgs{a, rest} AmDrop{} <> t:
      act.keep(rest, t)
    case T.BtArgs{a, rest} AmErased{} <> t:
      T.BtDead{a} <> act.keep(rest, t)
    case T.BtArgs{a, rest} AmTpl{} <> t:
      T.BtTplArg{a} <> act.keep(rest, t)
    case T.BtArgs{a, rest} m <> t:
      a <> act.keep(rest, t)
    case T.BtArgs{a, rest} Nil{}:
      act.list.nolevel(T.BtArgs{a, rest})
    case _ _:
      Nil{}

# a call's arguments split at the definition's arity
type ActTake is Data:
  ActTake{args: T.Bt, ms: List<&2, ActM>, rest: T.Bt, rms: List<&2, ActM>, ok: Bool}

def act.take.put(a: T.Bt, m: ActM, t: ActTake) -> ActTake:
  match t:
    case ActTake{args, ms, rest, rms, ok}:
      ActTake{T.BtArgs{a, args}, m <> ms, rest, rms, ok}

# the modes of the n parameters a call left out (live past the type's Pis)
def act.take.need(n: Nat, ms: List<&2, ActM>) -> List<&2, ActM>:
  match n ms:
    case 0n ms:
      Nil{}
    case 1n+p m <> t:
      m <> act.take.need(p, t)
    case 1n+p Nil{}:
      AmLive{} <> act.take.need(p, Nil{})

# the first n arguments and their modes, the rest of both; when the call
# has fewer than n, ok is False and rms holds the missing parameters' modes
def act.take(n: Nat, args: T.Bt, ms: List<&2, ActM>) -> ActTake:
  match n args ms:
    case 0n args ms:
      ActTake{T.BtANil{}, Nil{}, args, ms, True{}}
    case 1n+p T.BtArgs{a, rest} m <> t:
      act.take.put(a, m, act.take(p, rest, t))
    case 1n+p T.BtArgs{a, rest} Nil{}:
      act.take.put(a, AmLive{}, act.take(p, rest, Nil{}))
    case 1n+p T.BtANil{} ms:
      ActTake{T.BtANil{}, Nil{}, T.BtANil{}, act.take.need(1n+p, ms), False{}}
    case 1n+p args ms:
      ActTake{T.BtANil{}, Nil{}, T.BtANil{}, Nil{}, False{}}

# a header's templates come first (ToBend/Copy.bend), so a call's template
# arguments do too, in order, before the others
def act.is.tpl(t: T.Bt) -> Bool:
  match t:
    case T.BtTplArg{a}:
      True{}
    case _:
      False{}

def act.tpl.first(+xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  List.append(&2, T.Bt, List.filter(~T.Bt, ~(x => act.is.tpl(x)), xs), List.filter(~T.Bt, ~(x => Bool.not(act.is.tpl(x))), xs))

# A call with fewer arguments than the def's header takes is eta-expanded:
# a lambda for each missing kept parameter (a dropped one needs none).  The
# names are eta1, eta2, ...: a call's own arguments were translated before
# its lambdas exist, so they cannot mention them.
def act.eta.names(ms: List<&2, ActM>, +k: Nat) -> List<&2, List<&2, U32>>:
  match ms:
    case Nil{}:
      Nil{}
    case AmDrop{} <> t:
      act.eta.names(t, k)
    case m <> t:
      List.append(&2, U32, S.b("eta"), S.b(Nat.show(k))) <> act.eta.names(t, 1n+k)

def act.eta.vars(ns: List<&2, List<&2, U32>>) -> List<&2, T.Bt>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      T.BtVar{n} <> act.eta.vars(t)

def act.eta(ns: List<&2, List<&2, U32>>, b: T.Bt) -> T.Bt:
  match ns:
    case Nil{}:
      b
    case n <> t:
      T.BtLam{T.BmLive{}, n, act.eta(t, b)}

# A call missing arguments is eta-expanded, each lambda in the mode of the
# callee's parameter it stands for (an erased one is -eta, its variable
# passed in a dead position), as the call's type has it.
def act.eta.ms(ms: List<&2, ActM>) -> List<&2, ActM>:
  match ms:
    case Nil{}:
      Nil{}
    case AmDrop{} <> t:
      act.eta.ms(t)
    case m <> t:
      m <> act.eta.ms(t)

def act.eta.by(ns: List<&2, List<&2, U32>>, ms: List<&2, ActM>, b: T.Bt) -> T.Bt:
  match ns ms:
    case n <> t AmErased{} <> mt:
      T.BtLam{T.BmErased{}, n, act.eta.by(t, mt, b)}
    case n <> t m <> mt:
      T.BtLam{T.BmLive{}, n, act.eta.by(t, mt, b)}
    case _ _:
      b

def act.eta.args(ns: List<&2, List<&2, U32>>, ms: List<&2, ActM>) -> List<&2, T.Bt>:
  match ns ms:
    case n <> t AmErased{} <> mt:
      T.BtDead{T.BtVar{n}} <> act.eta.args(t, mt)
    case n <> t AmTpl{} <> mt:
      T.BtTplArg{T.BtVar{n}} <> act.eta.args(t, mt)
    case n <> t m <> mt:
      T.BtVar{n} <> act.eta.args(t, mt)
    case _ _:
      Nil{}

# f(first arity kept arguments)(the other kept ones), as the Bend def's
# header takes the first group and its value the rest
def act.call.of(+f: List<&2, U32>, t: ActTake) -> T.Bt:
  match t:
    case ActTake{args, ms, rest, rms, True{}}:
      act.app.list(T.BtApp{T.BtVar{f}, T.tba.args(act.tpl.first(act.keep(args, ms)))}, act.keep(rest, rms))
    case ActTake{args, ms, rest, +rms, False{}}:
      +ns = act.eta.names(rms, 1n)
      +em = act.eta.ms(rms)
      act.eta.by(ns, em, T.BtApp{T.BtVar{f}, T.tba.args(act.tpl.first(List.append(&2, T.Bt, act.keep(args, ms), act.eta.args(ns, em))))})

def act.call(+f: List<&2, U32>, ms: List<&2, ActM>, +n: Nat, args: T.Bt) -> T.Bt:
  act.call.of(f, act.take(n, args, ms))

# ≡'s kept arguments are its type and its two sides; with fewer it is a
# relation, eta-expanded (eqx, eqy: its arguments were translated before
# these lambdas exist)
# (its arguments arrive marked dead: ≡ is type-valued, so all its
# parameters are erased; an equation's sides are dead anyway, and the
# rewrites read them as plain variables, so the marks come off)
def act.undead(t: T.Bt) -> T.Bt:
  match t:
    case T.BtDead{a}:
      a
    case t:
      t

# ≡'s level argument, a quantity once levels are, is no part of the equation
def act.eq.noq(on: Bool, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match on xs:
    case True{} h <> t:
      t
    case _ xs:
      xs

def act.eq(xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case ty <> a <> b <> Nil{}:
      T.BtEq{act.undead(ty), act.undead(a), act.undead(b)}
    case ty <> a <> Nil{}:
      T.BtLam{T.BmLive{}, S.b("eqy"), T.BtEq{act.undead(ty), act.undead(a), T.BtVar{S.b("eqy")}}}
    case ty <> Nil{}:
      T.BtLam{T.BmLive{}, S.b("eqx"), T.BtLam{T.BmLive{}, S.b("eqy"), T.BtEq{act.undead(ty), T.BtVar{S.b("eqx")}, T.BtVar{S.b("eqy")}}}}
    case _:
      act.todo("≡ applied to other than its two sides")

# A datatype applied: Bend writes it with all its parameters (D<A, B>), so
# one applied to fewer is eta-expanded over the missing ones (Σ-syntax = Σ).
def act.tyapp.of(+ref: List<&2, U32>, t: ActTake) -> T.Bt:
  match t:
    case ActTake{args, ms, rest, rms, True{}}:
      T.BtTyApp{ref, T.tba.args(act.keep(args, ms))}
    case ActTake{args, ms, rest, rms, False{}}:
      +ns = act.eta.names(rms, 1n)
      act.eta(ns, T.BtTyApp{ref, T.tba.args(List.append(&2, T.Bt, act.keep(args, ms), act.eta.vars(ns)))})

def act.app.def.kind(k: A.AgKw, cp: Bool, +ref: List<&2, U32>, ms: List<&2, ActM>, +ar: Nat, args: T.Bt) -> T.Bt:
  match k cp:
    case _ True{}:
      act.todo("a module application's copy that was not inlined")
    case A.AkRecord{} False{}:
      act.tyapp.of(ref, act.take(ar, args, ms))
    case A.AkData{} False{}:
      act.tyapp.of(ref, act.take(ar, args, ms))
    case A.AkFunction{} False{}:
      act.call(ref, ms, ar, args)
    case A.AkPrimitive{} False{}:
      act.call(ref, ms, ar, args)
    case A.AkPostulate{} False{}:
      act.todo("a postulate")
    case _ False{}:
      T.BtTodo{List.append(&2, U32, S.b("a name the symbol table does not have: "), ref)}

def act.copy.is(c: Maybe<&2, ActCopy>) -> Bool:
  match c:
    case Some{x}:
      True{}
    case None{}:
      False{}

# a definition applied
def act.app.def(s: ActSym, +env: ActEnv, args: T.Bt) -> T.Bt:
  match s:
    case ActSym{m, n, k, ms, ar, AbLevel{}, fs, c, cp}:
      Bool.pick(T.Bt, act.quant.on(), act.q1(), act.level())
    case ActSym{m, n, k, ms, ar, AbQuant{}, fs, c, cp}:
      Bool.pick(T.Bt, act.quant.on(), T.BtVar{S.b("Quant")}, act.level())
    case ActSym{m, n, k, ms, ar, AbQone{}, fs, c, cp}:
      Bool.pick(T.Bt, act.quant.on(), act.q1(), act.level())
    case ActSym{m, n, k, ms, ar, AbQmin{}, fs, c, cp}:
      Bool.pick(T.Bt, act.quant.on(), act.qmin.args(args), act.level())
    case ActSym{m, n, k, ms, ar, AbNat{}, fs, c, cp}:
      T.BtVar{S.b("Nat")}
    case ActSym{m, n, k, ms, ar, AbBool{}, fs, c, cp}:
      T.BtVar{S.b("Bool")}
    case ActSym{m, n, k, ms, ar, AbUnit{}, fs, c, cp}:
      T.BtVar{S.b("Unit")}
    case ActSym{m, n, k, ms, ar, AbString{}, fs, c, cp}:
      T.BtVar{S.b("String")}
    case ActSym{m, n, k, ms, ar, AbEq{}, fs, c, cp}:
      act.eq(act.eq.noq(act.quant.on(), act.keep(args, ms)))
    case ActSym{+m, +n, k, ms, ar, b, fs, c, cp}:
      act.app.def.kind(k, act.copy.is(cp), act.ref.of(act.is.here(env, m), env, m, n), ms, ar, args)

# suc applied, or unapplied (`cong suc`, `map suc xs`): the function
# sn => 1n+sn
def act.suc(xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case h <> t:
      T.BtSucc{h}
    case Nil{}:
      T.BtLam{T.BmLive{}, S.b("sn"), T.BtSucc{T.BtVar{S.b("sn")}}}

# {==} for each of a constructor's equation fields (an indexed family's)
def act.refls(fs: List<&2, String>) -> List<&2, T.Bt>:
  match fs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BtRefl{} <> act.refls(t)

# the modes of the parameters a call's arguments leave out
def act.ms.after(args: T.Bt, ms: List<&2, ActM>) -> List<&2, ActM>:
  match args ms:
    case T.BtArgs{a, rest} m <> t:
      act.ms.after(rest, t)
    case _ ms:
      ms

# A constructor applied to fewer than its fields (`pure = just`,
# `map inj₁ xs`) is eta-expanded over the missing ones, as a call is.
def act.app.con.kind(k: A.AgKw, +ref: List<&2, U32>, +ms: List<&2, ActM>, fs: List<&2, String>, +args: T.Bt) -> T.Bt:
  match k:
    case A.AkConstructor{}:
      +ns = act.eta.names(act.ms.after(args, ms), 1n)
      act.eta(ns, T.BtCon{ref, T.tba.args(List.append(&2, T.Bt, List.append(&2, T.Bt, act.keep(args, ms), act.eta.vars(ns)), act.refls(fs)))})
    case _:
      T.BtTodo{List.append(&2, U32, S.b("a constructor the symbol table does not have: "), ref)}

# a constructor applied (its own arguments only, as Agda writes them)
def act.app.con(s: ActSym, +env: ActEnv, args: T.Bt) -> T.Bt:
  match s:
    case ActSym{m, n, k, ms, ar, AbZero{}, fs, c, cp}:
      T.BtNat{S.b("0")}
    case ActSym{m, n, k, ms, ar, AbSuc{}, fs, c, cp}:
      act.suc(act.keep(args, ms))
    case ActSym{m, n, k, ms, ar, AbTrue{}, fs, c, cp}:
      T.BtCon{S.b("True"), T.BtANil{}}
    case ActSym{m, n, k, ms, ar, AbFalse{}, fs, c, cp}:
      T.BtCon{S.b("False"), T.BtANil{}}
    case ActSym{m, n, k, ms, ar, AbRefl{}, fs, c, cp}:
      T.BtRefl{}
    case ActSym{m, n, k, ms, ar, AbTt{}, fs, c, cp}:
      T.BtCon{S.b("Unit"), T.BtANil{}}
    case ActSym{+m, +n, k, ms, ar, b, fs, c, cp}:
      act.app.con.kind(k, act.ref.of(act.is.here(env, m), env, m, n), ms, fs, args)

# the context under a binder: its entry in front when it binds (abs), the
# same context when it does not (noabs)
def act.bind(dep: Bool, e: T.Bt, ctx: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match dep:
    case True{}:
      e <> ctx
    case False{}:
      ctx

def act.lit(l: A.Ag) -> T.Bt:
  match l:
    case A.AgLNat{s}:
      T.BtNat{s}
    case A.AgLStr{s}:
      T.BtStr{s}
    case _:
      act.todo("a literal Bend has no counterpart for (Word64, Float, Char, a quoted name)")

# a Pi: a Level binder leaves only the codomain
def act.pi(lv: Bool, m: ActM, nm: List<&2, U32>, d: Bool, a: T.Bt, +b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, Bool.and(lv, Bool.not(act.quant.on())), b, T.BtPi{act.bmode(m), nm, d, a, b})

# The fold over terms (and elimination spines, which become argument
# spines).  ctx: the Bend term of each binder in scope, index 0 first.
def act.t(a: A.Ag, +ctx: List<&2, T.Bt>, +env: ActEnv) -> T.Bt:
  match a:
    case A.AgVar{+i, x, es}:
      act.app.var(act.ctx.at(i, ctx), act.t(es, ctx, env))
    case A.AgDef{+q, es}:
      act.app.def(act.sym(env, q), env, act.t(es, ctx, env))
    case A.AgDefX{+q, es}:
      act.app.def(act.sym(env, q), env, act.t(es, ctx, env))
    case A.AgCon{+q, o, es}:
      act.app.con(act.sym(env, q), env, act.t(es, ctx, env))
    case A.AgLam{i, +x, d, b}:
      +nm = act.fresh(x, ctx)
      T.BtLam{T.BmLive{}, nm, act.t(b, act.bind(d, T.BtVar{nm}, ctx), env)}
    case A.AgPi{+i, +x, +a2, +d, +b}:
      +lv = act.ty.level(a2)
      +nm = act.fresh(x, ctx)
      act.pi(lv, Bool.pick(ActM, Bool.or(act.ends.sort(b), act.sig.on(env)), act.mode(i, a2, act.opaque.env(d, a2, env)), act.mode.v(i, a2, act.opaque.env(d, a2, env))), nm, d, act.t(a2, ctx, env), act.t(b, act.bind(d, Bool.pick(T.Bt, Bool.and(lv, Bool.not(act.quant.on())), act.level(), T.BtVar{nm}), ctx), env))
    case A.AgSort{s}:
      Bool.pick(T.Bt, act.quant.on(), act.sort(s, ctx, env), T.BtType{})
    case A.AgEl{s, t}:
      act.t(t, ctx, env)
    case A.AgLit{l}:
      act.lit(l)
    case A.AgLevel{l}:
      act.qt(l, ctx, env)
    case A.AgDontCare{t}:
      act.t(t, ctx, env)
    case A.AgStored{t}:
      act.todo("a stored term (agda-export could not restore a projection's parameters)")
    case A.AgMeta{es}:
      act.todo("an unsolved metavariable")
    case A.AgRaw{c, x}:
      act.todo("a cubical or unknown form")
    case A.AgBeta{f, es}:
      act.todo("a lambda applied that the inlining did not reduce")
    case A.AgENil{}:
      T.BtANil{}
    case A.AgEApp{i, +t, rest}:
      T.BtArgs{act.arg(Bool.and(Bool.not(act.quant.on()), act.is.level(t, ctx, env)), act.t(t, ctx, env)), act.t(rest, ctx, env)}
    case A.AgEProj{q, rest}:
      T.BtArgs{act.todo("a projection elimination (stored form)"), act.t(rest, ctx, env)}
    case A.AgERaw{x, rest}:
      T.BtArgs{act.todo("a cubical elimination"), act.t(rest, ctx, env)}
    case _:
      act.todo("not a term")

# Symbols of a module's definitions ----------------------------------------------

def act.qs(q: A.AgQ) -> List<&2, U32>:
  match q:
    case A.AgQ{s, w, k}:
      s

# the keys of a name list, in order
def act.keys(a: A.Ag) -> List<&2, String>:
  match a:
    case A.AgQs{i, q, rest}:
      act.key(q) <> act.keys(rest)
    case _:
      Nil{}

def act.vars.len(a: A.Ag) -> Nat:
  match a:
    case A.AgVars{i, x, rest}:
      1n+act.vars.len(rest)
    case _:
      0n

# a copy's leaf: done (vars ...) TERM
def act.copy.of(tree: A.Ag) -> Maybe<&2, ActCopy>:
  match tree:
    case A.AgDone{xs, t}:
      Some{ActCopy{act.vars.len(xs), t}}
    case _:
      None{}

# the patterns a clause matches before its first projection pattern
def act.pats.len(ps: A.Ag) -> Nat:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      0n
    case A.AgPArg{i, x, p, rest}:
      1n+act.pats.len(rest)
    case _:
      0n

def act.cls.arity(cls: A.Ag) -> Nat:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      act.pats.len(ps)
    case _:
      0n

def act.flag(+k: A.AgKw, fl: List<&2, A.AgKw>) -> Bool:
  match fl:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(A.aas.kw.eq(h, k), act.flag(k, t))

# A constructor's own arguments are its fields, values in Bend (a
# record's Carrier : Set c is a field like any other): live, a Level
# still dropped.
def act.ms.live(ms: List<&2, ActM>) -> List<&2, ActM>:
  match ms:
    case Nil{}:
      Nil{}
    case AmDrop{} <> t:
      AmDrop{} <> act.ms.live(t)
    case m <> t:
      AmLive{} <> act.ms.live(t)

def act.drop.n(n: Nat, ms: List<&2, ActM>) -> List<&2, ActM>:
  match n ms:
    case 1n+p m <> t:
      act.drop.n(p, t)
    case _ ms:
      ms

def act.sym.copy(c: Maybe<&2, ActCopy>, +mo: List<&2, U32>, +nm: List<&2, U32>, ms: List<&2, ActM>, b: ActB) -> ActSym:
  match c:
    case Some{ActCopy{+n, t}}:
      ActSym{mo, nm, A.AkFunction{}, ms, n, b, Nil{}, Nil{}, Some{ActCopy{n, t}}}
    case None{}:
      ActSym{mo, nm, A.AkFunction{}, ms, 0n, b, Nil{}, Nil{}, None{}}

# A function's entry: a record field's projection takes the record's
# parameters and the record (its index); a copy, its leaf's variables;
# any other function, a projection-like one included (Agda's index there
# only says which argument determines the ones before it), what its first
# clause matches.
# Lifting: a plain function takes every Pi of its type as a parameter, not
# only those its clauses bind (`step-≈-⟩ = forward …` binds none of its
# points; `flip f = λ y x → …` binds f).  Its body is then applied to the
# extra parameters (act.lift.app) and a call fills them all (a partial one
# is eta-expanded), so the quantity pass may erase a lifted parameter its
# body never uses, as it does a header's: a chain's points are then dead
# where they are passed.  Not lifted: projections and projection-like
# functions, copies, copattern definitions, type-valued definitions, and a
# definition without clauses.
def act.pats.proj(ps: A.Ag) -> Bool:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      True{}
    case A.AgPArg{i, x, p, rest}:
      act.pats.proj(rest)
    case _:
      False{}

def act.cls.liftable(cls: A.Ag) -> Bool:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      Bool.not(act.pats.proj(ps))
    case _:
      False{}

def act.lift.ar(+n: Nat, +m: Nat, ok: Bool) -> Nat:
  match ok:
    case True{}:
      Bool.pick(Nat, Nat.is_lt(n, m), m, n)
    case False{}:
      n

def act.sym.fun(cp: Bool, srt: Bool, tl: Bool, p: A.AgProj, +cls: A.Ag, tree: A.Ag, +mo: List<&2, U32>, +nm: List<&2, U32>, +ms: List<&2, ActM>, b: ActB) -> ActSym:
  match cp p:
    case True{} p:
      act.sym.copy(act.copy.of(tree), mo, nm, ms, b)
    case False{} A.AgPrOf{Some{r}, o, ix}:
      ActSym{mo, nm, A.AkFunction{}, ms, ix, b, act.opaque.mark(srt), Nil{}, None{}}
    case False{} A.AgPrOf{None{}, o, ix}:
      ActSym{mo, nm, A.AkFunction{}, ms, act.cls.arity(cls), b, Nil{}, Nil{}, None{}}
    case False{} A.AgPrNone{}:
      ActSym{mo, nm, A.AkFunction{}, ms, act.lift.ar(act.cls.arity(cls), List.length(&2, ActM, ms), Bool.and(Bool.not(tl), act.cls.liftable(cls))), b, Nil{}, Nil{}, None{}}

def act.con.name.of(un: Bool, +nm: List<&2, U32>) -> List<&2, U32>:
  match un:
    case True{}:
      List.take(&2, U32, nm, Nat.sub(S.len(nm), 12n))
    case False{}:
      nm

# a record's unnamed constructor is R.constructor: its Bend name is R's
def act.con.name(+nm: List<&2, U32>) -> List<&2, U32>:
  act.con.name.of(S.suffix(nm, S.b(".constructor")), nm)

# A name's local part: its printed name without the module's, each part
# made a Bend identifier (ToBend/Names.bend), joined by dots.
def act.parts(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> Nil{}:
      S.b(N.tnm.part(S.str(h)))
    case h <> t:
      List.append(&2, U32, S.b(N.tnm.part(S.str(h))), 46 <> act.parts(t))

def act.local.of(here: Bool, +top: List<&2, U32>, +qs: List<&2, U32>) -> List<&2, U32>:
  match here:
    case True{}:
      act.parts(S.split(List.drop(&2, U32, qs, 1n+S.len(top)), 46))
    case False{}:
      act.parts(S.split(qs, 46))

def act.local(+top: List<&2, U32>, +qs: List<&2, U32>) -> List<&2, U32>:
  act.local.of(S.prefix(qs, List.append(&2, U32, top, 46 <> Nil{})), top, qs)

# A type-valued function whose case tree is one leaf headed by a variable
# (a module parameter: `_∙_ IdempotentOn x = (x ∙ x) ≈ x` over `_≈_`) uses
# its parameters live in its body, which Bend checks as code; inlined where
# it is used, its body sits in a type, a dead position.  So its symbol is
# made a copy (inlined, not emitted).
def act.var.head(t: A.Ag) -> Bool:
  match t:
    case A.AgVar{i, x, es}:
      True{}
    case _:
      False{}

def act.inl.d(srt: Bool, d: A.AgD) -> Bool:
  match srt d:
    case True{} A.AgDFun{A.AgPrNone{}, r, w, e, t, mu, cls, A.AgDone{xs, body}}:
      act.var.head(body)
    case _ _:
      False{}

def act.tel.len(t: A.Ag) -> Nat:
  match t:
    case A.AgTel{x, i, ty, rest}:
      1n+act.tel.len(rest)
    case _:
      0n

# A data type or record made by module application is the original applied
# to the module's arguments, which its clause says (agda-export writes it
# explicitly from format 2.1): inlined where used, as a function copy is.
# The clause's variables are its telescope's, in order.
def act.tel.n(t: A.Ag) -> Nat:
  match t:
    case A.AgStored{x}:
      act.tel.len(x)
    case t:
      act.tel.len(t)

def act.copy.cl(cp: Bool, cl: A.Ag) -> Maybe<&2, ActCopy>:
  match cp cl:
    case True{} A.AgCl{tel, ps, body, ty, ca, rest}:
      Some{ActCopy{act.tel.n(tel), body}}
    case _ _:
      None{}

# a constructor made by module application: the original it copies (terms
# and patterns name the copy; Bend has only the original)
def act.con.src.d(cp: Bool, d: A.AgD) -> Maybe<&2, A.AgQ>:
  match cp d:
    case True{} A.AgDCon{dq, p, ar, ck, src}:
      Some{src}
    case _ _:
      None{}

def act.con.src(d: A.AgDecl) -> Maybe<&2, A.AgQ>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, dd}:
      act.con.src.d(act.flag(A.AkCopy{}, fl), dd)

# Indexed families: Bend has none, so an index is one more (erased) type
# parameter and each constructor carries an equation per index, {i == t},
# t the index its Agda type ends at (Reflects A true: {b == True{} :
# Bool}).  A constructor applied passes {==} for each; a pattern binds them.
# A type after its Pis.
def act.target(t: A.Ag) -> A.Ag:
  match t:
    case A.AgEl{s, A.AgPi{i, x, a, d, b}}:
      act.target(b)
    case t:
      t

def act.es.len(es: A.Ag) -> Nat:
  match es:
    case A.AgEApp{i, t, rest}:
      1n+act.es.len(rest)
    case _:
      0n

# the arguments of a spine after its first n
def act.es.after(n: Nat, es: A.Ag) -> A.Ag:
  match n es:
    case 1n+p A.AgEApp{i, t, rest}:
      act.es.after(p, rest)
    case _ es:
      es

def act.ixs.target(+pars: Nat, t: A.Ag) -> Nat:
  match t:
    case A.AgEl{s, A.AgDef{q, es}}:
      act.es.len(act.es.after(pars, es))
    case _:
      0n

# a constructor's index count: its type's target's arguments after the
# data type's parameters (0 for any other definition)
def act.ixs.of(d: A.AgD, t: A.Ag) -> Nat:
  match d:
    case A.AgDCon{dq, +pars, ar, ck, src}:
      act.ixs.target(pars, act.target(t))
    case _:
      0n

# a constructor's equation fields, by name: their number, and the index
# each equates, by its head (ix_eqz, ix_eqs: zero, suc; ix_eqt, ix_eqf: true,
# false; ix_eqv: a variable; ix_eqn: another term) and, for suc^k of one of
# the constructor's own arguments (k >= 0), "_k<k>_f<f>" (f: the argument's
# place, from 1).  An absurd pattern on the family reads the head
# (act.abs.fam), a dotted field the shape (act.ds).
def act.ix.tag(b: ActB) -> String:
  match b:
    case AbZero{}:
      "ix_eqz"
    case AbSuc{}:
      "ix_eqs"
    case AbTrue{}:
      "ix_eqt"
    case AbFalse{}:
      "ix_eqf"
    case _:
      "ix_eqn"

# a constructor's: another constructor's head is ix_eqc:KEY (its key), so
# an absurd pattern can refute a clash with it (act.abs.lm)
def act.ix.ctag(b: ActB, +q: A.AgQ) -> String:
  match b:
    case AbNone{}:
      "ix_eqc:" ++ act.key(q)
    case b:
      act.ix.tag(b)

def act.ix.is.suc(b: ActB) -> Bool:
  match b:
    case AbSuc{}:
      True{}
    case _:
      False{}

# the place (from 1) among a constructor's own arguments of de Bruijn i in
# its type's target (rds: its Pis innermost first, whether each binds: a
# non-dependent one binds no variable; pars of them the data type's
# parameters); 0 when i is a parameter or no binder
def act.ix.at(rds: List<&2, Bool>, i: Nat, +at: Nat) -> Maybe<&2, Nat>:
  match rds i:
    case Nil{} _:
      None{}
    case True{} <> t 0n:
      Some{at}
    case True{} <> t 1n+p:
      act.ix.at(t, p, 1n+at)
    case False{} <> t i:
      act.ix.at(t, i, 1n+at)

def act.ix.fld.of(m: Maybe<&2, Nat>, +tot: Nat, +pars: Nat) -> Nat:
  match m:
    case None{}:
      0n
    case Some{at}:
      +pos = Nat.sub(Nat.sub(tot, 1n), at)
      Bool.pick(Nat, Nat.is_le(pars, pos), 1n+Nat.sub(pos, pars), 0n)

def act.ix.fld(i: Nat, +rds: List<&2, Bool>, +pars: Nat) -> Nat:
  act.ix.fld.of(act.ix.at(rds, i, 0n), List.length(&2, Bool, rds), pars)

def act.ix.var(i: Nat, +k: Nat, +tot: List<&2, Bool>, +pars: Nat) -> String:
  +f = act.ix.fld(i, tot, pars)
  Bool.pick(String, Nat.is_eq(f, 0n), "", "_k" ++ Nat.show(k) ++ "_f" ++ Nat.show(f))

def act.ix.shape(t: A.Ag, +k: Nat, +tot: List<&2, Bool>, +pars: Nat) -> String:
  match t:
    case A.AgVar{+i, x, A.AgENil{}}:
      act.ix.var(i, k, tot, pars)
    case A.AgCon{q, o, A.AgEApp{i, a, A.AgENil{}}}:
      Bool.pick(String, act.ix.is.suc(act.builtin(act.qs(q))), act.ix.shape(a, 1n+k, tot, pars), "")
    case _:
      ""

# another constructor's arguments, after its key: "/f" each, f the place of
# the constructor's own argument it is (0 for any other term), so a case
# can write the index with the fields its pattern binds (act.cq)
def act.ix.cargs(es: A.Ag, +tot: List<&2, Bool>, +pars: Nat) -> String:
  match es:
    case A.AgEApp{i, A.AgVar{+v, x, A.AgENil{}}, rest}:
      "/" ++ Nat.show(act.ix.fld(v, tot, pars)) ++ act.ix.cargs(rest, tot, pars)
    case A.AgEApp{i, t, rest}:
      "/0" ++ act.ix.cargs(rest, tot, pars)
    case _:
      ""

def act.ix.cargs.of(b: ActB, es: A.Ag, +tot: List<&2, Bool>, +pars: Nat) -> String:
  match b:
    case AbNone{}:
      act.ix.cargs(es, tot, pars)
    case _:
      ""

def act.ix.head(t: A.Ag, +tot: List<&2, Bool>, +pars: Nat) -> String:
  match t:
    case A.AgCon{+q, o, A.AgEApp{+i, +a, A.AgENil{}}}:
      +b = act.builtin(act.qs(q))
      act.ix.ctag(b, q) ++ Bool.pick(String, act.ix.is.suc(b), act.ix.shape(a, 1n, tot, pars), act.ix.cargs.of(b, A.AgEApp{i, a, A.AgENil{}}, tot, pars))
    case A.AgCon{+q, o, es}:
      +b = act.builtin(act.qs(q))
      act.ix.ctag(b, q) ++ act.ix.cargs.of(b, es, tot, pars)
    case A.AgLit{A.AgLNat{s}}:
      Bool.pick(String, S.eq(s, S.b("0")), "ix_eqz", "ix_eqs")
    case A.AgVar{+i, x, A.AgENil{}}:
      "ix_eqv" ++ act.ix.var(i, 0n, tot, pars)
    case _:
      "ix_eqn"

def act.ix.heads(es: A.Ag, +tot: List<&2, Bool>, +pars: Nat) -> List<&2, String>:
  match es:
    case A.AgEApp{i, t, rest}:
      act.ix.head(t, tot, pars) <> act.ix.heads(rest, tot, pars)
    case _:
      Nil{}

# a type's Pis, innermost first: whether each binds a variable
def act.pis.rds(t: A.Ag, acc: List<&2, Bool>) -> List<&2, Bool>:
  match t:
    case A.AgEl{s, A.AgPi{i, x, a, d, b}}:
      act.pis.rds(b, d <> acc)
    case _:
      acc

def act.ixs.heads.target(+pars: Nat, +tot: List<&2, Bool>, t: A.Ag) -> List<&2, String>:
  match t:
    case A.AgEl{s, A.AgDef{q, es}}:
      act.ix.heads(act.es.after(pars, es), tot, pars)
    case _:
      Nil{}

def act.ixs.heads(d: A.AgD, +t: A.Ag) -> List<&2, String>:
  match d:
    case A.AgDCon{dq, +pars, ar, ck, src}:
      act.ixs.heads.target(pars, act.pis.rds(t, Nil{}), act.target(t))
    case _:
      Nil{}

def act.sym.d(d: A.AgD, cp: Bool, srt: Bool, tl: Bool, +mo: List<&2, U32>, +nm: List<&2, U32>, +ms: List<&2, ActM>, b: ActB, ixh: List<&2, String>) -> ActSym:
  match d:
    case A.AgDFun{p, r, w, e, t, mu, cls, tree}:
      act.sym.fun(cp, srt, tl, p, cls, tree, mo, nm, ms, b)
    case A.AgDRec{+pars, c, named, ind, fs, tel, eta, pm, rcl}:
      ActSym{mo, nm, A.AkRecord{}, ms, pars, b, act.keys(fs), act.con.name(act.local(mo, act.qs(c))), act.copy.cl(cp, rcl)}
    case A.AgDData{+pars, +ixs, cs, s, dcl}:
      ActSym{mo, nm, A.AkData{}, ms, Nat.add(pars, ixs), b, act.keys(cs), Nil{}, act.copy.cl(cp, dcl)}
    case A.AgDCon{+dq, +pars, ar, ck, src}:
      ActSym{mo, act.con.name(nm), A.AkConstructor{}, act.ms.live(act.drop.n(pars, ms)), ar, b, ixh, S.b(act.key(dq)), None{}}
    case A.AgDPost{}:
      ActSym{mo, nm, A.AkPostulate{}, ms, 0n, b, Nil{}, Nil{}, None{}}
    case A.AgDPrim{n, cls, tree}:
      ActSym{mo, nm, A.AkPrimitive{}, ms, act.cls.arity(cls), b, Nil{}, Nil{}, None{}}
    case A.AgDOther{x}:
      ActSym{mo, nm, A.AkWord{}, ms, 0n, b, Nil{}, Nil{}, None{}}

def act.role.pick(b: ActB, lv: Bool) -> ActB:
  match b lv:
    case AbNone{} True{}:
      AbLevel{}
    case b _:
      b

def act.role(+qs: List<&2, U32>, lv: Bool) -> ActB:
  act.role.pick(act.builtin(qs), lv)

# a module's file under src/: its name's parts, each a plain name
def act.path.parts(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      S.b(".bend")
    case h <> Nil{}:
      List.append(&2, U32, S.b(N.tnm.path(S.str(h))), S.b(".bend"))
    case h <> t:
      List.append(&2, U32, S.b(N.tnm.path(S.str(h))), 47 <> act.path.parts(t))

def act.path(+m: List<&2, U32>) -> List<&2, U32>:
  act.path.parts(S.split(m, 46))

# Headers ------------------------------------------------------------------------

# A def's parameters from the first n Pis of its type, the rest of the type
# as its result, the context they leave, and every parameter's entry in
# order (ents: a non-dependent Pi's parameter binds no variable of the
# context, but a clause's pattern still stands for it; a dropped one is
# the level marker); ok is False when the type has fewer Pis than n.
type ActPs is Data:
  ActPs{ps: List<&2, T.BParam>, ret: T.Bt, ctx: List<&2, T.Bt>, ents: List<&2, T.Bt>, ok: Bool}

def act.entry(m: ActM, +nm: List<&2, U32>) -> T.Bt:
  match m:
    case AmDrop{}:
      act.level()
    case _:
      T.BtVar{nm}

def act.params.put(m: ActM, +nm: List<&2, U32>, ty: T.Bt, r: ActPs) -> ActPs:
  match m r:
    case AmDrop{} ActPs{ps, ret, ctx, es, ok}:
      ActPs{ps, ret, ctx, act.level() <> es, ok}
    case m ActPs{ps, ret, ctx, es, ok}:
      ActPs{T.BParam{act.bmode(m), nm, ty} <> ps, ret, ctx, T.BtVar{nm} <> es, ok}

def act.unfold(+env: ActEnv, q: A.AgQ, +es: A.Ag) -> A.Ag:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(q))), es)

# whether a TYPE ends in a sort once the type-valued definitions it ends in
# are opened (`_≉_ : Rel A ℓ` is a relation: Rel opens to A -> A -> Set)
def act.ends.sort.u(fuel: Nat, t: A.Ag, +unf: Map<&2, ActCopy>) -> Bool:
  match fuel t:
    case f A.AgEl{s, x}:
      act.ends.sort.u(f, x, unf)
    case f A.AgPi{i, x, a, d, b}:
      act.ends.sort.u(f, b, unf)
    case f A.AgSort{s}:
      True{}
    case 1n+f A.AgDef{+q, +es}:
      act.ends.sort.u(f, act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(q))), es), unf)
    case _ _:
      False{}

# the modes of every Pi of a TYPE, the Pis of the type-valued definitions it
# ends in included (sym : Symmetric _≈_ takes {x y} after the record: both
# erased, as Symmetric opens to them), so a call keeps those arguments dead
def act.modes.u(fuel: Nat, t: A.Ag, +tylevel: Bool, +tab: Map<&2, ActSym>, +unf: Map<&2, ActCopy>) -> List<&2, ActM>:
  match fuel t:
    case f A.AgEl{s, x}:
      act.modes.u(f, x, tylevel, tab, unf)
    case f A.AgPi{i, x, +a, +d, b}:
      act.mode(i, a, Bool.or(tylevel, act.opaque.dep(d, a, tab, unf))) <> act.modes.u(f, b, tylevel, tab, unf)
    case f A.AgStored{x}:
      act.modes.u(f, x, tylevel, tab, unf)
    case 1n+f A.AgDef{+q, +es}:
      act.modes.u(f, act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(q))), es), tylevel, tab, unf)
    case _ _:
      Nil{}

# Whether a definition is type-valued (every Pi erased): its type ends in a
# sort once the type-valued definitions it ends in are opened (`_⊓_ : PT A B
# → PT A B → PT A B` is a predicate transformer: its P and Q are used only
# in dead places, and live they would make X a copy), but a record field's
# projection by its own type only, as the field's Bend type has it
# (`_≈_ : Rel (A ⇒ B) e` opens to two morphisms the field takes live;
# erased, a call's arguments were dead, so Copy left CommutativeSquare's
# f g h i erased where the body uses them live, and Bend refused it).
def act.tylevel(d: A.AgD, +ty: A.Ag, +unf: Map<&2, ActCopy>) -> Bool:
  match d:
    case A.AgDFun{A.AgPrOf{Some{r}, o, ix}, rs, w, e, t, mu, cls, tree}:
      act.ends.sort(ty)
    case _:
      act.ends.sort.u(8n, ty, unf)

# A definition's entry, given its module and its (unique) Bend name.
def act.sym.of(+mo: List<&2, U32>, +nm: List<&2, U32>, d: A.AgDecl, +tab: Map<&2, ActSym>, +unf: Map<&2, ActCopy>) -> ActSym:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, +fl, lang, +ty, +dd}:
      act.sym.d(dd, Bool.or(act.flag(A.AkCopy{}, fl), act.inl.d(act.ends.sort(ty), dd)), act.ends.sort(ty), act.tylevel(dd, ty, unf), mo, nm, act.modes.u(8n, ty, act.tylevel(dd, ty, unf), tab, unf), act.role(act.qs(q), act.ends.level(ty)), act.ixs.heads(dd, ty))

# seen: the names this header has given so far (a non-dependent Pi's
# parameter is in no context, but its name is taken)
def act.params.go(fuel: Nat, n: Nat, t: A.Ag, ms: List<&2, ActM>, +ctx: List<&2, T.Bt>, +seen: List<&2, List<&2, U32>>, +env: ActEnv, +renv: ActEnv) -> ActPs:
  match fuel n t ms:
    case f 0n t ms:
      ActPs{Nil{}, act.t(t, ctx, renv), ctx, Nil{}, True{}}
    case f 1n+p A.AgEl{s, A.AgPi{i, +x, a, d, b}} +m <> mt:
      +nm = act.fresh.in(x, ctx, seen)
      act.params.put(m, nm, act.t(a, ctx, env), act.params.go(f, p, b, mt, act.bind(d, act.entry(m, nm), ctx), nm <> seen, env, renv))
    case f 1n+p A.AgEl{s, A.AgPi{i, +x, +a, +d, b}} Nil{}:
      +nm = act.fresh.in(x, ctx, seen)
      +m = act.mode(i, a, act.opaque.env(d, a, env))
      act.params.put(m, nm, act.t(a, ctx, env), act.params.go(f, p, b, Nil{}, act.bind(d, act.entry(m, nm), ctx), nm <> seen, env, renv))
    case 1n+g 1n+p A.AgEl{s, A.AgDef{+q, +es}} ms:
      act.params.go(g, 1n+p, A.AgEl{s, act.inline(1024n, act.unfold(env, q, es), env)}, ms, ctx, seen, env, renv)
    case f 1n+p t ms:
      ActPs{Nil{}, act.todo("a type with fewer Pis than its clauses take parameters"), ctx, Nil{}, False{}}

# The fuel bounds the unfoldings a header may take (each a type-valued
# definition opened to reach the Pis the clauses take).
def act.params(fuel: Nat, n: Nat, t: A.Ag, ms: List<&2, ActM>, +ctx: List<&2, T.Bt>, +env: ActEnv) -> ActPs:
  act.params.go(fuel, n, t, ms, ctx, Nil{}, env, env)

# a function's header: its parameters' types read under "sig!" (act.sig.env),
# its result type (what the clauses return, Pis the clauses do not take
# included: Consequences' anon.total⇒refl) in the plain environment
def act.params.s(fuel: Nat, n: Nat, t: A.Ag, ms: List<&2, ActM>, +ctx: List<&2, T.Bt>, +env: ActEnv, +renv: ActEnv) -> ActPs:
  act.params.go(fuel, n, t, ms, ctx, Nil{}, env, renv)

# Clauses ------------------------------------------------------------------------

# a pattern variable's binding: its position in the clause's telescope and
# the Bend term it stands for
type ActBind is Data:
  ActBind{pos: Nat, t: T.Bt}
  # a dotted field of a top constructor pattern, bound as x (act.ds); not
  # a binding of pos unless the case makes it one
  ActBDot{pos: Nat, x: List<&2, U32>}

# a translated pattern (or pattern spine), its bindings, and whether the
# clause is left out: it holds an absurd pattern, or a cubical one (the
# clauses --cubical-compatible generates beside the user's, FORMAT.md)
type ActPat is Data:
  ActPat{p: T.Bt, bs: List<&2, ActBind>, absurd: Bool}

def act.tel.hints(t: A.Ag) -> List<&2, List<&2, U32>>:
  match t:
    case A.AgTel{x, i, ty, rest}:
      act.hint(x) <> act.tel.hints(rest)
    case _:
      Nil{}

def act.count(+x: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(Bool.pick(Nat, S.eq(h, x), 1n, 0n), act.count(x, t))

def act.nth.b(n: Nat, xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match n xs:
    case 0n h <> t:
      h
    case 1n+p h <> t:
      act.nth.b(p, t)
    case _ Nil{}:
      S.b("x")

def act.pv.of(plain: Bool, +h: List<&2, U32>, +pos: Nat) -> List<&2, U32>:
  match plain:
    case True{}:
      h
    case False{}:
      List.append(&2, U32, h, 95 <> S.b(Nat.show(pos)))

def act.pv.name.of(+h: List<&2, U32>, +pos: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>) -> List<&2, U32>:
  act.pv.of(Bool.and(Bool.and(Nat.is_eq(act.count(h, hints), 1n), Bool.not(act.used(h, pnames))), Bool.not(S.eq(h, S.b("x")))), h, pos)

# A pattern variable's name: its telescope hint when that is unique among
# the telescope's hints and no parameter's name, else the hint and its
# position (x_3).
def act.pv.name(+pos: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>) -> List<&2, U32>:
  act.pv.name.of(act.nth.b(pos, hints), pos, hints, pnames)

def act.pat.cat(a: ActPat, b: ActPat) -> ActPat:
  match a b:
    case ActPat{p, bs, ab} ActPat{q, cs, ac}:
      ActPat{T.BtArgs{p, q}, List.append(&2, ActBind, bs, cs), Bool.or(ab, ac)}

def act.pat.first(a: T.Bt) -> T.Bt:
  match a:
    case T.BtArgs{h, t}:
      h
    case _:
      act.todo("suc with no pattern")

# an equation field's pattern: a placeholder the case names (act.eq.deep)
def act.wilds(fs: List<&2, String>) -> List<&2, T.Bt>:
  match fs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BtPv{T.BmLive{}, S.b(h)} <> act.wilds(t)

# a spine with more patterns after it: one for each equation field
def act.spine.wild(sp: T.Bt, fs: List<&2, String>) -> T.Bt:
  match sp:
    case T.BtArgs{a, rest}:
      T.BtArgs{a, act.spine.wild(rest, fs)}
    case _:
      T.tba.args(act.wilds(fs))

def act.pat.con.kind(k: A.AgKw, +ref: List<&2, U32>, fs: List<&2, String>, sub: T.Bt) -> T.Bt:
  match k:
    case A.AkConstructor{}:
      T.BtCon{ref, act.spine.wild(sub, fs)}
    case _:
      T.BtTodo{List.append(&2, U32, S.b("a constructor pattern the symbol table does not have: "), ref)}

# A refl inside a constructor pattern (act.nrf): a variable, x_i_rfl once
# act.eq.deep names it by its place
def act.nrf.ph() -> List<&2, U32>:
  S.b("a2b_rfl")

def act.nrf.is.ph(+nm: List<&2, U32>) -> Bool:
  S.eq(nm, S.b("a2b_rfl"))

def act.pat.con.p(s: ActSym, +env: ActEnv, sub: T.Bt) -> T.Bt:
  match s:
    case ActSym{m, n, k, ms, ar, AbZero{}, fs, c, cp}:
      T.BtNat{S.b("0")}
    case ActSym{m, n, k, ms, ar, AbSuc{}, fs, c, cp}:
      T.BtSucc{act.pat.first(sub)}
    case ActSym{m, n, k, ms, ar, AbTrue{}, fs, c, cp}:
      T.BtCon{S.b("True"), T.BtANil{}}
    case ActSym{m, n, k, ms, ar, AbFalse{}, fs, c, cp}:
      T.BtCon{S.b("False"), T.BtANil{}}
    case ActSym{m, n, k, ms, ar, AbTt{}, fs, c, cp}:
      T.BtCon{S.b("Unit"), T.BtANil{}}
    case ActSym{m, n, k, ms, ar, AbRefl{}, fs, c, cp}:
      T.BtPv{T.BmLive{}, act.nrf.ph()}
    case ActSym{+m, +n, k, ms, ar, b, fs, c, cp}:
      act.pat.con.kind(k, act.ref.of(act.is.here(env, m), env, m, n), fs, sub)

def act.pat.con(s: ActSym, +env: ActEnv, sub: ActPat) -> ActPat:
  match sub:
    case ActPat{p, bs, ab}:
      ActPat{act.pat.con.p(s, env, p), bs, ab}

# A pattern, or a spine of them (a constructor's own arguments), with the
# bindings of its variables.  n is the telescope's length (a variable's
# index counts from its end).
def act.pat(p: A.Ag, +n: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv) -> ActPat:
  match p:
    case A.AgPArg{i, x, q, rest}:
      act.pat.cat(act.pat(q, n, hints, pnames, env), act.pat(rest, n, hints, pnames, env))
    case A.AgPEnd{}:
      ActPat{T.BtANil{}, Nil{}, False{}}
    case A.AgPVar{x, +ix, o}:
      +pos = Nat.sub(Nat.sub(n, 1n), ix)
      +nm = act.pv.name(pos, hints, pnames)
      ActPat{T.BtPv{T.BmLive{}, nm}, [ActBind{pos, T.BtVar{nm}}], A.aas.kw.eq(o, A.AkAbsurd{})}
    case A.AgPDot{t}:
      ActPat{T.BtWild{}, Nil{}, False{}}
    case A.AgPCon{+q, r, fo, ps}:
      act.pat.con(act.sym(env, q), env, act.pat(ps, n, hints, pnames, env))
    case A.AgPLit{A.AgLNat{s}}:
      ActPat{T.BtNat{s}, Nil{}, False{}}
    case A.AgRaw{c, x}:
      ActPat{T.BtWild{}, Nil{}, True{}}
    case _:
      ActPat{act.todo("a pattern not translated (a literal other than a Nat, a copattern)"), Nil{}, False{}}

def act.pat.dot(t: A.Ag, +n: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>) -> ActPat:
  match t:
    case A.AgVar{+ix, x, A.AgENil{}}:
      +pos = Nat.sub(Nat.sub(n, 1n), ix)
      +nm = List.append(&2, U32, act.pv.name(pos, hints, pnames), S.b("_dot"))
      ActPat{T.BtPv{T.BmLive{}, nm}, [ActBDot{pos, nm}], False{}}
    case _:
      ActPat{T.BtWild{}, Nil{}, False{}}

# a top constructor pattern's own arguments: a dotted variable is bound
# (act.ds), the rest as act.pat
def act.pat.subs(p: A.Ag, +n: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv) -> ActPat:
  match p:
    case A.AgPArg{i, x, A.AgPDot{t}, rest}:
      act.pat.cat(act.pat.dot(t, n, hints, pnames), act.pat.subs(rest, n, hints, pnames, env))
    case A.AgPArg{i, x, q, rest}:
      act.pat.cat(act.pat(q, n, hints, pnames, env), act.pat.subs(rest, n, hints, pnames, env))
    case p:
      act.pat(p, n, hints, pnames, env)

def act.pat.top(p: A.Ag, +n: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv) -> ActPat:
  match p:
    case A.AgPCon{+q, r, fo, ps}:
      act.pat.con(act.sym(env, q), env, act.pat.subs(ps, n, hints, pnames, env))
    case p:
      act.pat(p, n, hints, pnames, env)

def act.top.var(p: A.Ag, +n: Nat, ent: T.Bt) -> List<&2, ActBind>:
  match p:
    case A.AgPVar{x, +ix, o}:
      [ActBind{Nat.sub(Nat.sub(n, 1n), ix), ent}]
    case _:
      Nil{}

# A cubical pattern (pdef: the transpX and hcomp clauses
# --cubical-compatible generates beside the user's) at a parameter the
# match does not split leaves the clause out as one at a split parameter
# does (2026-10-29: `≤-reflexive {zero} refl`'s generated clauses put
# transpX at the refl, and their stored bodies became gaps).
def act.pat.cub(p: A.Ag) -> Bool:
  match p:
    case A.AgRaw{c, x}:
      True{}
    case _:
      False{}

def act.pat.ab(b: Bool, a: ActPat) -> ActPat:
  match a:
    case ActPat{p, cs, ab}:
      ActPat{p, cs, Bool.or(b, ab)}

def act.pat.add(bs: List<&2, ActBind>, a: ActPat) -> ActPat:
  match a:
    case ActPat{p, cs, ab}:
      ActPat{p, List.append(&2, ActBind, bs, cs), ab}

# A clause's patterns: at a parameter the match splits (scr), the pattern;
# at another, its variable stands for the parameter itself.  The result
# holds the patterns of the split parameters only.
def act.top(ps: A.Ag, scr: List<&2, Bool>, ents: List<&2, T.Bt>, +n: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv) -> ActPat:
  match ps scr ents:
    case A.AgPArg{i, x, q, rest} True{} <> st e <> et:
      act.pat.cat(act.pat(q, n, hints, pnames, env), act.top(rest, st, et, n, hints, pnames, env))
    case A.AgPArg{i, x, +q, rest} False{} <> st e <> et:
      act.pat.ab(act.pat.cub(q), act.pat.add(act.top.var(q, n, e), act.top(rest, st, et, n, hints, pnames, env)))
    case _ _ _:
      ActPat{T.BtANil{}, Nil{}, False{}}

# act.top, its top constructor patterns' dotted fields bound (act.ds)
# Dotted fields at one outer variable in two constructor patterns
# (`zip3 (x ∷ xs) (y ∷ ys) (z ∷ zs)`: n dotted at the second and the
# third): act.pat.dot names each n_dot; one in a later parameter's pattern
# than the first is n_dot_<its place> (act.sd binds and casts each).
def act.dd.sfx(+nm: List<&2, U32>, +seen: List<&2, List<&2, U32>>, +j: Nat) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, act.used(nm, seen), List.append(&2, U32, nm, S.b("_" ++ Nat.show(j))), nm)

def act.dd.ren.p(p: T.Bt, +seen: List<&2, List<&2, U32>>, +j: Nat) -> T.Bt:
  match p:
    case T.BtArgs{a, rest}:
      T.BtArgs{act.dd.ren.p(a, seen, j), act.dd.ren.p(rest, seen, j)}
    case T.BtCon{c, a}:
      T.BtCon{c, act.dd.ren.p(a, seen, j)}
    case T.BtSucc{a}:
      T.BtSucc{act.dd.ren.p(a, seen, j)}
    case T.BtPv{m, +nm}:
      T.BtPv{m, act.dd.sfx(nm, seen, j)}
    case p:
      p

def act.dd.ren.bs(bs: List<&2, ActBind>, +seen: List<&2, List<&2, U32>>, +j: Nat) -> List<&2, ActBind>:
  match bs:
    case Nil{}:
      Nil{}
    case ActBDot{p, +x} <> t:
      ActBDot{p, act.dd.sfx(x, seen, j)} <> act.dd.ren.bs(t, seen, j)
    case b <> t:
      b <> act.dd.ren.bs(t, seen, j)

def act.dd.olds(bs: List<&2, ActBind>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Nil{}
    case ActBDot{p, x} <> t:
      x <> act.dd.olds(t)
    case b <> t:
      act.dd.olds(t)

def act.dd.ren(a: ActPat, +seen: List<&2, List<&2, U32>>, +j: Nat) -> ActPat:
  match a:
    case ActPat{p, bs, ab}:
      ActPat{act.dd.ren.p(p, seen, j), act.dd.ren.bs(bs, seen, j), ab}

def act.dd.dots(a: ActPat) -> List<&2, List<&2, U32>>:
  match a:
    case ActPat{p, bs, ab}:
      act.dd.olds(bs)

def act.top.d(ps: A.Ag, scr: List<&2, Bool>, ents: List<&2, T.Bt>, +n: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +seen: List<&2, List<&2, U32>>, +j: Nat) -> ActPat:
  match ps scr ents:
    case A.AgPArg{i, x, q, rest} True{} <> st e <> et:
      +a = act.pat.top(q, n, hints, pnames, env)
      act.pat.cat(act.dd.ren(a, seen, j), act.top.d(rest, st, et, n, hints, pnames, env, List.append(&2, List<&2, U32>, seen, act.dd.dots(a)), 1n+j))
    case A.AgPArg{i, x, +q, rest} False{} <> st e <> et:
      act.pat.ab(act.pat.cub(q), act.pat.add(act.top.var(q, n, e), act.top.d(rest, st, et, n, hints, pnames, env, seen, 1n+j)))
    case _ _ _:
      ActPat{T.BtANil{}, Nil{}, False{}}

def act.bind.find(+pos: Nat, bs: List<&2, ActBind>) -> T.Bt:
  match bs:
    case Nil{}:
      act.todo("a pattern variable the clause does not bind (a dot or forced pattern)")
    case ActBind{+p, t} <> rest:
      Bool.pick(T.Bt, Nat.is_eq(p, pos), t, act.bind.find(pos, rest))
    case ActBDot{p, x} <> rest:
      act.bind.find(pos, rest)

# the body's context from the bindings: telescope position n-1 first
def act.ctx.of(k: Nat, +bs: List<&2, ActBind>) -> List<&2, T.Bt>:
  match k:
    case 0n:
      Nil{}
    case 1n+(+p):
      act.bind.find(p, bs) <> act.ctx.of(p, bs)

# Equations: Bend cannot match on an equation, so a clause matching refl
# (`sym refl = refl`, `cong f refl = refl`) is translated as a rewrite of
# the goal before its body.  Agda's match makes one side of the equation a
# dot pattern (that variable is gone from the clause); with e : {a == b},
# Bend's `%e : P` needs the goal to be P with b at the holes and leaves P
# with a there, so when the dotted variable d is b the rewrite is
# `%e : G[d := _]`, and when it is a, the reversed equation first
# (`e2 = Equal.sym(T, a, b, e)`, then `%e2 : G[d := _]`).  G is the case's
# goal: the def's result type with the case's patterns put for the
# parameters it splits.  A clause may hold several; each rewrites the goal
# the one before left.
type ActRw is Data:
  ActRw{rws: List<&2, T.Bt>, dots: List<&2, List<&2, U32>>}

def act.var.name(t: T.Bt) -> List<&2, U32>:
  match t:
    case T.BtVar{x}:
      x
    case _:
      S.b("r")

def act.rw.add(e: T.Bt, r: ActRw) -> ActRw:
  match r:
    case ActRw{rs, ds}:
      ActRw{e <> rs, ds}

def act.rw.dot(e: T.Bt, r: ActRw) -> ActRw:
  match r:
    case ActRw{rs, ds}:
      ActRw{rs, act.var.name(e) <> ds}

def act.is.refl(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, k, ms, ar, AbRefl{}, fs, c, cp}:
      True{}
    case _:
      False{}

def act.rw.refl(hit: Bool, e: T.Bt, r: ActRw) -> ActRw:
  match hit:
    case True{}:
      act.rw.add(e, r)
    case False{}:
      r

def act.rw.pat(p: A.Ag, +e: T.Bt, +env: ActEnv, r: ActRw) -> ActRw:
  match p:
    case A.AgPCon{+q, rec, fo, ps}:
      act.rw.refl(act.is.refl(act.sym(env, q)), e, r)
    case A.AgPDot{t}:
      act.rw.dot(e, r)
    case _:
      r

# a clause's top-level refl and dot patterns, by parameter
def act.rw.scan(ps: A.Ag, ents: List<&2, T.Bt>, +env: ActEnv) -> ActRw:
  match ps ents:
    case A.AgPArg{i, x, p, rest} +e <> et:
      act.rw.pat(p, e, env, act.rw.scan(rest, et, env))
    case _ _:
      ActRw{Nil{}, Nil{}}

# a pattern as the term it stands for
def act.pat.term(p: T.Bt) -> T.Bt:
  match p:
    case T.BtPv{m, x}:
      T.BtVar{x}
    case T.BtCon{c, a}:
      T.BtCon{c, act.pat.term(a)}
    case T.BtSucc{a}:
      T.BtSucc{act.pat.term(a)}
    case T.BtArgs{a, rest}:
      T.BtArgs{act.pat.term(a), act.pat.term(rest)}
    case p:
      p

def act.goal.put(t: T.Bt, +x: List<&2, U32>, +p: T.Bt, wild: Bool) -> T.Bt:
  match wild:
    case True{}:
      t
    case False{}:
      T.tba.subst(t, x, act.pat.term(p))

def act.wild(p: T.Bt) -> Bool:
  match p:
    case T.BtWild{}:
      True{}
    case _:
      False{}

# the def's result type with each split parameter replaced by the case's
# pattern for it (a catch-all leaves it as it is)
def act.goal(xs: List<&2, T.Bt>, ps: T.Bt, t: T.Bt) -> T.Bt:
  match xs ps:
    case x <> xt T.BtArgs{+p, rest}:
      act.goal(xt, rest, act.goal.put(t, act.var.name(x), p, act.wild(p)))
    case _ _:
      t

def act.param.ty(ps: List<&2, T.BParam>, +x: List<&2, U32>) -> T.Bt:
  match ps:
    case Nil{}:
      T.BtWild{}
    case T.BParam{m, +n, ty} <> t:
      Bool.pick(T.Bt, S.eq(n, x), ty, act.param.ty(t, x))

def act.dotted(t: T.Bt, +ds: List<&2, List<&2, U32>>) -> Bool:
  match t:
    case T.BtVar{x}:
      act.used(x, ds)
    case _:
      False{}

# One rewrite's plan: 0 none (no side of e is a dotted variable), 1 with
# e, 2 with e reversed (sym: the Equal.sym call, named e2); the motive P
# and the goal the rewrite leaves.
type ActStep is Data:
  ActStep{k: Nat, p: T.Bt, goal: T.Bt, sym: T.Bt, e2: List<&2, U32>}

# The side to mark in the goal: the dotted variable when the goal mentions
# it (the goal then says what the body proves of the other side), else
# the other side (the body's hypotheses mention the dotted one: `trans
# refl eq = eq` proves i ≡ k from eq : j ≡ k, so i becomes j).  Marking b
# rewrites with e; marking a, with e reversed.
def act.mark.b(rb: Bool, ra: Bool, inb: Bool, ina: Bool) -> Nat:
  match rb ra inb ina:
    case True{} _ True{} _:
      1n
    case True{} _ False{} True{}:
      2n
    case False{} True{} _ True{}:
      2n
    case False{} True{} True{} False{}:
      1n
    case _ _ _ _:
      0n

def act.occurs(+x: List<&2, U32>, +t: T.Bt) -> Bool:
  act.used(x, T.tba.refs(t, Nil{}))

# a variable's name, or none (a rewrite's evidence that is no variable)
def act.var.name.or(t: T.Bt) -> List<&2, U32>:
  match t:
    case T.BtVar{x}:
      x
    case _:
      Nil{}

# A step whose goal mentions neither side still rewrites when a parameter's
# type mentions the dotted side (`cast refl v i = v i`, v : Ar g → C at
# i : Ar f; agda-algebras' EqArgs): the motive is the goal, and the step
# generalizes those parameters (act.gen.ps), their types with the hole
# (2026-10-29).  ps.ment2: a parameter other than x and the evidence en
# whose type mentions x.
# another pattern's index evidence is not a parameter to generalize: its own
# step rewrites it (Fn.lookup's Fin.zero evidence under Vec.cons's)
def act.is.bteq(ty: T.Bt) -> Bool:
  match ty:
    case T.BtEq{t, a, b}:
      True{}
    case _:
      False{}

def act.ps.ment2(ps: List<&2, T.BParam>, +x: List<&2, U32>, +en: List<&2, U32>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case T.BParam{m, +y, +ty} <> t:
      Bool.or(Bool.and(Bool.and(Bool.and(Bool.not(S.eq(y, x)), Bool.not(S.eq(y, en))), Bool.not(act.is.bteq(ty))), act.occurs(x, ty)), act.ps.ment2(t, x, en))

def act.mark.p(k: Nat, rb: Bool, ra: Bool, pb: Bool, pa: Bool) -> Nat:
  match k rb ra pb pa:
    case 0n True{} _ True{} _:
      1n
    case 0n False{} True{} _ True{}:
      2n
    case k _ _ _ _:
      k

# with e a variable the rewrite is J (%e@e), so the goal it leaves has
# {==} for e as well as a for b
def act.step.k(k: Nat, +t: T.Bt, +a: T.Bt, +b: T.Bt, +e: T.Bt, +goal: T.Bt) -> ActStep:
  match k:
    case 1n:
      ActStep{1n, T.tba.subst(goal, act.var.name(b), T.BtWild{}), T.tba.subst(T.tba.subst(goal, act.var.name(b), a), act.var.name.or(e), T.BtRefl{}), T.BtWild{}, Nil{}}
    case 2n:
      ActStep{2n, T.tba.subst(goal, act.var.name(a), T.BtWild{}), T.tba.subst(goal, act.var.name(a), b), T.BtApp{T.BtVar{S.b("Equal.sym")}, T.tba.args([T.BtDead{t}, T.BtDead{a}, T.BtDead{b}, e])}, List.append(&2, U32, act.var.name(e), S.b("_sym"))}
    case _:
      ActStep{0n, T.BtWild{}, goal, T.BtWild{}, Nil{}}

def act.step.dir(+rb: Bool, +ra: Bool, +t: T.Bt, +a: T.Bt, +b: T.Bt, +e: T.Bt, +goal: T.Bt, +hps: List<&2, T.BParam>) -> ActStep:
  +en = act.var.name.or(e)
  act.step.k(act.mark.p(act.mark.b(rb, ra, act.occurs(act.var.name(b), goal), act.occurs(act.var.name(a), goal)), rb, ra, act.ps.ment2(hps, act.var.name(b), en), act.ps.ment2(hps, act.var.name(a), en)), t, a, b, e, goal)

def act.step(ty: T.Bt, +e: T.Bt, +ds: List<&2, List<&2, U32>>, +goal: T.Bt, +hps: List<&2, T.BParam>) -> ActStep:
  match ty:
    case T.BtEq{+t, +a, +b}:
      act.step.dir(act.dotted(b, ds), act.dotted(a, ds), t, a, b, e, goal, hps)
    case _:
      ActStep{0n, T.BtWild{}, goal, T.BtWild{}, Nil{}}

def act.step.goal(s: ActStep) -> T.Bt:
  match s:
    case ActStep{k, p, g, y, e2}:
      g

# J generalizes.  A rewrite %e@e : P at e : {a == b} (b the dotted side)
# is Bend's J, but only the goal is its motive: a parameter whose type
# mentions b or e (q : {b == z} in `assoc refl q r = refl`) keeps b in the
# body, where Agda's match on refl put a.  So, as Agda's unifier does, the
# motive abstracts those parameters (and the ones whose types mention
# those): the step is
#   {(%e@e : @q:Q[b := _] -> P; q => body) : @q:Q -> G}(q)
# The parameters: in telescope order, not e, b or a split one (a dotted
# one is: a later step's endpoint, as s in `splice-concat refl refl q`).
def act.any.of(ns: List<&2, List<&2, U32>>, +seen: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case +h <> t:
      Bool.or(act.used(h, seen), act.any.of(t, seen))

def act.drop.name(+y: List<&2, U32>, ns: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case +h <> t:
      List.append(&2, List<&2, U32>, Bool.pick(List<&2, List<&2, U32>>, S.eq(h, y), Nil{}, [h]), act.drop.name(y, t))

# whether t mentions a name of ns free (a Pi's or a lambda's binder hides
# its name in its body: B : @y:A -> {x == y : A} -> Type does not mention y)
def act.mentions(t: T.Bt, +ns: List<&2, List<&2, U32>>) -> Bool:
  match t:
    case T.BtVar{+x}:
      act.used(x, ns)
    case T.BtLam{m, +y, b}:
      act.mentions(b, act.drop.name(y, ns))
    case T.BtPi{m, +y, d, a, b}:
      Bool.or(act.mentions(a, ns), act.mentions(b, act.drop.name(y, ns)))
    case T.BtApp{f, a}:
      Bool.or(act.mentions(f, ns), act.mentions(a, ns))
    case T.BtArgs{a, rest}:
      Bool.or(act.mentions(a, ns), act.mentions(rest, ns))
    case T.BtTplArg{a}:
      act.mentions(a, ns)
    case T.BtDead{a}:
      act.mentions(a, ns)
    case T.BtCon{c, a}:
      act.mentions(a, ns)
    case T.BtTyApp{n, a}:
      act.mentions(a, ns)
    case T.BtEq{ty, a, b}:
      Bool.or(act.mentions(ty, ns), Bool.or(act.mentions(a, ns), act.mentions(b, ns)))
    case T.BtSucc{a}:
      act.mentions(a, ns)
    case T.BtAnn{a, ty}:
      Bool.or(act.mentions(a, ns), act.mentions(ty, ns))
    case T.BtExpr{e}:
      act.mentions(e, ns)
    case T.BtRw{e, p, b}:
      Bool.or(act.mentions(e, ns), Bool.or(act.mentions(p, ns), act.mentions(b, ns)))
    case T.BtLet{x, v, b}:
      Bool.or(act.mentions(v, ns), act.mentions(b, ns))
    case _:
      act.any.of(T.tba.refs(t, Nil{}), ns)

def act.gen.ps(ps: List<&2, T.BParam>, +skip: List<&2, List<&2, U32>>, +seen: List<&2, List<&2, U32>>) -> List<&2, T.BParam>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{+m, +x, +ty} <> t:
      +hit = Bool.and(Bool.not(act.used(x, skip)), act.mentions(ty, seen))
      List.append(&2, T.BParam, Bool.pick(List<&2, T.BParam>, hit, [T.BParam{m, x, ty}], Nil{}), act.gen.ps(t, skip, Bool.pick(List<&2, List<&2, U32>>, hit, x <> seen, seen)))

def act.gen.names(ps: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      x <> act.gen.names(t)

def act.gen.ty(ty: T.Bt, +b: List<&2, U32>, wild: Bool) -> T.Bt:
  match wild:
    case True{}:
      T.tba.subst(ty, b, T.BtWild{})
    case False{}:
      ty

# Pis over the generalized parameters: in the motive, b is the hole
def act.gen.pis(gs: List<&2, T.BParam>, +b: List<&2, U32>, +wild: Bool, t: T.Bt) -> T.Bt:
  match gs:
    case Nil{}:
      t
    case T.BParam{m, x, ty} <> r:
      T.BtPi{m, x, True{}, act.gen.ty(ty, b, wild), act.gen.pis(r, b, wild, t)}

def act.gen.lams(gs: List<&2, T.BParam>, b: T.Bt) -> T.Bt:
  match gs:
    case Nil{}:
      b
    case T.BParam{m, x, ty} <> r:
      T.BtLam{m, x, act.gen.lams(r, b)}

# each argument live: the lambda's body uses its binder, not the parameter,
# so this use is what tells Copy the parameter is live (an erased one used
# live inside becomes live, and the translation again writes its Pi live)
def act.gen.arg(m: T.BMode, x: List<&2, U32>) -> T.Bt:
  T.BtVar{x}

def act.gen.args(gs: List<&2, T.BParam>) -> List<&2, T.Bt>:
  match gs:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> r:
      act.gen.arg(m, x) <> act.gen.args(r)

def act.gen.none(gs: List<&2, T.BParam>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case _:
      False{}

# whether a clause's rest can be written inside a term (the generalizing
# step's lambda body, on one line): rewrites (a reversed one's let too) over
# an expression; a match cannot
def act.loose.ok(t: T.Bt) -> Bool:
  match t:
    case T.BtMatch{xs, cs}:
      False{}
    case T.BtRw{e, p, b}:
      act.loose.ok(b)
    case T.BtLet{x, v, T.BtRw{T.BtVar{y}, p, b}}:
      act.loose.ok(b)
    case T.BtLet{x, v, b}:
      False{}
    case _:
      True{}

def act.gen.wrap(none: Bool, +gs: List<&2, T.BParam>, e: T.Bt, p: T.Bt, +goal: T.Bt, +b: List<&2, U32>, inner: T.Bt) -> T.Bt:
  match none:
    case True{}:
      T.BtRw{e, p, inner}
    case False{}:
      T.BtExpr{T.BtApp{T.BtAnn{T.BtRw{e, act.gen.pis(gs, b, True{}, p), act.gen.lams(gs, inner)}, act.gen.pis(gs, b, False{}, goal)}, T.tba.args(act.gen.args(gs))}}

# the rewrite a step plans, in front of the rest (b: the dotted side's
# name, the motive's hole)
def act.step.wrap(s: ActStep, e: T.Bt, +goal: T.Bt, +gs: List<&2, T.BParam>, +b: List<&2, U32>, +inner: T.Bt) -> T.Bt:
  match s:
    case ActStep{0n, p, g, y, e2}:
      inner
    case ActStep{1n, p, g, y, e2}:
      act.gen.wrap(Bool.or(act.gen.none(gs), Bool.not(act.loose.ok(inner))), gs, e, p, goal, b, inner)
    case ActStep{3n, p, g, y, e2}:
      act.gen.wrap(Bool.or(act.gen.none(gs), Bool.not(act.loose.ok(inner))), gs, e, p, goal, b, inner)
    case ActStep{k, p, g, y, +e2}:
      T.BtLet{e2, y, act.gen.wrap(Bool.or(act.gen.none(gs), Bool.not(act.loose.ok(inner))), gs, T.BtVar{e2}, p, goal, b, inner)}

def act.step.kind(s: ActStep) -> Nat:
  match s:
    case ActStep{k, p, g, y, e2}:
      k

def act.eq.rhs(ty: T.Bt) -> List<&2, U32>:
  match ty:
    case T.BtEq{t, a, b}:
      act.var.name(b)
    case _:
      Nil{}

def act.eq.lhs(ty: T.Bt) -> T.Bt:
  match ty:
    case T.BtEq{t, a, b}:
      a
    case _:
      T.BtWild{}

# a step's hole: b's name for a rewrite with e, a's for one with e reversed
# (none for no rewrite); and what the hole's variable becomes after it
def act.step.hole(k: Nat, +ty: T.Bt) -> List<&2, U32>:
  match k:
    case 1n:
      act.eq.rhs(ty)
    case 3n:
      act.eq.rhs(ty)
    case 2n:
      act.var.name(act.eq.lhs(ty))
    case _:
      Nil{}

def act.eq.rhs.t(ty: T.Bt) -> T.Bt:
  match ty:
    case T.BtEq{t, a, b}:
      b
    case _:
      T.BtWild{}

def act.step.fill(k: Nat, +ty: T.Bt) -> T.Bt:
  match k:
    case 2n:
      act.eq.rhs.t(ty)
    case _:
      act.eq.lhs(ty)

# with e itself the evidence (J on e), e is {==} after the step
def act.step.ev(k: Nat, +en: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 1n:
      en
    case 3n:
      en
    case _:
      Nil{}

# A reversed step (a dotted: e : {a == b}, Agda put b for a) whose goal or
# a parameter's type mentions e itself cannot go through Equal.sym (the
# motive would have sym(sym(e)) for e).  It is J on e, b the hole (3):
# the goal at b := a, e := {==}, and the body, written with b (Agda's
# survivor), has a for b.
def act.ps.mention(ps: List<&2, T.BParam>, +x: List<&2, U32>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case T.BParam{m, +y, +ty} <> t:
      Bool.or(Bool.and(Bool.not(S.eq(y, x)), act.occurs(x, ty)), act.ps.mention(t, x))

def act.eq.rhs.or(ty: T.Bt) -> List<&2, U32>:
  match ty:
    case T.BtEq{t, a, b}:
      act.var.name.or(b)
    case _:
      Nil{}

def act.step.three(+ty: T.Bt, +en: List<&2, U32>, +goal: T.Bt) -> ActStep:
  ActStep{3n, T.tba.subst(goal, act.eq.rhs(ty), T.BtWild{}), T.tba.subst(T.tba.subst(goal, act.eq.rhs(ty), act.eq.lhs(ty)), en, T.BtRefl{}), T.BtWild{}, Nil{}}

def act.step.j(+s: ActStep, +ty: T.Bt, +en: List<&2, U32>, +goal: T.Bt, +hps: List<&2, T.BParam>) -> ActStep:
  +hit = Bool.and(Bool.and(Nat.is_eq(act.step.kind(s), 2n), Bool.not(S.eq(en, Nil{}))), Bool.and(Bool.not(S.eq(act.eq.rhs.or(ty), Nil{})), Bool.or(act.occurs(en, goal), act.ps.mention(hps, en))))
  Bool.pick(ActStep, hit, act.step.three(ty, en, goal), s)

def act.step.body(k: Nat, +ty: T.Bt, body: T.Bt) -> T.Bt:
  match k:
    case 3n:
      T.tba.subst(body, act.eq.rhs(ty), act.eq.lhs(ty))
    case _:
      body

# after a generalizing step, the generalized parameters' types have the
# hole filled, and {==} for e (the next steps read them)
def act.gen.hps(ps: List<&2, T.BParam>, +gn: List<&2, List<&2, U32>>, +b: List<&2, U32>, +a: T.Bt, +en: List<&2, U32>) -> List<&2, T.BParam>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, +x, +ty} <> t:
      T.BParam{m, x, Bool.pick(T.Bt, act.used(x, gn), T.tba.subst(T.tba.subst(ty, b, a), en, T.BtRefl{}), ty)} <> act.gen.hps(t, gn, b, a, en)

# Equations between successors (`suc m ≡ suc n`: Agda's refl unifies by
# injectivity, n dotted as m; pred-cancel-≡, suc-injective): with both
# sides suc^k of a variable, k >= 1, the step is the one at the variables,
# its motive's hole under k a2b_pred calls (%e : G[n := a2b_pred^k(_)]:
# G at a2b_pred^k(suc^k n) is G, at a2b_pred^k(suc^k m) it is G[n := m]),
# and it generalizes no parameter (2026-10-29).
def act.sucs.k(t: T.Bt) -> Nat:
  match t:
    case T.BtSucc{a}:
      1n+act.sucs.k(a)
    case _:
      0n

def act.sucs.peel(t: T.Bt) -> T.Bt:
  match t:
    case T.BtSucc{a}:
      act.sucs.peel(a)
    case t:
      t

def act.pk.preds(k: Nat, t: T.Bt) -> T.Bt:
  match k:
    case 0n:
      t
    case 1n+p:
      T.BtApp{T.BtVar{S.b("a2b_pred")}, T.tba.args([act.pk.preds(p, t)])}

def act.bt.isvar(t: T.Bt) -> Bool:
  match t:
    case T.BtVar{x}:
      True{}
    case _:
      False{}

# the depth k of an equation between suc^k of two variables (k >= 1), else 0
def act.eq.pk(+ty: T.Bt) -> Nat:
  match ty:
    case T.BtEq{t, +a, +b}:
      +ka = act.sucs.k(a)
      Bool.pick(Nat, Bool.and(Bool.and(Nat.is_eq(ka, act.sucs.k(b)), Bool.not(Nat.is_eq(ka, 0n))), Bool.and(act.bt.isvar(act.sucs.peel(a)), act.bt.isvar(act.sucs.peel(b)))), ka, 0n)
    case _:
      0n

# the equation between the variables under its sucs (when pk > 0)
def act.eq.pty(+pk: Nat, ty: T.Bt) -> T.Bt:
  match ty:
    case T.BtEq{+t, +a, +b}:
      Bool.pick(T.Bt, Nat.is_eq(pk, 0n), T.BtEq{t, a, b}, T.BtEq{t, act.sucs.peel(a), act.sucs.peel(b)})
    case ty:
      ty

def act.step.kp(k: Nat, +j: Nat, +t: T.Bt, +a: T.Bt, +b: T.Bt, +a1: T.Bt, +b1: T.Bt, +e: T.Bt, +goal: T.Bt) -> ActStep:
  match k:
    case 1n:
      ActStep{1n, T.tba.subst(goal, act.var.name(b1), act.pk.preds(j, T.BtWild{})), T.tba.subst(T.tba.subst(goal, act.var.name(b1), a1), act.var.name.or(e), T.BtRefl{}), T.BtWild{}, Nil{}}
    case 2n:
      ActStep{2n, T.tba.subst(goal, act.var.name(a1), act.pk.preds(j, T.BtWild{})), T.tba.subst(goal, act.var.name(a1), b1), T.BtApp{T.BtVar{S.b("Equal.sym")}, T.tba.args([T.BtDead{t}, T.BtDead{a}, T.BtDead{b}, e])}, List.append(&2, U32, act.var.name(e), S.b("_sym"))}
    case _:
      ActStep{0n, T.BtWild{}, goal, T.BtWild{}, Nil{}}

def act.step.pk(pk: Nat, +ty: T.Bt, +e: T.Bt, +ds: List<&2, List<&2, U32>>, +goal: T.Bt, +hps: List<&2, T.BParam>) -> ActStep:
  match pk ty:
    case 0n ty:
      act.step(ty, e, ds, goal, hps)
    case 1n+q T.BtEq{+t, +a, +b}:
      +a1 = act.sucs.peel(a)
      +b1 = act.sucs.peel(b)
      act.step.kp(act.mark.b(act.dotted(b1, ds), act.dotted(a1, ds), act.occurs(act.var.name(b1), goal), act.occurs(act.var.name(a1), goal)), 1n+q, t, a, b, a1, b1, e, goal)
    case _ _:
      ActStep{0n, T.BtWild{}, goal, T.BtWild{}, Nil{}}

# the parameters but the split ones (a step's ps.ment2 asks only those a
# rewrite could generalize: lookup's x : Vec A n is matched, not moved)
def act.ps.minus(ps: List<&2, T.BParam>, +skip: List<&2, List<&2, U32>>) -> List<&2, T.BParam>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{+m, +x, +ty} <> t:
      List.append(&2, T.BParam, Bool.pick(List<&2, T.BParam>, act.used(x, skip), Nil{}, [T.BParam{m, x, ty}]), act.ps.minus(t, skip))

# Equations between two applications of one constructor (`(Γ , B) ≡ (Γ , A)`
# at Z : (Γ , A) ∋ A, plfa's ext; `A ⇒ B ≡ C ⇒ D` at a refl pattern,
# ⇒-inj₁: Agda's unifier uses injectivity) are one equation a field: where
# a field's sides differ and one is a variable whose type the clause
# knows, e_pjI = Equal.cong(T, F, {\{C: (a2b_f1 => .. => a2b_fN => a2b_fI);
# (_ => v)} : T -> F}, a, b, e) : {a_I == b_I : F} (v: that variable, F its
# type; Bend 2.0.39 checks it, /tmp/bx/inj/d.bend), then a step like any
# variable equation's, its let only when the step rewrites (2026-10-29).
type ActInj is Data:
  ActInj{x: List<&2, U32>, h: List<&2, U32>, ty: T.Bt, v: T.Bt}
  ActOne{e: T.Bt}

def act.inj.bind(n: Nat, +k: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      "a2b_f" ++ Nat.show(k) ++ " => " ++ act.inj.bind(p, 1n+k)

def act.inj.prj(+c: List<&2, U32>, +n: Nat, +i: Nat, +d: List<&2, U32>, +t: T.Bt, +f: T.Bt) -> T.Bt:
  +raw = List.append(&2, U32, S.b("\\{"), List.append(&2, U32, c, List.append(&2, U32, S.b(": (" ++ act.inj.bind(n, 1n) ++ "a2b_f" ++ Nat.show(i) ++ "); (_ => "), List.append(&2, U32, d, S.b(")}")))))
  T.BtAnn{T.BtVar{raw}, T.BtPi{T.BmLive{}, S.b("_"), False{}, t, f}}

def act.inj.vn(t: T.Bt) -> List<&2, U32>:
  match t:
    case T.BtVar{x}:
      x
    case _:
      Nil{}

def act.inj.known(t: T.Bt) -> Bool:
  match t:
    case T.BtWild{}:
      False{}
    case _:
      True{}

# two variables of one name (no equation to rewrite by)
def act.inj.same(a: T.Bt, b: T.Bt) -> Bool:
  match a b:
    case T.BtVar{x} T.BtVar{y}:
      S.eq(x, y)
    case _ _:
      False{}

def act.inj.fields(xa: List<&2, T.Bt>, xb: List<&2, T.Bt>, +i: Nat, +n: Nat, +c: List<&2, U32>, +t: T.Bt, +wa: T.Bt, +wb: T.Bt, +e: T.Bt, +en: List<&2, U32>, +hps: List<&2, T.BParam>) -> List<&2, ActInj>:
  match xa xb:
    case +a <> at +b <> bt:
      +a1 = act.undead(a)
      +b1 = act.undead(b)
      +va = act.inj.vn(a1)
      +vb = act.inj.vn(b1)
      +fa = act.param.ty(hps, va)
      +ka = Bool.and(Bool.not(S.eq(va, Nil{})), act.inj.known(fa))
      +v = Bool.pick(List<&2, U32>, ka, va, vb)
      +f = Bool.pick(T.Bt, ka, fa, act.param.ty(hps, vb))
      +ok = Bool.and(Bool.and(Bool.not(S.eq(v, Nil{})), act.inj.known(f)), Bool.not(act.inj.same(a1, b1)))
      +rest = act.inj.fields(at, bt, 1n+i, n, c, t, wa, wb, e, en, hps)
      Bool.pick(List<&2, ActInj>, ok, ActInj{List.append(&2, U32, en, S.b("_pj" ++ Nat.show(i))), en, T.BtEq{f, a1, b1}, T.BtApp{T.BtVar{S.b("Equal.cong")}, T.tba.args([T.BtDead{t}, T.BtDead{f}, T.BtDead{act.inj.prj(c, n, i, v, t, f)}, T.BtDead{wa}, T.BtDead{wb}, e])}} <> rest, rest)
    case _ _:
      Nil{}

def act.inj.list(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      h <> act.inj.list(t)
    case _:
      Nil{}

def act.inj.con(a: T.Bt, b: T.Bt, +t: T.Bt, +e: T.Bt, +hps: List<&2, T.BParam>) -> List<&2, ActInj>:
  match a b:
    case T.BtCon{+ca, +xa} T.BtCon{+cb, +xb}:
      +la = act.inj.list(xa)
      +lb = act.inj.list(xb)
      +n = List.length(&2, T.Bt, la)
      Bool.pick(List<&2, ActInj>, Bool.and(Bool.and(S.eq(ca, cb), Nat.is_eq(n, List.length(&2, T.Bt, lb))), Bool.not(Nat.is_eq(n, 0n))), act.inj.fields(la, lb, 1n, n, ca, t, T.BtCon{ca, xa}, T.BtCon{cb, xb}, e, act.var.name(e), hps), Nil{})
    case _ _:
      Nil{}

def act.inj.of(ety: T.Bt, +e: T.Bt, +hps: List<&2, T.BParam>) -> List<&2, ActInj>:
  match ety:
    case T.BtEq{+t, a, b}:
      act.inj.con(act.undead(a), act.undead(b), t, e, hps)
    case _:
      Nil{}

# the clause's rewrites, in order, before its body (svs: the split
# parameters, which a rewrite does not generalize; pj: the equations the
# head equation splits into, act.inj, or ActOne{e} for e itself)
def act.inj.or(pjs: List<&2, ActInj>, +e: T.Bt) -> List<&2, ActInj>:
  match pjs:
    case Nil{}:
      [ActOne{e}]
    case h <> r:
      h <> r

# a field equation's step: its evidence the projection itself (no let, so
# a generalizing step around it is still one term), a reversed one's let
# named after the field
def act.inj.sname(s: ActStep, +x: List<&2, U32>) -> ActStep:
  match s:
    case ActStep{k, p, g, y, e2}:
      ActStep{k, p, g, y, List.append(&2, U32, x, S.b("_sym"))}

def act.rws(fuel: Nat, pj: List<&2, ActInj>, es: List<&2, T.Bt>, +ds: List<&2, List<&2, U32>>, +goal: T.Bt, +hps: List<&2, T.BParam>, +svs: List<&2, List<&2, U32>>, body: T.Bt) -> T.Bt:
  match fuel pj es:
    case 1n+q ActInj{+x, +h, +ety, +v} <> r es:
      +s = act.inj.sname(act.step(ety, v, ds, goal, act.ps.minus(hps, svs)), x)
      +k = act.step.kind(s)
      +bn = act.step.hole(k, ety)
      +gs = Bool.pick(List<&2, T.BParam>, Nat.is_eq(k, 0n), Nil{}, act.gen.ps(hps, x <> h <> bn <> svs, [bn]))
      +hps3 = Bool.pick(List<&2, T.BParam>, Nat.is_eq(k, 0n), hps, act.gen.hps(hps, act.gen.names(gs), bn, act.step.fill(k, ety), Nil{}))
      act.step.wrap(s, v, goal, gs, bn, act.rws(q, r, es, ds, act.step.goal(s), hps3, svs, act.step.body(k, ety, body)))
    case 1n+q ActOne{+e} <> r es:
      +ety0 = act.param.ty(hps, act.var.name(e))
      +pk = act.eq.pk(ety0)
      +ety = act.eq.pty(pk, ety0)
      +s0 = act.step.pk(pk, ety0, e, ds, goal, act.ps.minus(hps, svs))
      +s = Bool.pick(ActStep, Nat.is_eq(pk, 0n), act.step.j(s0, ety, act.var.name.or(e), goal, hps), s0)
      +k = act.step.kind(s)
      +bn = act.step.hole(k, ety)
      +en = act.var.name(e)
      +gs = Bool.pick(List<&2, T.BParam>, Bool.or(Nat.is_eq(k, 0n), Bool.not(Nat.is_eq(pk, 0n))), Nil{}, act.gen.ps(hps, en <> bn <> svs, [bn, act.step.ev(k, en)]))
      act.step.wrap(s, e, goal, gs, bn, act.rws(q, r, es, ds, act.step.goal(s), act.gen.hps(hps, act.gen.names(gs), bn, act.step.fill(k, ety), act.step.ev(k, act.var.name.or(e))), svs, act.step.body(k, ety, body)))
    case 1n+p Nil{} +e <> t:
      act.rws(p, act.inj.or(act.inj.of(act.param.ty(hps, act.var.name(e)), e, hps), e), t, ds, goal, hps, svs, body)
    case _ _ _:
      body

# Indexed patterns: a constructor pattern of an indexed family names its
# equation fields after its place (x_2_eq: parameter x's pattern, its
# second argument), and at a split parameter each becomes a rewrite like a
# refl pattern's.  Its type is {v == t : T}: v the index the parameter's
# type has there, t the term the clause's dot pattern gives v (Agda's
# match made v a dot pattern), T v's type.
type ActDot is Data:
  ActDot{x: List<&2, U32>, t: A.Ag}

# the clause's top-level dot patterns, by parameter
def act.dots(ps: A.Ag, ents: List<&2, T.Bt>) -> List<&2, ActDot>:
  match ps ents:
    case A.AgPArg{i, x, A.AgPDot{t}, rest} e <> et:
      ActDot{act.var.name(e), t} <> act.dots(rest, et)
    case A.AgPArg{i, x, p, rest} e <> et:
      act.dots(rest, et)
    case _ _:
      Nil{}

def act.dot.find(ds: List<&2, ActDot>, +v: List<&2, U32>) -> Maybe<&2, A.Ag>:
  match ds:
    case Nil{}:
      None{}
    case ActDot{+x, +t} <> rest:
      Bool.pick(Maybe<&2, A.Ag>, S.eq(x, v), Some{t}, act.dot.find(rest, v))

def act.at(+pre: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  List.append(&2, U32, pre, 95 <> S.b(Nat.show(i)))

# an equation field's placeholder (act.wilds): its name starts ix_eq
def act.is.ph(+nm: List<&2, U32>) -> Bool:
  S.eq(List.take(&2, U32, nm, 5n), S.b("ix_eq"))

# the equation placeholders of a pattern (or a spine of them, i its
# position) named after their place under pre
def act.eq.deep(p: T.Bt, +pre: List<&2, U32>, +i: Nat) -> T.Bt:
  match p:
    case T.BtArgs{a, rest}:
      T.BtArgs{act.eq.deep(a, act.at(pre, i), 1n), act.eq.deep(rest, pre, 1n+i)}
    case T.BtCon{c, a}:
      T.BtCon{c, act.eq.deep(a, pre, 1n)}
    case T.BtSucc{a}:
      T.BtSucc{act.eq.deep(a, pre, 1n)}
    case T.BtPv{+m, +nm}:
      T.BtPv{m, Bool.pick(List<&2, U32>, act.is.ph(nm), List.append(&2, U32, pre, S.b("_eq")), Bool.pick(List<&2, U32>, act.nrf.is.ph(nm), List.append(&2, U32, pre, S.b("_rfl")), nm))}
    case p:
      p

# the top patterns, each under its parameter's name
def act.eq.spine(ps: T.Bt, xs: List<&2, T.Bt>) -> T.Bt:
  match ps xs:
    case T.BtArgs{p, rest} x <> xt:
      T.BtArgs{act.eq.deep(p, act.var.name(x), 1n), act.eq.spine(rest, xt)}
    case ps _:
      ps

def act.spine.list(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      h <> act.spine.list(t)
    case _:
      Nil{}

def act.list.take(n: Nat, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match n xs:
    case 1n+p h <> t:
      h <> act.list.take(p, t)
    case _ xs:
      Nil{}

def act.list.last(+n: Nat, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  List.reverse(&2, T.Bt, act.list.take(n, List.reverse(&2, T.Bt, xs)))

# the equation variables of a top constructor pattern: its arguments
# named x_i_eq, by position
def act.eq.vars(a: T.Bt, +x: List<&2, U32>, +i: Nat) -> List<&2, List<&2, U32>>:
  match a:
    case T.BtArgs{T.BtPv{m, +nm}, rest}:
      +e = List.append(&2, U32, act.at(x, i), S.b("_eq"))
      List.append(&2, List<&2, U32>, Bool.pick(List<&2, List<&2, U32>>, S.eq(nm, e), [e], Nil{}), act.eq.vars(rest, x, 1n+i))
    case T.BtArgs{h, rest}:
      act.eq.vars(rest, x, 1n+i)
    case _:
      Nil{}

# an equation variable's parameter: {v == t : T} when the clause dots v
def act.eq.p(m: Maybe<&2, A.Ag>, +e: List<&2, U32>, +v: T.Bt, +hps: List<&2, T.BParam>, +ctx: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.BParam>:
  match m:
    case Some{t}:
      [T.BParam{T.BmLive{}, e, T.BtEq{act.param.ty(hps, act.var.name(v)), v, act.t(act.inline(100000n, t, env), ctx, env)}}]
    case None{}:
      Nil{}

def act.eq.ps(es: List<&2, List<&2, U32>>, ixs: List<&2, T.Bt>, +hps: List<&2, T.BParam>, +dots: List<&2, ActDot>, +ctx: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.BParam>:
  match es ixs:
    case +e <> et +v <> vt:
      List.append(&2, T.BParam, act.eq.p(act.dot.find(dots, act.var.name(v)), e, v, hps, ctx, env), act.eq.ps(et, vt, hps, dots, ctx, env))
    case _ _:
      Nil{}

# a spine's terms, an erased one's mark taken off
def act.spine.undead(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      act.undead(h) <> act.spine.undead(t)
    case _:
      Nil{}

def act.ty.args(t: T.Bt) -> List<&2, T.Bt>:
  match t:
    case T.BtTyApp{n, a}:
      act.spine.undead(a)
    case _:
      Nil{}

# the equation parameters of one top pattern at parameter x
def act.eq.top(p: T.Bt, +x: List<&2, U32>, +hps: List<&2, T.BParam>, +dots: List<&2, ActDot>, +ctx: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.BParam>:
  match p:
    case T.BtCon{c, a}:
      +es = act.eq.vars(a, x, 1n)
      act.eq.ps(es, act.list.last(List.length(&2, List<&2, U32>, es), act.ty.args(act.param.ty(hps, x))), hps, dots, ctx, env)
    case _:
      Nil{}

def act.eq.tops(ps: T.Bt, xs: List<&2, T.Bt>, +hps: List<&2, T.BParam>, +dots: List<&2, ActDot>, +ctx: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.BParam>:
  match ps xs:
    case T.BtArgs{p, rest} x <> xt:
      List.append(&2, T.BParam, act.eq.top(p, act.var.name(x), hps, dots, ctx, env), act.eq.tops(rest, xt, hps, dots, ctx, env))
    case _ _:
      Nil{}

def act.ps.vars(ps: List<&2, T.BParam>) -> List<&2, T.Bt>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      T.BtVar{x} <> act.ps.vars(t)

# a case's body: the rewrites of its refl patterns, then those of its
# indexed patterns' equations (eqs), then the body
# Index proofs, not index rewrites.  A case that answers with a constructor
# of its goal's datatype, its only rewrites its split's index equations
# e : {v == t : Nat} (a dotted index: toℕ {.(suc n)} (suc {n} i)), needs
# them only for the constructor's equation fields, {==} at the goal's
# indices once v is t.  But a rewrite on a variable e does not compute, so
# a function written so is stuck at a constructor whose equation is a
# variable, and a proof about it (toℕ (inject₁ zero) ≡ 0 at zero {n} e) is
# refused.  So the fields are proved instead, the case left without
# rewrites: at the goal's index I, Equal.cong(Nat, Nat, y => I[v := y], v,
# t, e) : {I == I[v := t]} (e itself when I is v), one equation after
# another by Equal.trans.  Only for Nat equations, a constructor whose last
# arguments are {==} (one per index, the goal's last arguments), each index
# a variable, a successor or free of every v, and no v in the goal's
# other arguments or in the constructor's own.
def act.ixp.list(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      h <> act.ixp.list(t)
    case _:
      Nil{}

def act.ixp.nat(t: T.Bt) -> Bool:
  match t:
    case T.BtVar{x}:
      S.eq(x, S.b("Nat"))
    case _:
      False{}

def act.ixp.okeq(t: T.Bt) -> Bool:
  match t:
    case T.BtEq{ty, T.BtVar{v}, b}:
      act.ixp.nat(ty)
    case _:
      False{}

def act.ixp.okeqs(eqs: List<&2, T.BParam>) -> Bool:
  match eqs:
    case Nil{}:
      True{}
    case T.BParam{m, x, ty} <> t:
      Bool.and(act.ixp.okeq(ty), act.ixp.okeqs(t))

def act.ixp.v(t: T.Bt) -> List<&2, U32>:
  match t:
    case T.BtEq{ty, T.BtVar{v}, b}:
      v
    case _:
      Nil{}

def act.ixp.rhs(t: T.Bt) -> T.Bt:
  match t:
    case T.BtEq{ty, a, b}:
      b
    case _:
      T.BtWild{}

def act.ixp.vs(eqs: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match eqs:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      act.ixp.v(ty) <> act.ixp.vs(t)

# whether t mentions one of vs
def act.ixp.men(+vs: List<&2, List<&2, U32>>, +t: T.Bt) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case v <> r:
      Bool.or(act.occurs(v, t), act.ixp.men(r, t))

def act.ixp.menl(+vs: List<&2, List<&2, U32>>, ts: List<&2, T.Bt>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(act.ixp.men(vs, h), act.ixp.menl(vs, t))

def act.ixp.isrefl(t: T.Bt) -> Bool:
  match t:
    case T.BtRefl{}:
      True{}
    case _:
      False{}

# how many {==} end the list
def act.ixp.nrefl(ts: List<&2, T.Bt>, k: Nat) -> Nat:
  match ts:
    case Nil{}:
      k
    case +h <> t:
      act.ixp.nrefl(t, Bool.pick(Nat, act.ixp.isrefl(h), 1n+k, 0n))

# an index whose type is surely Nat, or one no equation touches
def act.ixp.shape(+vs: List<&2, List<&2, U32>>, +t: T.Bt) -> Bool:
  match t:
    case T.BtVar{x}:
      True{}
    case T.BtSucc{a}:
      True{}
    case T.BtNat{n}:
      True{}
    case _:
      Bool.not(act.ixp.men(vs, t))

def act.ixp.shapes(+vs: List<&2, List<&2, U32>>, ts: List<&2, T.Bt>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(act.ixp.shape(vs, h), act.ixp.shapes(vs, t))

def act.ixp.undeads(ts: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match ts:
    case Nil{}:
      Nil{}
    case h <> t:
      act.undead(h) <> act.ixp.undeads(t)

# the index after every equation's v is its t
def act.ixp.sub(eqs: List<&2, T.BParam>, t: T.Bt) -> T.Bt:
  match eqs:
    case Nil{}:
      t
    case T.BParam{m, x, +ty} <> r:
      act.ixp.sub(r, T.tba.subst(t, act.ixp.v(ty), act.ixp.rhs(ty)))

def act.ixp.nat.t() -> T.Bt:
  T.BtDead{T.BtVar{S.b("Nat")}}

# a proof of {I == I[v := t]} by e : {v == t}
def act.ixp.cong(+v: List<&2, U32>, +t: T.Bt, +e: List<&2, U32>, +i: T.Bt) -> T.Bt:
  match i:
    case T.BtVar{x}:
      Bool.pick(T.Bt, S.eq(x, v), T.BtVar{e}, T.BtApp{T.BtVar{S.b("Equal.cong")}, T.tba.args([act.ixp.nat.t(), act.ixp.nat.t(), T.BtDead{T.BtLam{T.BmLive{}, S.b("a2b_y"), T.tba.subst(i, v, T.BtVar{S.b("a2b_y")})}}, T.BtDead{T.BtVar{v}}, T.BtDead{t}, T.BtVar{e}])})
    case _:
      T.BtApp{T.BtVar{S.b("Equal.cong")}, T.tba.args([act.ixp.nat.t(), act.ixp.nat.t(), T.BtDead{T.BtLam{T.BmLive{}, S.b("a2b_y"), T.tba.subst(i, v, T.BtVar{S.b("a2b_y")})}}, T.BtDead{T.BtVar{v}}, T.BtDead{t}, T.BtVar{e}])}

def act.ixp.join(+i: T.Bt, +j: T.Bt, +k: T.Bt, +p: T.Bt, +q: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, act.ixp.isrefl(q), p, Bool.pick(T.Bt, act.ixp.isrefl(p), q, T.BtApp{T.BtVar{S.b("Equal.trans")}, T.tba.args([act.ixp.nat.t(), T.BtDead{i}, T.BtDead{j}, T.BtDead{k}, p, q])}))

def act.ixp.step(b: Bool, +v: List<&2, U32>, +t: T.Bt, +e: List<&2, U32>, +i: T.Bt) -> T.Bt:
  match b:
    case True{}:
      act.ixp.cong(v, t, e, i)
    case False{}:
      T.BtRefl{}

# the proof at one index, equation after equation
def act.ixp.pf(+eqs: List<&2, T.BParam>, +i: T.Bt) -> T.Bt:
  match eqs:
    case Nil{}:
      T.BtRefl{}
    case T.BParam{m, +x, +ty} <> +r:
      +v = act.ixp.v(ty)
      +t = act.ixp.rhs(ty)
      +i2 = T.tba.subst(i, v, t)
      act.ixp.join(i, i2, act.ixp.sub(r, i2), act.ixp.step(act.occurs(v, i), v, t, x, i), act.ixp.pf(r, i2))

def act.ixp.pfs(+eqs: List<&2, T.BParam>, ixs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match ixs:
    case Nil{}:
      Nil{}
    case h <> t:
      act.ixp.pf(eqs, h) <> act.ixp.pfs(eqs, t)

def act.ixp.ok(+vs: List<&2, List<&2, U32>>, +r: Nat, +gs: List<&2, T.Bt>, +cas: List<&2, T.Bt>) -> Bool:
  +ng = List.length(&2, T.Bt, gs)
  +na = List.length(&2, T.Bt, cas)
  Bool.and(Bool.and(Bool.not(Nat.is_eq(r, 0n)), Bool.and(Nat.is_le(r, ng), Nat.is_le(r, na))), Bool.and(Bool.and(Bool.not(act.ixp.menl(vs, List.take(&2, T.Bt, gs, Nat.sub(ng, r)))), Bool.not(act.ixp.menl(vs, List.take(&2, T.Bt, cas, Nat.sub(na, r))))), Bool.and(act.ixp.shapes(vs, List.drop(&2, T.Bt, gs, Nat.sub(ng, r))), act.ixp.menl(vs, List.drop(&2, T.Bt, gs, Nat.sub(ng, r))))))

def act.ixp.con(b: Bool, +r: Nat, +c: List<&2, U32>, +cas: List<&2, T.Bt>, +gs: List<&2, T.Bt>, +eqs: List<&2, T.BParam>) -> Maybe<&2, T.Bt>:
  match b:
    case True{}:
      Some{T.BtExpr{T.BtCon{c, T.tba.args(List.append(&2, T.Bt, List.take(&2, T.Bt, cas, Nat.sub(List.length(&2, T.Bt, cas), r)), act.ixp.pfs(eqs, List.drop(&2, T.Bt, gs, Nat.sub(List.length(&2, T.Bt, gs), r)))))}}}
    case False{}:
      None{}

def act.ixp.at(+eqs: List<&2, T.BParam>, goal: T.Bt, body: T.Bt) -> Maybe<&2, T.Bt>:
  match goal body:
    case T.BtTyApp{n, ga} T.BtExpr{T.BtCon{+c, ca}}:
      +gs = act.ixp.undeads(act.ixp.list(ga))
      +cas = act.ixp.list(ca)
      +vs = act.ixp.vs(eqs)
      +r = act.ixp.nrefl(cas, 0n)
      act.ixp.con(Bool.and(act.ixp.okeqs(eqs), act.ixp.ok(vs, r, gs, cas)), r, c, cas, gs, eqs)
    case _ _:
      None{}

def act.ixp.try(+rs: List<&2, T.Bt>, +eqs: List<&2, T.BParam>, +goal: T.Bt, +body: T.Bt) -> Maybe<&2, T.Bt>:
  match rs eqs:
    case Nil{} +e <> t:
      act.ixp.at(eqs, goal, body)
    case _ _:
      None{}

# An index equation e : {v == t} the goal itself mentions (the split's
# constructor, its field e, is in the goal: toℕ (inject₁ zero) ≡ toℕ zero
# at zero {n} e) is no rewrite: the motive G[v := _] has e at the type
# with v, so Bend refuses it (unless t is a variable, J's case,
# act.step.j); without it the goal may still compute (inject₁ zero is
# zero by index proofs, act.ixp).
def act.ixp.rvar(t: T.Bt) -> Bool:
  match t:
    case T.BtEq{ty, a, T.BtVar{b}}:
      True{}
    case _:
      False{}

def act.ixp.keep(eqs: List<&2, T.BParam>, +goal: T.Bt) -> List<&2, T.BParam>:
  match eqs:
    case Nil{}:
      Nil{}
    case T.BParam{+m, +x, +ty} <> +t:
      +r = act.ixp.keep(t, goal)
      Bool.pick(List<&2, T.BParam>, Bool.and(act.occurs(x, goal), Bool.not(act.ixp.rvar(ty))), r, T.BParam{m, x, ty} <> r)

def act.case.body.or(m: Maybe<&2, T.Bt>, +eqs: List<&2, T.BParam>, +rs: List<&2, T.Bt>, +ds: List<&2, List<&2, U32>>, +goal: T.Bt, +hps: List<&2, T.BParam>, +svs: List<&2, List<&2, U32>>, +body: T.Bt) -> T.Bt:
  match m:
    case Some{b}:
      b
    case None{}:
      act.rws(256n, Nil{}, List.append(&2, T.Bt, rs, act.ps.vars(act.ixp.keep(eqs, goal))), ds, goal, List.append(&2, T.BParam, hps, eqs), svs, body)

def act.case.body(+eqs: List<&2, T.BParam>, rw: ActRw, +goal: T.Bt, +hps: List<&2, T.BParam>, +svs: List<&2, List<&2, U32>>, +body: T.Bt) -> T.Bt:
  match rw:
    case ActRw{+rs, +ds}:
      act.case.body.or(act.ixp.try(rs, eqs, goal, body), eqs, rs, ds, goal, hps, svs, body)

# the scrutinees: the entries of the split parameters
def act.scr.vars(scr: List<&2, Bool>, ents: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match scr ents:
    case True{} <> st e <> et:
      e <> act.scr.vars(st, et)
    case False{} <> st e <> et:
      act.scr.vars(st, et)
    case _ _:
      Nil{}

# Definitions by clauses, one level (`T false`, `True (no _)`: toWitness's
# absurd pattern): the type- and Bool-valued definitions' clauses are in
# the unfoldings under "tcl:" (act.tcl.of); at arguments already
# constructors (inlined, and each argument headed by such a definition
# evaluated once at inlined arguments of its own), the first clause whose
# patterns match them (constructors by key, literals by digits; a variable
# or a dot anything), its body when closed.
def act.tcl.key(q: A.AgQ) -> String:
  "tcl:" ++ act.key(q)

def act.tcl.body(c: ActCopy) -> A.Ag:
  match c:
    case ActCopy{n, b}:
      b

def act.tcl.cls(+env: ActEnv, q: A.AgQ) -> A.Ag:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.tcl.body(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.tcl.key(q))))

type ActPt is Data:
  ActPt{p: A.Ag, t: A.Ag}

def act.ev.zip(ps: A.Ag, es: A.Ag, acc: List<&2, ActPt>) -> List<&2, ActPt>:
  match ps es:
    case A.AgPArg{i, x, p, prest} A.AgEApp{i2, t, erest}:
      ActPt{p, t} <> act.ev.zip(prest, erest, acc)
    case _ _:
      acc

# a literal against zero/suc (0 is zero; k+1 is suc of k)
def act.ev.num.go(cs: List<&2, U32>, acc: Nat) -> Nat:
  match cs:
    case Nil{}:
      acc
    case c <> t:
      act.ev.num.go(t, Nat.add(Nat.mul(acc, 10n), Nat.sub(U32.to_nat(c), 48n)))

def act.ev.litok(b: ActB, +s: List<&2, U32>) -> Bool:
  match b:
    case AbZero{}:
      S.eq(s, S.b("0"))
    case AbSuc{}:
      Bool.not(S.eq(s, S.b("0")))
    case _:
      False{}

def act.ev.litsub(b: ActB, sub: A.Ag, +s: List<&2, U32>, rest: List<&2, ActPt>) -> List<&2, ActPt>:
  match b sub:
    case AbSuc{} A.AgPArg{i, x, p, prest}:
      ActPt{p, A.AgLit{A.AgLNat{S.b(Nat.show(Nat.sub(act.ev.num.go(s, 0n), 1n)))}}} <> rest
    case _ _:
      rest

def act.ev.pairs(fuel: Nat, xs: List<&2, ActPt>) -> Bool:
  match fuel xs:
    case _ Nil{}:
      True{}
    case 0n _:
      False{}
    case 1n+f ActPt{A.AgPVar{x, ix, o}, t} <> rest:
      act.ev.pairs(f, rest)
    case 1n+f ActPt{A.AgPDot{d}, t} <> rest:
      act.ev.pairs(f, rest)
    case 1n+f ActPt{A.AgPCon{q, r, fo, sub}, A.AgCon{q2, o, es2}} <> rest:
      Bool.and(String.eq(act.key(q), act.key(q2)), act.ev.pairs(f, act.ev.zip(sub, es2, rest)))
    case 1n+f ActPt{A.AgPLit{A.AgLNat{s}}, A.AgLit{A.AgLNat{s2}}} <> rest:
      Bool.and(S.eq(s, s2), act.ev.pairs(f, rest))
    case 1n+f ActPt{A.AgPCon{+q, r, fo, sub}, A.AgLit{A.AgLNat{+s}}} <> rest:
      +b = act.builtin(act.qs(q))
      Bool.and(act.ev.litok(b, s), act.ev.pairs(f, act.ev.litsub(b, sub, s, rest)))
    case _ _:
      False{}

def act.ag.closed(t: A.Ag) -> Bool:
  match t:
    case A.AgDef{q, es}:
      act.ag.closed(es)
    case A.AgCon{q, o, es}:
      act.ag.closed(es)
    case A.AgEApp{i, a, rest}:
      Bool.and(act.ag.closed(a), act.ag.closed(rest))
    case A.AgENil{}:
      True{}
    case A.AgLit{l}:
      True{}
    case A.AgEl{s, a}:
      act.ag.closed(a)
    case A.AgSort{s}:
      True{}
    case A.AgLevel{l}:
      True{}
    case _:
      False{}

def act.ev.pick(hit: Bool, +body: A.Ag, alt: Maybe<&2, A.Ag>) -> Maybe<&2, A.Ag>:
  Bool.pick(Maybe<&2, A.Ag>, Bool.and(hit, act.ag.closed(body)), Some{body}, alt)

def act.ev.cls(cls: A.Ag, +es: A.Ag) -> Maybe<&2, A.Ag>:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      act.ev.pick(act.ev.pairs(64n, act.ev.zip(ps, es, Nil{})), body, act.ev.cls(rest, es))
    case _:
      None{}

def act.ev.or(m: Maybe<&2, A.Ag>, d: A.Ag) -> A.Ag:
  match m:
    case Some{b}:
      b
    case None{}:
      d

# The arguments evaluated, nested (fuel levels): each inlined, and one
# headed by a type- or Bool-valued definition by clauses evaluated at its
# own evaluated arguments (NonZero 0's field `T (not (0 ≡ᵇ 0))`: _==_ at
# 0 0 is true, not true is false, T false is ⊥).
def act.ev.go(fuel: Nat, spine: Bool, t: A.Ag, +env: ActEnv) -> A.Ag:
  match fuel spine t:
    case 1n+(+f) True{} A.AgEApp{i, a, rest}:
      A.AgEApp{i, act.ev.go(f, False{}, act.inline(64n, a, env), env), act.ev.go(f, True{}, rest, env)}
    case 1n+f False{} A.AgDef{+q, +es}:
      act.ev.or(act.ev.cls(act.tcl.cls(env, q), act.ev.go(f, True{}, es, env)), A.AgDef{q, es})
    case _ _ t:
      t

def act.ev.args(es: A.Ag, +env: ActEnv) -> A.Ag:
  act.ev.go(8n, True{}, es, env)

# Absurd clauses: Agda's `f ()` needs no split when the variable's type is
# empty (⊥ = Irrelevant Empty), but Bend has to see the emptiness, so the
# clause's body matches the variable down to an empty data type: a
# type-valued definition is opened, a one-field record (Irrelevant A, Lift
# A) is matched and its field, whose type is taken to be the record's last
# argument, eliminated in turn, and an empty data type is a match with no
# cases.  One step of that walk:
type ActAbsSt is Data:
  AbsDone{}
  AbsOpen{t: A.Ag}
  AbsWrap{c: List<&2, U32>, t: A.Ag}
  AbsEq{t: A.Ag}
  AbsFam{t: A.Ag, cs: List<&2, String>}
  AbsFail{}

# the last argument of a spine
def act.es.last(es: A.Ag) -> A.Ag:
  match es:
    case A.AgEApp{i, t, A.AgENil{}}:
      t
    case A.AgEApp{i, t, rest}:
      act.es.last(rest)
    case _:
      A.AgNone{}

# a one-field record's field type at the record's arguments (the record's
# unfoldings hold it under "rft:", act.rft.of); else, as before, the last
# argument (Irrelevant A, Lift A)
def act.rft.key(q: A.AgQ) -> String:
  "rft:" ++ act.key(q)

def act.rft.at(c: ActCopy, +es: A.Ag) -> A.Ag:
  match c:
    case ActCopy{0n, A.AgNone{}}:
      act.es.last(es)
    case c:
      act.unfold.of(c, es)

def act.rft(+env: ActEnv, q: A.AgQ, +es: A.Ag) -> A.Ag:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.rft.at(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.rft.key(q))), es)

def act.abs.cl(m: Maybe<&2, A.Ag>) -> ActAbsSt:
  match m:
    case Some{b}:
      AbsOpen{b}
    case None{}:
      AbsFail{}

# a type-valued definition opened: its unfolding, else its clause at the
# arguments (act.ev.cls)
def act.abs.open(t: A.Ag, +q: A.AgQ, +es: A.Ag, +env: ActEnv) -> ActAbsSt:
  match t:
    case A.AgNone{}:
      act.abs.cl(act.ev.cls(act.tcl.cls(env, q), act.ev.args(es, env)))
    case t:
      AbsOpen{act.inline(1024n, t, env)}

def act.abs.sym(s: ActSym, +q: A.AgQ, +es: A.Ag, +env: ActEnv) -> ActAbsSt:
  match s:
    case ActSym{m, n, k, ms, ar, AbEq{}, fs, c, cp}:
      AbsEq{A.AgDef{q, es}}
    case ActSym{m, n, A.AkData{}, ms, ar, b, Nil{}, c, cp}:
      AbsDone{}
    case ActSym{m, n, A.AkData{}, ms, ar, b, cs, c, cp}:
      AbsFam{A.AgDef{q, es}, cs}
    case ActSym{+m, n, A.AkRecord{}, ms, ar, b, f <> Nil{}, +c, cp}:
      AbsWrap{act.ref.of(act.is.here(env, m), env, m, c), act.rft(env, q, es)}
    case ActSym{m, n, A.AkFunction{}, ms, ar, b, fs, c, cp}:
      act.abs.open(act.unfold(env, q, es), q, es, env)
    case _:
      AbsFail{}

def act.abs.def(t: A.Ag, +env: ActEnv) -> ActAbsSt:
  match t:
    case A.AgDef{+q, +es}:
      act.abs.sym(act.sym(env, q), q, es, env)
    case _:
      AbsFail{}

def act.abs.step(t: A.Ag, +env: ActEnv) -> ActAbsSt:
  match t:
    case A.AgEl{s, a}:
      act.abs.def(a, env)
    case t:
      act.abs.def(t, env)

def act.abs.match(+x: List<&2, U32>, cs: T.Bt) -> T.Bt:
  T.BtMatch{T.tba.args([T.BtVar{x}]), cs}

# Bend cannot match on an equation, so an absurd one between two
# constructors (`not-injective {false} {true} ()`, `suc n ≡ 0`) is
# refuted by a rewrite through a motive that is Unit at its left side and
# Empty at its right, and Empty.absurd at the goal (Bend's GUIDE: rewrite a
# clash through disc(_)).  disc(_) is Bool.pick over a Bool that is True
# at the left side: for Bool, _ itself (or its negation); for Nat, whether
# _ is 0n against whether the left side is (a zero/suc clash).  Other types:
# a gap.
def act.bt.app(+f: String, args: List<&2, T.Bt>) -> T.Bt:
  T.BtApp{T.BtVar{S.b(f)}, T.tba.args(args)}

def act.abs.same(b: T.Bt, +a: T.Bt) -> T.Bt:
  act.bt.app("Bool.pick", [T.BtVar{S.b("Bool")}, b, a, act.bt.app("Bool.not", [a])])

def act.abs.iz(t: T.Bt) -> T.Bt:
  act.bt.app("Nat.is_eq", [t, T.BtNat{S.b("0")}])

def act.abs.disc(+ty: List<&2, U32>, +a: T.Bt) -> Maybe<&2, T.Bt>:
  Bool.pick(Maybe<&2, T.Bt>, S.eq(ty, S.b("Bool")), Some{act.abs.same(T.BtWild{}, a)}, Bool.pick(Maybe<&2, T.Bt>, S.eq(ty, S.b("Nat")), Some{act.abs.same(act.abs.iz(T.BtWild{}), act.abs.iz(a))}, None{}))

def act.abs.disc.ty(+ty: T.Bt, +a: T.Bt) -> Maybe<&2, T.Bt>:
  match ty:
    case T.BtVar{n}:
      act.abs.disc(n, a)
    case _:
      None{}

def act.abs.refute(m: Maybe<&2, T.Bt>, +x: List<&2, U32>, +goal: T.Bt) -> T.Bt:
  match m:
    case Some{d}:
      T.BtExpr{act.bt.app("Empty.absurd", [T.BtDead{goal}, T.BtRw{T.BtVar{x}, act.bt.app("Bool.pick", [T.BtType{}, d, T.BtVar{S.b("Unit")}, T.BtVar{S.b("Empty")}]), T.BtExpr{T.BtCon{S.b("Unit"), T.BtANil{}}}}])}
    case None{}:
      T.BtExpr{act.todo("an absurd pattern on an equation of a type other than Bool or Nat")}

# A clash between two constructors of another type (`strict _ ≡
# nonstrict _`, IsStrict (nonstrict _)) is refuted through a lambda-match
# motive, {\{C: (_ => .. => Unit); (_ => Empty)} : T -> Type}(_), Unit at
# the left side's constructor C (its fields' lambdas) and Empty at any
# other (Bend 2.0.39 checks it, /tmp/bx/lm/a.bend); T: the sides' type.
def act.abs.lm.arm(n: Nat) -> String:
  match n:
    case 0n:
      "Unit"
    case 1n+p:
      "_ => " ++ act.abs.lm.arm(p)

def act.abs.lm.of(+c: List<&2, U32>, +n: Nat, ty: T.Bt) -> T.Bt:
  +raw = List.append(&2, U32, S.b("\\{"), List.append(&2, U32, c, S.b(": (" ++ act.abs.lm.arm(n) ++ "); (_ => Empty)}")))
  T.BtApp{T.BtAnn{T.BtVar{raw}, T.BtPi{T.BmLive{}, S.b("_"), False{}, ty, T.BtType{}}}, T.tba.args([T.BtWild{}])}

def act.abs.refute.m(+p: T.Bt, +x: List<&2, U32>, +goal: T.Bt) -> T.Bt:
  T.BtExpr{act.bt.app("Empty.absurd", [T.BtDead{goal}, T.BtRw{T.BtVar{x}, p, T.BtExpr{T.BtCon{S.b("Unit"), T.BtANil{}}}}])}

# the motive for a: a constructor other than b's head
def act.abs.lm.ab(a: T.Bt, b: T.Bt, ty: T.Bt) -> Maybe<&2, T.Bt>:
  match a b:
    case T.BtCon{+ca, args} T.BtCon{+cb, bargs}:
      Bool.pick(Maybe<&2, T.Bt>, S.eq(ca, cb), None{}, Some{act.abs.lm.of(ca, List.length(&2, T.Bt, act.spine.list(args)), ty)})
    case _ _:
      None{}

def act.abs.refute.or(m: Maybe<&2, T.Bt>, n: Maybe<&2, T.Bt>, +x: List<&2, U32>, +goal: T.Bt) -> T.Bt:
  match m n:
    case Some{d} _:
      act.abs.refute(Some{d}, x, goal)
    case None{} Some{p}:
      act.abs.refute.m(p, x, goal)
    case None{} None{}:
      act.abs.refute(None{}, x, goal)

def act.abs.clash(t: T.Bt, +x: List<&2, U32>, +goal: T.Bt) -> T.Bt:
  match t:
    case T.BtEq{+ty, +a, +b}:
      act.abs.refute.or(act.abs.disc.ty(ty, a), act.abs.lm.ab(act.undead(a), act.undead(b), ty), x, goal)
    case _:
      T.BtExpr{act.todo("an absurd pattern on an equation agda2bend could not read")}

# An absurd pattern on an indexed family (`n≮0 ()`: suc n ≤ 0): x is
# matched, and each constructor's case refutes one of its index equations
# whose sides have different heads, the family's index (left) against the
# constructor's (its equation field's name: act.ix.tag), as act.abs.refute
# does an equation's.  A constructor none of whose equations clashes at the
# head (`suc m ≤ suc n` with m ≤ n absurd) is a gap.
# Nat's _+_ (Agda.Builtin.Nat's, by its printed name) at a literal or a
# suc first: suc at the head (`Vec A (1 + n)`), as Bend computes it
def act.abs.isplus(+f: List<&2, U32>) -> Bool:
  Bool.or(S.eq(f, S.b("plus")), S.eq(List.take(&2, U32, List.reverse(&2, U32, f), 5n), List.reverse(&2, U32, S.b(".plus"))))

def act.abs.hd.plus(b: Bool, a: T.Bt, +t: T.Bt) -> T.Bt:
  match b a:
    case True{} T.BtArgs{T.BtNat{+s}, rest}:
      Bool.pick(T.Bt, S.eq(s, S.b("0")), t, T.BtSucc{T.BtWild{}})
    case True{} T.BtArgs{T.BtSucc{x}, rest}:
      T.BtSucc{T.BtWild{}}
    case _ _:
      t

def act.abs.hd(+t: T.Bt) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+f}, a}:
      act.abs.hd.plus(act.abs.isplus(f), a, t)
    case T.BtDead{a}:
      a
    case t:
      t

def act.abs.clashes1(+h: String, a: T.Bt) -> Bool:
  match a:
    case T.BtSucc{t}:
      String.eq(h, "ix_eqz")
    case T.BtNat{+s}:
      Bool.pick(Bool, S.eq(s, S.b("0")), String.eq(h, "ix_eqs"), String.eq(h, "ix_eqz"))
    case T.BtCon{+c, args}:
      Bool.or(Bool.and(S.eq(c, S.b("True")), String.eq(h, "ix_eqf")), Bool.and(S.eq(c, S.b("False")), String.eq(h, "ix_eqt")))
    case _:
      False{}

def act.abs.clashes(+h: String, +a: T.Bt) -> Bool:
  act.abs.clashes1(h, act.abs.hd(a))

def act.abs.tagty(+h: String) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, Bool.or(String.eq(h, "ix_eqt"), String.eq(h, "ix_eqf")), S.b("Bool"), S.b("Nat"))

def act.tag.base(+h: String) -> String:
  S.str(List.take(&2, U32, S.b(h), 6n))

# a constructor's entry by key (act.sym.key, which comes later in the file)
def act.abs.sym.key(+env: ActEnv, k: String) -> ActSym:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.sym.got(Map.get(ActSym, act.sym0(), tab, k))

# a key up to its first '/'
def act.cq.key(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      Bool.pick(List<&2, U32>, U32.is_eq(h, 47), Nil{}, h <> act.cq.key(t))

# the Bend name of the constructor an ix_eqc:KEY tag names (empty for
# another tag)
def act.abs.sym.ref(s: ActSym, +env: ActEnv) -> List<&2, U32>:
  match s:
    case ActSym{+m, n, k, ms, ar, b, fs, c, cp}:
      act.ref.of(act.is.here(env, m), env, m, n)

def act.abs.ctag.ref(+h0: String, +env: ActEnv) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, String.eq(act.tag.base(h0), "ix_eqc"), act.abs.sym.ref(act.abs.sym.key(env, S.str(act.cq.key(List.drop(&2, U32, S.b(h0), 7n)))), env), Nil{})

def act.abs.nonnil(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      True{}

# the motive refuting the family's index u against the constructor's
# (tag h0): both constructors, different (ty: the index's type, a hole
# when unknown)
def act.abs.lm.ix2(+r: List<&2, U32>, +c: List<&2, U32>, +n: Nat, t: T.Bt) -> Maybe<&2, T.Bt>:
  Bool.pick(Maybe<&2, T.Bt>, Bool.or(Bool.not(act.abs.nonnil(r)), S.eq(c, r)), None{}, Some{act.abs.lm.of(c, n, t)})

def act.abs.lm.ix(u: T.Bt, +h0: String, ty: Maybe<&2, T.Bt>, +env: ActEnv) -> Maybe<&2, T.Bt>:
  match u ty:
    case T.BtCon{+c, args} Some{t}:
      act.abs.lm.ix2(act.abs.ctag.ref(h0, env), c, List.length(&2, T.Bt, act.spine.list(args)), t)
    case _ _:
      None{}

def act.abs.ty.hd(tys: List<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match tys:
    case h <> t:
      Some{h}
    case Nil{}:
      None{}

def act.abs.ty.tl(tys: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match tys:
    case h <> t:
      t
    case Nil{}:
      Nil{}

def act.abs.fam.lm(m: Maybe<&2, T.Bt>, +x: List<&2, U32>, +goal: T.Bt, rest: T.Bt) -> T.Bt:
  match m:
    case Some{p}:
      act.abs.refute.m(p, x, goal)
    case None{}:
      rest

# A family's index the fold cannot read the head of, a call (`pred 0`, `0
# ∸ suc n`, as Agda's case tree leaves it), against a zero/suc or
# true/false: Bend computes the call, so the refutation through disc(_)
# checks when the call's value clashes (pred-cancel-<, m≮m∸n; 2026-10-29).
# Tried only when no index refutes at its head, the first such equation.
def act.abs.unk(t: T.Bt) -> Bool:
  match t:
    case T.BtApp{T.BtVar{f}, a}:
      True{}
    case _:
      False{}

def act.abs.known.tag(+h: String) -> Bool:
  Bool.or(Bool.or(String.eq(h, "ix_eqz"), String.eq(h, "ix_eqs")), Bool.or(String.eq(h, "ix_eqt"), String.eq(h, "ix_eqf")))

def act.abs.fam.unk(fs: List<&2, String>, ixs: List<&2, T.Bt>, +x: List<&2, U32>, +i: Nat, +goal: T.Bt, +why: String) -> T.Bt:
  match fs ixs:
    case +h0 <> ft a <> at:
      +h = act.tag.base(h0)
      +u = act.undead(a)
      Bool.pick(T.Bt, Bool.and(act.abs.known.tag(h), act.abs.unk(act.abs.hd(u))), act.abs.refute(act.abs.disc(act.abs.tagty(h), u), act.at(x, i), goal), act.abs.fam.unk(ft, at, x, 1n+i, goal, why))
    case _ _:
      T.BtExpr{T.BtTodo{S.b("an absurd pattern on a family a constructor of which no index equation refutes at the head (" ++ why ++ ")")}}

def act.abs.fam.pick(fs: List<&2, String>, ixs: List<&2, T.Bt>, +tys: List<&2, T.Bt>, +x: List<&2, U32>, +i: Nat, +goal: T.Bt, +why: String, +env: ActEnv, fb: T.Bt) -> T.Bt:
  match fs ixs:
    case +h0 <> ft a <> at:
      +h = act.tag.base(h0)
      +u = act.undead(a)
      Bool.pick(T.Bt, act.abs.clashes(h, u), act.abs.refute(act.abs.disc(act.abs.tagty(h), u), act.at(x, i), goal), act.abs.fam.lm(act.abs.lm.ix(act.abs.hd(u), h0, act.abs.ty.hd(tys), env), act.at(x, i), goal, act.abs.fam.pick(ft, at, act.abs.ty.tl(tys), x, 1n+i, goal, why, env, fb)))
    case _ _:
      fb

def act.abs.tags(fs: List<&2, String>, +n: Nat) -> String:
  match fs:
    case Nil{}:
      "of " ++ Nat.show(n) ++ " indices"
    case h <> t:
      h ++ " " ++ act.abs.tags(t, n)

def act.abs.wilds(n: Nat) -> List<&2, T.Bt>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      T.BtWild{} <> act.abs.wilds(p)

def act.abs.eqpvs(fs: List<&2, String>, +x: List<&2, U32>, +i: Nat) -> List<&2, T.Bt>:
  match fs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BtPv{T.BmLive{}, act.at(x, i)} <> act.abs.eqpvs(t, x, 1n+i)

def act.abs.fam.c(s: ActSym, +ixs: List<&2, T.Bt>, +tys: List<&2, T.Bt>, +x: List<&2, U32>, +env: ActEnv, +goal: T.Bt, rest: T.Bt) -> T.Bt:
  match s:
    case ActSym{+m, +n, A.AkConstructor{}, ms, ar, b, +fs, c, cp}:
      +y = List.append(&2, U32, x, S.b("_ix"))
      +lix = act.list.last(List.length(&2, String, fs), ixs)
      +why = act.abs.tags(fs, List.length(&2, T.Bt, ixs))
      T.BtCase{T.tba.args([T.BtCon{act.ref.of(act.is.here(env, m), env, m, n), T.tba.args(List.append(&2, T.Bt, act.abs.wilds(ar), act.abs.eqpvs(fs, y, 1n)))}]), act.abs.fam.pick(fs, lix, act.list.last(List.length(&2, String, fs), tys), y, 1n, goal, why, env, act.abs.fam.unk(fs, lix, y, 1n, goal, why)), rest}
    case _:
      T.BtCase{T.tba.args([T.BtWild{}]), T.BtExpr{act.todo("an absurd pattern on a family whose constructor the symbol table does not have")}, rest}

def act.abs.fam.cs(cs: List<&2, String>, +ixs: List<&2, T.Bt>, +tys: List<&2, T.Bt>, +x: List<&2, U32>, +env: ActEnv, +goal: T.Bt) -> T.Bt:
  match cs:
    case Nil{}:
      T.BtCEnd{}
    case k <> rest:
      act.abs.fam.c(act.abs.sym.key(env, k), ixs, tys, x, env, goal, act.abs.fam.cs(rest, ixs, tys, x, env, goal))

# the domains of a type's Pis at a spine's arguments (each with the
# arguments before it substituted), in order
def act.pi.inst(d: Bool, b: A.Ag, +v: A.Ag) -> A.Ag:
  match d:
    case True{}:
      asb.subst(b, 0n, [v], 1n)
    case False{}:
      b

def act.pi.doms(fuel: Nat, t: A.Ag, es: A.Ag) -> List<&2, A.Ag>:
  match fuel t es:
    case 1n+f A.AgEl{s, A.AgPi{i, x, a, d, b}} A.AgEApp{ei, +v, rest}:
      a <> act.pi.doms(f, act.pi.inst(d, b, v), rest)
    case _ _ _:
      Nil{}

def act.abs.tys.t(ts: List<&2, A.Ag>, +ctx: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.Bt>:
  match ts:
    case Nil{}:
      Nil{}
    case h <> t:
      act.t(h, ctx, env) <> act.abs.tys.t(t, ctx, env)

def act.abs.cbody(c: ActCopy) -> A.Ag:
  match c:
    case ActCopy{n, b}:
      b

def act.abs.fty(+env: ActEnv, +k: String) -> A.Ag:
  match env:
    case ActEnv{mod, tab, al, +unf}:
      act.abs.cbody(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, "fty:" ++ k)))

# an indexed family's argument types (its data type's type, "fty:" in the
# unfoldings, at its arguments)
def act.abs.ixtys(t: A.Ag, +ctx: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.Bt>:
  match t:
    case A.AgDef{+q, +es}:
      act.abs.tys.t(act.pi.doms(256n, act.abs.fty(env, act.key(q)), es), ctx, env)
    case _:
      Nil{}

def act.abs.fam(t: T.Bt, +tys: List<&2, T.Bt>, cs: List<&2, String>, +x: List<&2, U32>, +env: ActEnv, +goal: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{r, args}:
      act.abs.match(x, act.abs.fam.cs(cs, act.spine.list(args), tys, x, env, goal))
    case _:
      T.BtExpr{act.todo("an absurd pattern on a family agda2bend could not read")}

# the elimination of x, a step at a time (ctx: the context of x's type;
# goal: the clause's)
def act.abs.elim(fuel: Nat, st: ActAbsSt, +x: List<&2, U32>, +env: ActEnv, +ctx: List<&2, T.Bt>, +goal: T.Bt) -> T.Bt:
  match fuel st:
    case _ AbsDone{}:
      act.abs.match(x, T.BtCEnd{})
    case 1n+f AbsOpen{t}:
      act.abs.elim(f, act.abs.step(t, env), x, env, ctx, goal)
    case 1n+f AbsWrap{c, t}:
      +y = List.append(&2, U32, x, S.b("_f"))
      act.abs.match(x, T.BtCase{T.tba.args([T.BtCon{c, T.tba.args([T.BtPv{T.BmLive{}, y}])}]), act.abs.elim(f, act.abs.step(t, env), y, env, ctx, goal), T.BtCEnd{}})
    case 1n+f AbsEq{t}:
      act.abs.clash(act.t(act.inline(100000n, t, env), ctx, env), x, goal)
    case 1n+f AbsFam{t, cs}:
      +ti = act.inline(100000n, t, env)
      act.abs.fam(act.t(ti, ctx, env), act.abs.ixtys(ti, ctx, env), cs, x, env, goal)
    case _ _:
      T.BtExpr{act.todo("an absurd pattern on a type agda2bend cannot see is empty")}

# a clause's first top-level absurd pattern variable: its parameter and type
type ActAbs is Data:
  ActAbs{x: List<&2, U32>, ty: A.Ag, ix: Nat}

def act.tel.nth(tel: A.Ag, n: Nat) -> A.Ag:
  match tel n:
    case A.AgTel{x, i, ty, rest} 0n:
      ty
    case A.AgTel{x, i, ty, rest} 1n+p:
      act.tel.nth(rest, p)
    case _ _:
      A.AgNone{}

def act.abs.find(ps: A.Ag, ents: List<&2, T.Bt>, +tel: A.Ag, +n: Nat) -> Maybe<&2, ActAbs>:
  match ps ents:
    case A.AgPArg{i, x, A.AgPVar{v, +ix, A.AkAbsurd{}}, rest} e <> et:
      Some{ActAbs{act.var.name(e), act.tel.nth(tel, Nat.sub(Nat.sub(n, 1n), ix)), ix}}
    case A.AgPArg{i, x, p, rest} e <> et:
      act.abs.find(rest, et, tel, n)
    case _ _:
      None{}

# a clause's body: an absurd one's elimination, else the body translated
def act.abs.body(m: Maybe<&2, ActAbs>, body: A.Ag, +ctx: List<&2, T.Bt>, +env: ActEnv, +goal: T.Bt) -> T.Bt:
  match m body:
    case Some{ActAbs{x, ty, ix}} A.AgAbsurd{}:
      act.abs.elim(16n, act.abs.step(ty, env), x, env, List.drop(&2, T.Bt, ctx, 1n+ix), goal)
    case _ body:
      T.BtExpr{act.t(act.inline(100000n, body, env), ctx, env)}

# the parameters some clause has an absurd pattern variable at (they must
# be live, as a split one: the elimination matches them)
def act.abs.one(p: A.Ag) -> Bool:
  match p:
    case A.AgPVar{x, n, A.AkAbsurd{}}:
      True{}
    case _:
      False{}

def act.abs.ps(ps: A.Ag) -> List<&2, Bool>:
  match ps:
    case A.AgPArg{i, x, p, rest}:
      act.abs.one(p) <> act.abs.ps(rest)
    case _:
      Nil{}

# Dotted constructor fields (`≤-pred (s≤s {.m} {.n} p) = p`): Agda's
# unification makes the field the outer variable m; Bend has the field, d,
# and an index equation e : {1n+m == 1n+d}.  The case binds d (act.top.d:
# m_dot), the body reads m as d, and a rewrite before it turns the goal's m
# into d: %h : G[m := a2b_pred(_)] with h = Equal.sym(Nat, 1n+m, 1n+d, e)
# (a2b_pred: Nat's predecessor, a def the module gets when it uses it,
# Agda2Bend.bend a2b.helpers).  Only for an equation suc^k(d), k >= 1,
# whose index is suc^k of the outer variable, in a case with no other
# rewrite, a variable dotted once; any other dotted field is a wildcard as
# before.
type ActDs is Data:
  ActDs{d: List<&2, U32>, s: List<&2, U32>, k: Nat, e: List<&2, U32>, i: T.Bt}

type ActDe is Data:
  ActDe{j: Nat, o: Nat, tag: String}

type ActDk is Data:
  ActDk{j: Nat, o: Nat, k: Nat}

def act.nil.ps(xs: List<&2, T.BParam>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _:
      False{}

def act.nil.bt(xs: List<&2, T.Bt>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _:
      False{}

def act.rw.none(+rw: ActRw) -> Bool:
  match rw:
    case ActRw{rs, ds}:
      act.nil.bt(rs)

# the position a dotted field's name stands for
def act.ds.dot(+bs: List<&2, ActBind>, +dn: List<&2, U32>) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case ActBDot{+p, +x} <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(x, dn), Some{p}, act.ds.dot(t, dn))
    case ActBind{p, v} <> t:
      act.ds.dot(t, dn)

def act.ds.count(+bs: List<&2, ActBind>, +dn: List<&2, U32>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case ActBDot{p, +x} <> t:
      Nat.add(Bool.pick(Nat, S.eq(x, dn), 1n, 0n), act.ds.count(t, dn))
    case ActBind{p, v} <> t:
      act.ds.count(t, dn)

def act.ds.is.dot(+bs: List<&2, ActBind>, +dn: List<&2, U32>) -> Bool:
  Bool.not(Nat.is_eq(act.ds.count(bs, dn), 0n))

def act.bt.sucs(k: Nat, t: T.Bt) -> T.Bt:
  match k:
    case 0n:
      t
    case 1n+p:
      T.BtSucc{act.bt.sucs(p, t)}

def act.bt.preds(k: Nat, t: T.Bt) -> T.Bt:
  match k:
    case 0n:
      t
    case 1n+p:
      act.bt.app("a2b_pred", [act.bt.preds(p, t)])

def act.abs.lit(+s: List<&2, U32>) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, S.eq(s, S.b("1")), Some{1n}, Bool.pick(Maybe<&2, Nat>, S.eq(s, S.b("2")), Some{2n}, Bool.pick(Maybe<&2, Nat>, S.eq(s, S.b("3")), Some{3n}, Bool.pick(Maybe<&2, Nat>, S.eq(s, S.b("4")), Some{4n}, None{}))))

def act.abs.nplus3(m: Maybe<&2, Nat>, b: T.Bt, +t: T.Bt) -> T.Bt:
  match m:
    case Some{k}:
      act.bt.sucs(k, b)
    case None{}:
      t

def act.abs.nplus2(isp: Bool, a: T.Bt, b: T.Bt, +t: T.Bt) -> T.Bt:
  match isp a:
    case True{} T.BtNat{+s}:
      act.abs.nplus3(act.abs.lit(s), b, t)
    case _ _:
      t

# k + b (_+_ at a literal 1-4 first) as suc^k(b), the form act.ds and act.sd
# read an index in (Bend computes the one to the other)
def act.abs.nplus(+t: T.Bt) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+f}, T.BtArgs{a, T.BtArgs{b, T.BtANil{}}}}:
      act.abs.nplus2(act.abs.isplus(f), a, b, t)
    case t:
      t

def act.ds.is(k: Nat, t: T.Bt, +s: List<&2, U32>) -> Bool:
  match k t:
    case 0n T.BtVar{x}:
      S.eq(x, s)
    case 1n+p T.BtSucc{a}:
      act.ds.is(p, a, s)
    case 1n+p T.BtDead{a}:
      act.ds.is(1n+p, a, s)
    case _ _:
      False{}

# a top pattern's equation fields: place, ordinal among them, tag
def act.ds.eqs(fs: List<&2, T.Bt>, +j: Nat, +o: Nat) -> List<&2, ActDe>:
  match fs:
    case Nil{}:
      Nil{}
    case T.BtPv{m, +nm} <> +t:
      +ph = act.is.ph(nm)
      +r = act.ds.eqs(t, 1n+j, Nat.add(Bool.pick(Nat, ph, 1n, 0n), o))
      Bool.pick(List<&2, ActDe>, ph, ActDe{j, o, S.str(nm)} <> r, r)
    case h <> t:
      act.ds.eqs(t, 1n+j, o)

# the k (1-4) of a tag "ix_eqs_k<k>_f<i>", 0 when it is not one
def act.ds.k(+tag: String, +i: Nat, k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+p):
      Bool.pick(Nat, String.eq(tag, "ix_eqs_k" ++ Nat.show(1n+p) ++ "_f" ++ Nat.show(i)), 1n+p, act.ds.k(tag, i, p))

def act.ds.find(es: List<&2, ActDe>, +i: Nat) -> Maybe<&2, ActDk>:
  match es:
    case Nil{}:
      None{}
    case ActDe{+j, +o, +tag} <> t:
      +kk = act.ds.k(tag, i, 4n)
      Bool.pick(Maybe<&2, ActDk>, Nat.is_eq(kk, 0n), act.ds.find(t, i), Some{ActDk{j, o, kk}})

def act.ds.nth(xs: List<&2, T.Bt>, o: Nat) -> T.Bt:
  match xs o:
    case h <> t 0n:
      h
    case h <> t 1n+p:
      act.ds.nth(t, p)
    case _ _:
      T.BtWild{}

# whether s is one of the def's parameters (a dotted field stands for an
# unsplit one only: a split one's variables are what a recursive call
# shrinks)
def act.ds.param(ps: List<&2, T.BParam>, +s: List<&2, U32>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case T.BParam{m, +n, ty} <> t:
      Bool.or(S.eq(n, s), act.ds.param(t, s))

def act.ds.one(m: Maybe<&2, ActDk>, +dn: List<&2, U32>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +pos: Nat, +hps: List<&2, T.BParam>) -> List<&2, ActDs>:
  match m:
    case None{}:
      Nil{}
    case Some{ActDk{+j, +o, +k}}:
      +i = act.abs.nplus(act.undead(act.goal(svars, q, act.ds.nth(ixs, o))))
      +s = act.var.name(act.bind.find(pos, bs))
      Bool.pick(List<&2, ActDs>, Bool.and(act.ds.is(k, i, s), act.ds.param(hps, s)), [ActDs{dn, s, k, List.append(&2, U32, act.at(xn, j), S.b("_eq")), i}], Nil{})

def act.ds.pv(m: Maybe<&2, Nat>, +dn: List<&2, U32>, +i: Nat, +es: List<&2, ActDe>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>) -> List<&2, ActDs>:
  match m:
    case None{}:
      Nil{}
    case Some{+pos}:
      act.ds.one(act.ds.find(es, i), dn, xn, ixs, svars, q, bs, pos, hps)

def act.ds.fields(fs: List<&2, T.Bt>, +i: Nat, +es: List<&2, ActDe>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>) -> List<&2, ActDs>:
  match fs:
    case Nil{}:
      Nil{}
    case T.BtPv{m, +nm} <> t:
      List.append(&2, ActDs, act.ds.pv(act.ds.dot(bs, nm), nm, i, es, xn, ixs, svars, q, bs, hps), act.ds.fields(t, 1n+i, es, xn, ixs, svars, q, bs, hps))
    case h <> t:
      act.ds.fields(t, 1n+i, es, xn, ixs, svars, q, bs, hps)

def act.ds.top(p: T.Bt, +x: T.Bt, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>) -> List<&2, ActDs>:
  match p:
    case T.BtCon{c, +args}:
      +fs = act.spine.list(args)
      +es = act.ds.eqs(fs, 1n, 0n)
      +xn = act.var.name(x)
      act.ds.fields(fs, 1n, es, xn, act.list.last(List.length(&2, ActDe, es), act.ty.args(act.param.ty(hps, xn))), svars, q, bs, hps)
    case _:
      Nil{}

def act.ds.tops(ps: T.Bt, xs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>) -> List<&2, ActDs>:
  match ps xs:
    case T.BtArgs{p, rest} +x <> xt:
      List.append(&2, ActDs, act.ds.top(p, x, svars, q, bs, hps), act.ds.tops(rest, xt, svars, q, bs, hps))
    case _ _:
      Nil{}

# how many dotted fields stand for the position (one: act.ds rewrites)
def act.ds.npos.go(bs: List<&2, ActBind>, +p: Nat) -> Nat:
  match bs:
    case Nil{}:
      0n
    case ActBDot{+q, x} <> t:
      Nat.add(Bool.pick(Nat, Nat.is_eq(q, p), 1n, 0n), act.ds.npos.go(t, p))
    case b <> t:
      act.ds.npos.go(t, p)

def act.ds.npos(+bs: List<&2, ActBind>, m: Maybe<&2, Nat>) -> Nat:
  match m:
    case Some{p}:
      act.ds.npos.go(bs, p)
    case None{}:
      0n

# the dotted fields bound once only
def act.ds.uniq(ds: List<&2, ActDs>, +bs: List<&2, ActBind>) -> List<&2, ActDs>:
  match ds:
    case Nil{}:
      Nil{}
    case ActDs{+d, +s, +k, +e, +i} <> +t:
      +r = act.ds.uniq(t, bs)
      Bool.pick(List<&2, ActDs>, Nat.is_eq(act.ds.npos(bs, act.ds.dot(bs, d)), 1n), ActDs{d, s, k, e, i} <> r, r)

def act.ds.names(ds: List<&2, ActDs>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      Nil{}
    case ActDs{d, s, k, e, i} <> t:
      d <> act.ds.names(t)

def act.ds.bind1(m: Maybe<&2, Nat>, +d: List<&2, U32>) -> List<&2, ActBind>:
  match m:
    case None{}:
      Nil{}
    case Some{p}:
      [ActBind{p, T.BtVar{d}}]

# the bindings the active dotted fields make (the outer variable read as
# the field), ahead of the others
def act.ds.binds(ds: List<&2, ActDs>, +bs: List<&2, ActBind>) -> List<&2, ActBind>:
  match ds:
    case Nil{}:
      Nil{}
    case ActDs{+d, s, k, e, i} <> t:
      List.append(&2, ActBind, act.ds.bind1(act.ds.dot(bs, d), d), act.ds.binds(t, bs))

# a pattern's dotted fields that are not active, wildcards again
def act.ds.undot(t: T.Bt, +on: List<&2, List<&2, U32>>, +bs: List<&2, ActBind>) -> T.Bt:
  match t:
    case T.BtArgs{a, rest}:
      T.BtArgs{act.ds.undot(a, on, bs), act.ds.undot(rest, on, bs)}
    case T.BtCon{c, a}:
      T.BtCon{c, act.ds.undot(a, on, bs)}
    case T.BtSucc{a}:
      T.BtSucc{act.ds.undot(a, on, bs)}
    case T.BtPv{+m, +nm}:
      Bool.pick(T.Bt, Bool.and(act.ds.is.dot(bs, nm), Bool.not(act.used(nm, on))), T.BtWild{}, T.BtPv{m, nm})
    case t:
      t

def act.ds.ndots(bs: List<&2, ActBind>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case ActBDot{p, x} <> t:
      1n+act.ds.ndots(t)
    case ActBind{p, v} <> t:
      act.ds.ndots(t)

def act.ds.dbgp(t: T.Bt) -> String:
  match t:
    case T.BtArgs{a, rest}:
      act.ds.dbgp(a) ++ "," ++ act.ds.dbgp(rest)
    case T.BtCon{c, a}:
      S.str(c) ++ "{" ++ act.ds.dbgp(a) ++ "}"
    case T.BtPv{m, nm}:
      S.str(nm)
    case T.BtWild{}:
      "_"
    case _:
      "?"

# the rewrites before the body, each on the goal the previous one leaves
def act.ds.wrap(ds: List<&2, ActDs>, +goal: T.Bt, body: T.Bt) -> T.Bt:
  match ds:
    case Nil{}:
      body
    case ActDs{+d, +s, +k, e, i} <> t:
      +h = List.append(&2, U32, d, S.b("_sym"))
      T.BtLet{h, act.bt.app("Equal.sym", [T.BtDead{T.BtVar{S.b("Nat")}}, T.BtDead{i}, T.BtDead{act.bt.sucs(k, T.BtVar{d})}, T.BtVar{e}]), T.BtRw{T.BtVar{h}, T.tba.subst(goal, s, act.bt.preds(k, T.BtWild{})), act.ds.wrap(t, T.tba.subst(goal, s, T.BtVar{d}), body)}}

# Dotted fields at a variable that is no parameter (`lookup (x ∷ xs) (suc
# {.n} i)`, n Vec._∷_'s field; `≤-trans (s≤s p) (s≤s {.n} q)`): the case
# binds the field d too, proves h : {d == s} by suc's injectivity from the
# index equations (the field's own {I == suc^k(d)} and s's {I == suc^k(s)}
# at another top constructor pattern, or I itself suc^k(s), s a variable a
# split made), and casts each later field v of d's constructor whose type
# (the clause telescope's, which has s) mentions s: v = a2b_cast(Nat, k =>
# T[s := k], d, s, h, v) (a2b_cast: the rewrite of F(b) to F(a),
# Agda2Bend.bend a2b.helpers).  A variable dotted once only.
type ActSd is Data:
  ActSd{d: List<&2, U32>, s: List<&2, U32>, h: T.Bt, vs: List<&2, List<&2, U32>>}

type ActSl is Data:
  ActSl{e: List<&2, U32>, i: T.Bt, k: Nat}

def act.sd.same1(a: T.Bt, b: T.Bt) -> Bool:
  match a b:
    case T.BtVar{x} T.BtVar{y}:
      S.eq(x, y)
    case T.BtSucc{x} T.BtSucc{y}:
      act.sd.same1(x, y)
    case T.BtNat{x} T.BtNat{y}:
      S.eq(x, y)
    case T.BtDead{x} y:
      act.sd.same1(x, y)
    case x T.BtDead{y}:
      act.sd.same1(x, y)
    case _ _:
      False{}

# two index terms the same (variables, suc, literals)
def act.sd.same(a: T.Bt, b: T.Bt) -> Bool:
  act.sd.same1(act.undead(a), act.undead(b))

def act.sd.idx(fs: List<&2, T.Bt>, +s: List<&2, U32>, +i: Nat) -> Maybe<&2, Nat>:
  match fs:
    case Nil{}:
      None{}
    case T.BtPv{m, +nm} <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(nm, s), Some{i}, act.sd.idx(t, s, 1n+i))
    case h <> t:
      act.sd.idx(t, s, 1n+i)

def act.sd.at.k(m: Maybe<&2, ActDk>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt) -> Maybe<&2, ActSl>:
  match m:
    case None{}:
      None{}
    case Some{ActDk{j, o, k}}:
      Some{ActSl{List.append(&2, U32, act.at(xn, j), S.b("_eq")), act.abs.nplus(act.undead(act.goal(svars, q, act.ds.nth(ixs, o)))), k}}

def act.sd.at(m: Maybe<&2, Nat>, +es: List<&2, ActDe>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt) -> Maybe<&2, ActSl>:
  match m:
    case None{}:
      None{}
    case Some{+i}:
      act.sd.at.k(act.ds.find(es, i), xn, ixs, svars, q)

def act.sd.or(a: Maybe<&2, ActSl>, b: Maybe<&2, ActSl>) -> Maybe<&2, ActSl>:
  match a:
    case None{}:
      b
    case a:
      a

# where s is a field of a top constructor pattern: its equation, index, k
def act.sd.loc(ps: T.Bt, xs: List<&2, T.Bt>, +s: List<&2, U32>, +svars: List<&2, T.Bt>, +q: T.Bt, +hps: List<&2, T.BParam>) -> Maybe<&2, ActSl>:
  match ps xs:
    case T.BtArgs{T.BtCon{c, +args}, rest} +x <> xt:
      +fs = act.spine.list(args)
      +es = act.ds.eqs(fs, 1n, 0n)
      +xn = act.var.name(x)
      act.sd.or(act.sd.at(act.sd.idx(fs, s, 1n), es, xn, act.list.last(List.length(&2, ActDe, es), act.ty.args(act.param.ty(hps, xn))), svars, q), act.sd.loc(rest, xt, s, svars, q, hps))
    case T.BtArgs{p, rest} x <> xt:
      act.sd.loc(rest, xt, s, svars, q, hps)
    case _ _:
      None{}

def act.sd.nat() -> T.Bt:
  T.BtDead{T.BtVar{S.b("Nat")}}

def act.sd.sym(+i: T.Bt, +a: T.Bt, e: T.Bt) -> T.Bt:
  act.bt.app("Equal.sym", [act.sd.nat(), T.BtDead{i}, T.BtDead{a}, e])

# {d == s} from e : {suc^k(d) == suc^k(s)}
def act.sd.inj(+k: Nat, +d: List<&2, U32>, +s: List<&2, U32>, e: T.Bt) -> T.Bt:
  act.bt.app("Equal.cong", [act.sd.nat(), act.sd.nat(), T.BtDead{T.BtLam{T.BmLive{}, S.b("a2b_y"), act.bt.preds(k, T.BtVar{S.b("a2b_y")})}}, T.BtDead{act.bt.sucs(k, T.BtVar{d})}, T.BtDead{act.bt.sucs(k, T.BtVar{s})}, e])

def act.sd.via(m: Maybe<&2, ActSl>, +k: Nat, +d: List<&2, U32>, +s: List<&2, U32>, +i: T.Bt, +ed: List<&2, U32>) -> Maybe<&2, T.Bt>:
  match m:
    case None{}:
      None{}
    case Some{ActSl{+es, +j, +k2}}:
      Bool.pick(Maybe<&2, T.Bt>, Bool.and(Nat.is_eq(k, k2), act.sd.same(i, j)), Some{act.sd.inj(k, d, s, act.bt.app("Equal.trans", [act.sd.nat(), T.BtDead{act.bt.sucs(k, T.BtVar{d})}, T.BtDead{i}, T.BtDead{act.bt.sucs(k, T.BtVar{s})}, act.sd.sym(i, act.bt.sucs(k, T.BtVar{d}), T.BtVar{ed}), T.BtVar{es}]))}, None{})

def act.sd.proof(+k: Nat, +d: List<&2, U32>, +s: List<&2, U32>, +i: T.Bt, +ed: List<&2, U32>, +svars: List<&2, T.Bt>, +q: T.Bt, +hps: List<&2, T.BParam>, +all: T.Bt, +allx: List<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  Bool.pick(Maybe<&2, T.Bt>, act.ds.is(k, i, s), Some{act.sd.inj(k, d, s, act.sd.sym(i, act.bt.sucs(k, T.BtVar{d}), T.BtVar{ed}))}, act.sd.via(act.sd.loc(all, allx, s, svars, q, hps), k, d, s, i, ed))

# a constructor pattern's fields that are variables (no equation field)
def act.sd.vs(fs: List<&2, T.Bt>) -> List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
      Nil{}
    case T.BtPv{m, +nm} <> +t:
      +r = act.sd.vs(t)
      Bool.pick(List<&2, List<&2, U32>>, act.is.ph(nm), r, nm <> r)
    case h <> t:
      act.sd.vs(t)

def act.sd.mk(m: Maybe<&2, T.Bt>, +d: List<&2, U32>, +s: List<&2, U32>, vs: List<&2, List<&2, U32>>) -> List<&2, ActSd>:
  match m:
    case None{}:
      Nil{}
    case Some{h}:
      [ActSd{d, s, h, vs}]

def act.sd.one(m: Maybe<&2, ActDk>, +dn: List<&2, U32>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +pos: Nat, +hps: List<&2, T.BParam>, +all: T.Bt, +allx: List<&2, T.Bt>, later: List<&2, T.Bt>) -> List<&2, ActSd>:
  match m:
    case None{}:
      Nil{}
    case Some{ActDk{+j, +o, +k}}:
      +i = act.abs.nplus(act.undead(act.goal(svars, q, act.ds.nth(ixs, o))))
      +s = act.var.name(act.bind.find(pos, bs))
      Bool.pick(List<&2, ActSd>, Bool.or(act.ds.param(hps, s), S.eq(s, S.b("r"))), Nil{}, act.sd.mk(act.sd.proof(k, dn, s, i, List.append(&2, U32, act.at(xn, j), S.b("_eq")), svars, q, hps, all, allx), dn, s, act.sd.vs(later)))

def act.sd.pv(m: Maybe<&2, Nat>, +dn: List<&2, U32>, +i: Nat, +es: List<&2, ActDe>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +all: T.Bt, +allx: List<&2, T.Bt>, later: List<&2, T.Bt>) -> List<&2, ActSd>:
  match m:
    case None{}:
      Nil{}
    case Some{+pos}:
      act.sd.one(act.ds.find(es, i), dn, xn, ixs, svars, q, bs, pos, hps, all, allx, later)

def act.sd.fields(fs: List<&2, T.Bt>, +i: Nat, +es: List<&2, ActDe>, +xn: List<&2, U32>, +ixs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +all: T.Bt, +allx: List<&2, T.Bt>) -> List<&2, ActSd>:
  match fs:
    case Nil{}:
      Nil{}
    case T.BtPv{m, +nm} <> +t:
      List.append(&2, ActSd, act.sd.pv(act.ds.dot(bs, nm), nm, i, es, xn, ixs, svars, q, bs, hps, all, allx, t), act.sd.fields(t, 1n+i, es, xn, ixs, svars, q, bs, hps, all, allx))
    case h <> t:
      act.sd.fields(t, 1n+i, es, xn, ixs, svars, q, bs, hps, all, allx)

def act.sd.top(p: T.Bt, +x: T.Bt, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +all: T.Bt, +allx: List<&2, T.Bt>) -> List<&2, ActSd>:
  match p:
    case T.BtCon{c, +args}:
      +fs = act.spine.list(args)
      +es = act.ds.eqs(fs, 1n, 0n)
      +xn = act.var.name(x)
      act.sd.fields(fs, 1n, es, xn, act.list.last(List.length(&2, ActDe, es), act.ty.args(act.param.ty(hps, xn))), svars, q, bs, hps, all, allx)
    case _:
      Nil{}

def act.sd.tops(ps: T.Bt, xs: List<&2, T.Bt>, +svars: List<&2, T.Bt>, +q: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +all: T.Bt, +allx: List<&2, T.Bt>) -> List<&2, ActSd>:
  match ps xs:
    case T.BtArgs{p, rest} +x <> xt:
      List.append(&2, ActSd, act.sd.top(p, x, svars, q, bs, hps, all, allx), act.sd.tops(rest, xt, svars, q, bs, hps, all, allx))
    case _ _:
      Nil{}

def act.sd.uniq(ds: List<&2, ActSd>, +bs: List<&2, ActBind>) -> List<&2, ActSd>:
  match ds:
    case Nil{}:
      Nil{}
    case ActSd{+d, +s, +h, +vs} <> +t:
      +r = act.sd.uniq(t, bs)
      Bool.pick(List<&2, ActSd>, Nat.is_eq(act.ds.count(bs, d), 1n), ActSd{d, s, h, vs} <> r, r)

def act.sd.names(ds: List<&2, ActSd>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      Nil{}
    case ActSd{d, s, h, vs} <> t:
      d <> act.sd.names(t)

def act.sd.hn(+d: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, d, S.b("_is"))

# the position v is bound at
def act.sd.pos(bs: List<&2, ActBind>, +v: List<&2, U32>) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case ActBind{+p, T.BtVar{+x}} <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(x, v), Some{p}, act.sd.pos(t, v))
    case h <> t:
      act.sd.pos(t, v)

# v's type, the clause telescope's, in Bend
def act.sd.ty(m: Maybe<&2, Nat>, +tel: A.Ag, +n: Nat, +ctx: List<&2, T.Bt>, +env: ActEnv) -> Maybe<&2, T.Bt>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      Some{act.t(act.inline(100000n, act.tel.nth(tel, p), env), List.drop(&2, T.Bt, ctx, Nat.sub(n, p)), env)}

# v's type at a cast: the later dotted fields' s (of those v follows) still d
def act.sd.motive(later: List<&2, ActSd>, +ty: T.Bt, +v: List<&2, U32>) -> T.Bt:
  match later:
    case Nil{}:
      ty
    case ActSd{+d, +s, h, +vs} <> t:
      act.sd.motive(t, Bool.pick(T.Bt, act.used(v, vs), T.tba.subst(ty, s, T.BtVar{d}), ty), v)

# whether a cast of v (its telescope type ty) at the dotted field happens
def act.sd.cast.at(+v: List<&2, U32>, +ty: T.Bt, +vs: List<&2, List<&2, U32>>, +s: List<&2, U32>, later: List<&2, ActSd>) -> Bool:
  Bool.and(act.used(v, vs), act.occurs(s, act.sd.motive(later, ty, v)))

def act.sd.ncast(sds: List<&2, ActSd>, +v: List<&2, U32>, +ty: T.Bt) -> Nat:
  match sds:
    case Nil{}:
      0n
    case ActSd{d, +s, h, +vs} <> +t:
      Nat.add(Bool.pick(Nat, act.sd.cast.at(v, ty, vs, s, t), 1n, 0n), act.sd.ncast(t, v, ty))

def act.sd.raw(+v: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, v, S.b("_raw"))

# v's casts in order: from cur (the field as bound, v_raw) to v itself
def act.sd.casts(sds: List<&2, ActSd>, +v: List<&2, U32>, +cur: List<&2, U32>, +ty: T.Bt, +body: T.Bt) -> T.Bt:
  match sds:
    case Nil{}:
      body
    case ActSd{+d, +s, h, +vs} <> +t:
      +mty = act.sd.motive(t, ty, v)
      +out = Bool.pick(List<&2, U32>, Nat.is_eq(act.sd.ncast(t, v, ty), 0n), v, List.append(&2, U32, cur, S.b("_c")))
      Bool.pick(T.Bt, act.sd.cast.at(v, ty, vs, s, t), T.BtLet{out, act.bt.app("a2b_cast", [act.sd.nat(), T.BtDead{T.BtLam{T.BmLive{}, S.b("a2b_k"), T.tba.subst(mty, s, T.BtVar{S.b("a2b_k")})}}, T.BtDead{T.BtVar{d}}, T.BtDead{T.BtVar{s}}, T.BtVar{act.sd.hn(d)}, T.BtVar{cur}]), act.sd.casts(t, v, out, ty, body)}, act.sd.casts(t, v, cur, ty, body))

# the fields a cast retypes, with their telescope types
type ActCv is Data:
  ActCv{v: List<&2, U32>, ty: T.Bt}

def act.sd.addvs(vs: List<&2, List<&2, U32>>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match vs:
    case Nil{}:
      acc
    case +v <> t:
      act.sd.addvs(t, Bool.pick(List<&2, List<&2, U32>>, act.used(v, acc), acc, List.append(&2, List<&2, U32>, acc, [v])))

def act.sd.allvs(sds: List<&2, ActSd>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match sds:
    case Nil{}:
      acc
    case ActSd{d, s, h, vs} <> t:
      act.sd.allvs(t, act.sd.addvs(vs, acc))

def act.sd.cv(m: Maybe<&2, T.Bt>, +sds: List<&2, ActSd>, +v: List<&2, U32>) -> List<&2, ActCv>:
  match m:
    case None{}:
      Nil{}
    case Some{+ty}:
      Bool.pick(List<&2, ActCv>, Nat.is_eq(act.sd.ncast(sds, v, ty), 0n), Nil{}, [ActCv{v, ty}])

def act.sd.plan(vs: List<&2, List<&2, U32>>, +sds: List<&2, ActSd>, +tel: A.Ag, +n: Nat, +ctx: List<&2, T.Bt>, +env: ActEnv, +bs: List<&2, ActBind>) -> List<&2, ActCv>:
  match vs:
    case Nil{}:
      Nil{}
    case +v <> t:
      List.append(&2, ActCv, act.sd.cv(act.sd.ty(act.sd.pos(bs, v), tel, n, ctx, env), sds, v), act.sd.plan(t, sds, tel, n, ctx, env, bs))

def act.sd.cvs(cvs: List<&2, ActCv>, +sds: List<&2, ActSd>, body: T.Bt) -> T.Bt:
  match cvs:
    case Nil{}:
      body
    case ActCv{+v, +ty} <> t:
      act.sd.casts(sds, v, act.sd.raw(v), ty, act.sd.cvs(t, sds, body))

def act.sd.cvnames(cvs: List<&2, ActCv>) -> List<&2, List<&2, U32>>:
  match cvs:
    case Nil{}:
      Nil{}
    case ActCv{v, ty} <> t:
      v <> act.sd.cvnames(t)

# a pattern with each field a cast retypes bound as v_raw
def act.sd.prn(p: T.Bt, +on: List<&2, List<&2, U32>>) -> T.Bt:
  match p:
    case T.BtArgs{a, rest}:
      T.BtArgs{act.sd.prn(a, on), act.sd.prn(rest, on)}
    case T.BtCon{c, a}:
      T.BtCon{c, act.sd.prn(a, on)}
    case T.BtSucc{a}:
      T.BtSucc{act.sd.prn(a, on)}
    case T.BtPv{m, +nm}:
      T.BtPv{m, Bool.pick(List<&2, U32>, act.used(nm, on), act.sd.raw(nm), nm)}
    case p:
      p

def act.sd.any(vs: List<&2, List<&2, U32>>, +on: List<&2, List<&2, U32>>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case +v <> t:
      Bool.or(act.used(v, on), act.sd.any(t, on))

def act.sd.let.if(b: Bool, +d: List<&2, U32>, h: T.Bt, body: T.Bt) -> T.Bt:
  match b:
    case True{}:
      T.BtLet{act.sd.hn(d), h, body}
    case False{}:
      body

# the proofs of the dotted fields some cast uses
def act.sd.lets(sds: List<&2, ActSd>, +cvs: List<&2, List<&2, U32>>, body: T.Bt) -> T.Bt:
  match sds:
    case Nil{}:
      body
    case ActSd{+d, s, h, +vs} <> t:
      act.sd.let.if(act.sd.any(vs, cvs), d, h, act.sd.lets(t, cvs, body))

# Refl inside a top constructor pattern (`×-≡,≡→≡ (refl , refl)`, a
# setoid's sym on pairs `(refl , g)`, unimath's `(pair refl refl)`): Bend
# cannot match an equation, so the refl is a field variable x_i_rfl whose
# equation is rewritten before the body as a top-level refl's is
# (act.rws).  Its type is the field's in the parameter's type (opened, as
# uhps has it): a pair's, Σ<…, A, B>'s A for the first field and B at the
# first field for the second, with the split parameters' first and second
# projections (.fst/.pr1, .snd/.pr2) read off their patterns.  Agda dots
# the other side's variable (`p₂ = (.a , .b)`, `x = (.(fst y) , _)`):
# those fields are bound (x_i_dot, or act.pat.dot's v_dot) and are the
# dotted variables the rewrite marks.  Only when the clause has such a
# refl; its dotted fields are then left to these rewrites (no act.ds or
# act.sd).
def act.nrf.rn(+x: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  List.append(&2, U32, act.at(x, i), S.b("_rfl"))

def act.nrf.args.has(a: T.Bt, +x: List<&2, U32>, +i: Nat) -> Bool:
  match a:
    case T.BtArgs{T.BtPv{m, +nm}, rest}:
      Bool.or(S.eq(nm, act.nrf.rn(x, i)), act.nrf.args.has(rest, x, 1n+i))
    case T.BtArgs{h, rest}:
      act.nrf.args.has(rest, x, 1n+i)
    case _:
      False{}

def act.nrf.has(ps: T.Bt, xs: List<&2, T.Bt>) -> Bool:
  match ps xs:
    case T.BtArgs{T.BtCon{c, a}, rest} +x <> xt:
      Bool.or(act.nrf.args.has(a, act.var.name(x), 1n), act.nrf.has(rest, xt))
    case T.BtArgs{p, rest} x <> xt:
      act.nrf.has(rest, xt)
    case _ _:
      False{}

def act.nrf.dn(+x: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  List.append(&2, U32, act.at(x, i), S.b("_dot"))

def act.nrf.args.dots(a: T.Bt, aps: A.Ag, +x: List<&2, U32>, +i: Nat) -> T.Bt:
  match a aps:
    case T.BtArgs{T.BtWild{}, rest} A.AgPArg{ai, ax, A.AgPDot{t}, arest}:
      T.BtArgs{T.BtPv{T.BmLive{}, act.nrf.dn(x, i)}, act.nrf.args.dots(rest, arest, x, 1n+i)}
    case T.BtArgs{h, rest} A.AgPArg{ai, ax, ap, arest}:
      T.BtArgs{h, act.nrf.args.dots(rest, arest, x, 1n+i)}
    case a _:
      a

def act.nrf.dots(ps: T.Bt, aps: List<&2, A.Ag>, xs: List<&2, T.Bt>) -> T.Bt:
  match ps aps xs:
    case T.BtArgs{T.BtCon{c, a}, rest} A.AgPCon{q, r, fo, sub} <> at +x <> xt:
      T.BtArgs{T.BtCon{c, act.nrf.args.dots(a, sub, act.var.name(x), 1n)}, act.nrf.dots(rest, at, xt)}
    case T.BtArgs{p, rest} ap <> at x <> xt:
      T.BtArgs{p, act.nrf.dots(rest, at, xt)}
    case ps _ _:
      ps

def act.nrf.q(on: Bool, ps: T.Bt, aps: List<&2, A.Ag>, xs: List<&2, T.Bt>) -> T.Bt:
  match on:
    case True{}:
      act.nrf.dots(ps, aps, xs)
    case False{}:
      ps

# the split parameters' patterns (scr), in order
def act.nrf.sps(ps: A.Ag, scr: List<&2, Bool>) -> List<&2, A.Ag>:
  match ps scr:
    case A.AgPArg{i, x, p, rest} True{} <> st:
      p <> act.nrf.sps(rest, st)
    case A.AgPArg{i, x, p, rest} False{} <> st:
      act.nrf.sps(rest, st)
    case _ _:
      Nil{}

def act.nrf.beta(b: T.Bt, +v: T.Bt) -> T.Bt:
  match b:
    case T.BtLam{m, +y, body}:
      T.tba.subst(body, y, v)
    case b:
      T.BtApp{b, T.tba.args([v])}

def act.nrf.fty.at(i: Nat, a: T.Bt, b: T.Bt, +f1: T.Bt) -> T.Bt:
  match i:
    case 1n:
      a
    case 2n:
      act.nrf.beta(b, f1)
    case _:
      T.BtWild{}

# a pair's field type (the parameter's type: Σ<…, A, B>)
def act.nrf.fty(+ty: T.Bt, +i: Nat, +f1: T.Bt) -> T.Bt:
  +as = act.ty.args(ty)
  +k = List.length(&2, T.Bt, as)
  act.nrf.fty.at(i, act.ds.nth(as, Nat.sub(k, 2n)), act.ds.nth(as, Nat.sub(k, 1n)), f1)

# a constructor pattern's field j (from 0) as a term
def act.nrf.fld(j: Nat, +p: T.Bt) -> T.Bt:
  match p:
    case T.BtCon{c, a}:
      act.pat.term(act.ds.nth(act.spine.list(a), j))
    case _:
      T.BtWild{}

def act.nrf.pj(+f: List<&2, U32>) -> Nat:
  Bool.pick(Nat, Bool.or(S.suffix(f, S.b(".fst")), S.suffix(f, S.b(".pr1"))), 1n, Bool.pick(Nat, Bool.or(S.suffix(f, S.b(".snd")), S.suffix(f, S.b(".pr2"))), 2n, 0n))

def act.nrf.pat(+s: List<&2, U32>, ps: T.Bt, xs: List<&2, T.Bt>) -> T.Bt:
  match ps xs:
    case T.BtArgs{+p, rest} +x <> xt:
      Bool.pick(T.Bt, S.eq(act.var.name(x), s), p, act.nrf.pat(s, rest, xt))
    case _ _:
      T.BtWild{}

def act.nrf.last(a: T.Bt) -> T.Bt:
  match a:
    case T.BtArgs{h, T.BtANil{}}:
      h
    case T.BtArgs{h, rest}:
      act.nrf.last(rest)
    case _:
      T.BtWild{}

def act.nrf.or(t: T.Bt, +d: T.Bt) -> T.Bt:
  match t:
    case T.BtWild{}:
      d
    case t:
      t

def act.nrf.red.last(+j: Nat, l: T.Bt, +f: List<&2, U32>, +a: T.Bt, +ps: T.Bt, +xs: List<&2, T.Bt>) -> T.Bt:
  match l:
    case T.BtVar{+s}:
      act.nrf.or(act.nrf.fld(j, act.nrf.pat(s, ps, xs)), T.BtApp{T.BtVar{f}, a})
    case _:
      T.BtApp{T.BtVar{f}, a}

def act.nrf.red.app(k: Nat, +f: List<&2, U32>, +a: T.Bt, +ps: T.Bt, +xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case 0n:
      T.BtApp{T.BtVar{f}, a}
    case 1n+j:
      act.nrf.red.last(j, act.nrf.last(a), f, a, ps, xs)

# a split parameter's projections in t read off its pattern
def act.nrf.red(t: T.Bt, +ps: T.Bt, +xs: List<&2, T.Bt>) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+f}, a}:
      act.nrf.red.app(act.nrf.pj(f), f, act.nrf.red(a, ps, xs), ps, xs)
    case T.BtApp{g, a}:
      T.BtApp{act.nrf.red(g, ps, xs), act.nrf.red(a, ps, xs)}
    case T.BtArgs{a, rest}:
      T.BtArgs{act.nrf.red(a, ps, xs), act.nrf.red(rest, ps, xs)}
    case T.BtEq{ty, a, b}:
      T.BtEq{ty, act.nrf.red(a, ps, xs), act.nrf.red(b, ps, xs)}
    case T.BtSucc{a}:
      T.BtSucc{act.nrf.red(a, ps, xs)}
    case T.BtDead{a}:
      T.BtDead{act.nrf.red(a, ps, xs)}
    case t:
      t

def act.nrf.args.eqs(a: T.Bt, +all: T.Bt, +x: List<&2, U32>, +ty: T.Bt, +i: Nat, +ps: T.Bt, +xs: List<&2, T.Bt>) -> List<&2, T.BParam>:
  match a:
    case T.BtArgs{T.BtPv{m, +nm}, rest}:
      List.append(&2, T.BParam, Bool.pick(List<&2, T.BParam>, S.eq(nm, act.nrf.rn(x, i)), [T.BParam{T.BmLive{}, nm, act.nrf.red(act.nrf.fty(ty, i, act.nrf.fld(0n, all)), ps, xs)}], Nil{}), act.nrf.args.eqs(rest, all, x, ty, 1n+i, ps, xs))
    case T.BtArgs{h, rest}:
      act.nrf.args.eqs(rest, all, x, ty, 1n+i, ps, xs)
    case _:
      Nil{}

def act.nrf.eqs(ps: T.Bt, xs: List<&2, T.Bt>, +all: T.Bt, +axs: List<&2, T.Bt>, +hps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match ps xs:
    case T.BtArgs{T.BtCon{+c, +a}, rest} +x <> xt:
      List.append(&2, T.BParam, act.nrf.args.eqs(a, T.BtCon{c, a}, act.var.name(x), act.param.ty(hps, act.var.name(x)), 1n, all, axs), act.nrf.eqs(rest, xt, all, axs, hps))
    case T.BtArgs{p, rest} x <> xt:
      act.nrf.eqs(rest, xt, all, axs, hps)
    case _ _:
      Nil{}

def act.nrf.eqs.if(on: Bool, +ps: T.Bt, +xs: List<&2, T.Bt>, +hps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match on:
    case True{}:
      act.nrf.eqs(ps, xs, ps, xs, hps)
    case False{}:
      Nil{}

def act.nrf.dnames(t: T.Bt) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtArgs{a, rest}:
      List.append(&2, List<&2, U32>, act.nrf.dnames(a), act.nrf.dnames(rest))
    case T.BtCon{c, a}:
      act.nrf.dnames(a)
    case T.BtPv{m, +nm}:
      Bool.pick(List<&2, List<&2, U32>>, S.suffix(nm, S.b("_dot")), [nm], Nil{})
    case _:
      Nil{}

def act.nrf.dnames.if(on: Bool, +ps: T.Bt) -> List<&2, List<&2, U32>>:
  match on:
    case True{}:
      act.nrf.dnames(ps)
    case False{}:
      Nil{}

def act.nrf.rw(rw: ActRw, +dn: List<&2, List<&2, U32>>) -> ActRw:
  match rw:
    case ActRw{rs, ds}:
      ActRw{rs, List.append(&2, List<&2, U32>, ds, dn)}

# Constructor-shaped indices (plfa's ext: Z {.Γ} {.A} at x : (Γ , B) ∋ A,
# Agda's unification dotting B as A).  The equation field between the
# parameter's index and the constructor's, e : {Γ , B == Γd , Ad}, is
# written with the fields the clause dots (Agda made each the outer
# variable its dot names) and splits into one equation a field
# (act.inj): {Γ == Γd}, {B == Ad}; a variable index's field, {A == Ad}.
# The case binds those fields (u0393_dot, A_dot), the body reads each outer
# variable as its field (as act.ds does), and the rewrites turn the goal's
# outer variables, and the parameters' types', into the fields (the outer
# ones count as dotted).  Only for an index that is a constructor (tag
# ix_eqc:KEY/f1/../fn, act.ix.cargs) of a datatype with no parameters or
# indices, the same constructor in the parameter's type; a field dotted
# once as a parameter the clause does not split, and each such field in
# some equation; a case with no other rewrite (2026-10-29).
type ActCq is Data:
  ActCq{eqs: List<&2, T.BParam>, on: List<&2, List<&2, U32>>, binds: List<&2, ActBind>, dv: List<&2, List<&2, U32>>, con: Bool, cds: List<&2, ActCd>}

# a dotted field the case binds: its outer variable's position and name
type ActCd is Data:
  ActCd{p: Nat, nm: List<&2, U32>, s: List<&2, U32>}

# a tag's constructor key and argument places
type ActCk is Data:
  ActCk{key: String, fs: List<&2, Nat>}

def act.cq.none() -> ActCq:
  ActCq{Nil{}, Nil{}, Nil{}, Nil{}, False{}, Nil{}}

def act.cq.digits(xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      act.cq.digits(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(h, 48))))

def act.cq.nats(xs: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      act.cq.digits(h, 0n) <> act.cq.nats(t)

def act.cq.ck(parts: List<&2, List<&2, U32>>) -> Maybe<&2, ActCk>:
  match parts:
    case +h <> t:
      Bool.pick(Maybe<&2, ActCk>, S.prefix(h, S.b("ix_eqc:")), Some{ActCk{S.str(List.drop(&2, U32, h, 7n)), act.cq.nats(t)}}, None{})
    case Nil{}:
      None{}

# a field as a term: a variable the case binds (a dotted one only if on)
def act.cq.term(t: T.Bt, +bs: List<&2, ActBind>, +on: List<&2, List<&2, U32>>) -> Maybe<&2, T.Bt>:
  match t:
    case T.BtPv{m, +nm}:
      Bool.pick(Maybe<&2, T.Bt>, Bool.or(Bool.not(act.ds.is.dot(bs, nm)), act.used(nm, on)), Some{T.BtVar{nm}}, None{})
    case _:
      None{}

def act.cq.at(+fs: List<&2, T.Bt>, +f: Nat, +bs: List<&2, ActBind>, +on: List<&2, List<&2, U32>>) -> Maybe<&2, T.Bt>:
  Bool.pick(Maybe<&2, T.Bt>, Nat.is_eq(f, 0n), None{}, act.cq.term(act.ds.nth(fs, Nat.sub(f, 1n)), bs, on))

def act.cq.args2(a: Maybe<&2, T.Bt>, r: Maybe<&2, List<&2, T.Bt>>) -> Maybe<&2, List<&2, T.Bt>>:
  match a r:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

def act.cq.args(ns: List<&2, Nat>, +fs: List<&2, T.Bt>, +bs: List<&2, ActBind>, +on: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, T.Bt>>:
  match ns:
    case Nil{}:
      Some{Nil{}}
    case f <> t:
      act.cq.args2(act.cq.at(fs, f, bs, on), act.cq.args(t, fs, bs, on))

# the type of a constructor's datatype, when it has no parameters or indices
def act.cq.ty2(d: ActSym, +env: ActEnv) -> Maybe<&2, T.Bt>:
  match d:
    case ActSym{+m, +n, A.AkData{}, ms, +ar, b, fs, c, cp}:
      Bool.pick(Maybe<&2, T.Bt>, Nat.is_eq(ar, 0n), Some{T.BtTyApp{act.ref.of(act.is.here(env, m), env, m, n), T.BtANil{}}}, None{})
    case _:
      None{}

def act.cq.ty(c: ActSym, +env: ActEnv) -> Maybe<&2, T.Bt>:
  match c:
    case ActSym{m, n, A.AkConstructor{}, ms, ar, b, fs, dk, cp}:
      act.cq.ty2(act.abs.sym.key(env, S.str(dk)), env)
    case _:
      None{}

def act.cq.ceq2(idx: T.Bt, +ref: List<&2, U32>, xs: Maybe<&2, List<&2, T.Bt>>, ty: Maybe<&2, T.Bt>, +nm: List<&2, U32>) -> List<&2, T.BParam>:
  match idx xs ty:
    case T.BtCon{+c, +a} Some{+ys} Some{t}:
      +n = List.length(&2, T.Bt, ys)
      Bool.pick(List<&2, T.BParam>, Bool.and(Bool.and(S.eq(c, ref), Nat.is_eq(List.length(&2, T.Bt, act.inj.list(a)), n)), Bool.not(Nat.is_eq(n, 0n))), [T.BParam{T.BmLive{}, nm, T.BtEq{t, T.BtCon{c, a}, T.BtCon{ref, T.tba.args(ys)}}}], Nil{})
    case _ _ _:
      Nil{}

def act.cq.ceq(+key: String, ns: List<&2, Nat>, idx: T.Bt, +fs: List<&2, T.Bt>, +nm: List<&2, U32>, +bs: List<&2, ActBind>, +on: List<&2, List<&2, U32>>, +env: ActEnv) -> List<&2, T.BParam>:
  +s = act.abs.sym.key(env, key)
  act.cq.ceq2(idx, act.abs.sym.ref(s, env), act.cq.args(ns, fs, bs, on), act.cq.ty(s, env), nm)

def act.cq.veq2(idx: T.Bt, m: Maybe<&2, T.Bt>, +nm: List<&2, U32>, +hps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match idx m:
    case T.BtVar{+v} Some{+r}:
      +t = act.param.ty(hps, v)
      Bool.pick(List<&2, T.BParam>, Bool.and(act.inj.known(t), Bool.not(act.inj.same(T.BtVar{v}, r))), [T.BParam{T.BmLive{}, nm, T.BtEq{t, T.BtVar{v}, r}}], Nil{})
    case _ _:
      Nil{}

def act.cq.eq2(m: Maybe<&2, ActCk>, v: Bool, +tb: List<&2, U32>, +idx: T.Bt, +fs: List<&2, T.Bt>, +nm: List<&2, U32>, +bs: List<&2, ActBind>, +on: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match m v:
    case Some{ActCk{+key, ns}} _:
      act.cq.ceq(key, ns, idx, fs, nm, bs, on, env)
    case None{} True{}:
      act.cq.veq2(idx, act.cq.at(fs, act.cq.digits(List.drop(&2, U32, tb, 11n), 0n), bs, on), nm, hps)
    case _ _:
      Nil{}

def act.cq.eq1(+tag: String, +idx: T.Bt, +fs: List<&2, T.Bt>, +nm: List<&2, U32>, +bs: List<&2, ActBind>, +on: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  +tb = S.b(tag)
  act.cq.eq2(act.cq.ck(S.split(tb, 47)), S.prefix(tb, S.b("ix_eqv_k0_f")), tb, idx, fs, nm, bs, on, env, hps)

def act.cq.eqs(es: List<&2, ActDe>, +ixs: List<&2, T.Bt>, +fs: List<&2, T.Bt>, +xn: List<&2, U32>, +bs: List<&2, ActBind>, +on: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +svars: List<&2, T.Bt>, +q: T.Bt) -> List<&2, T.BParam>:
  match es:
    case Nil{}:
      Nil{}
    case ActDe{+j, +o, +tag} <> t:
      +idx = act.undead(act.goal(svars, q, act.ds.nth(ixs, o)))
      List.append(&2, T.BParam, act.cq.eq1(tag, idx, fs, List.append(&2, U32, act.at(xn, j), S.b("_eq")), bs, on, env, hps), act.cq.eqs(t, ixs, fs, xn, bs, on, env, hps, svars, q))

def act.cq.dot1(m: Maybe<&2, Nat>, +nm: List<&2, U32>, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +sv: List<&2, List<&2, U32>>) -> List<&2, ActCd>:
  match m:
    case None{}:
      Nil{}
    case Some{+p}:
      +s = act.var.name(act.bind.find(p, bs))
      Bool.pick(List<&2, ActCd>, Bool.and(Bool.and(Nat.is_eq(act.ds.npos(bs, Some{p}), 1n), act.ds.param(hps, s)), Bool.not(act.used(s, sv))), [ActCd{p, nm, s}], Nil{})

def act.cq.dots(fs: List<&2, T.Bt>, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +sv: List<&2, List<&2, U32>>) -> List<&2, ActCd>:
  match fs:
    case Nil{}:
      Nil{}
    case T.BtPv{m, +nm} <> t:
      List.append(&2, ActCd, act.cq.dot1(act.ds.dot(bs, nm), nm, bs, hps, sv), act.cq.dots(t, bs, hps, sv))
    case h <> t:
      act.cq.dots(t, bs, hps, sv)

def act.cq.ons(cs: List<&2, ActCd>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      Nil{}
    case ActCd{p, nm, s} <> t:
      nm <> act.cq.ons(t)

def act.cq.dvs(cs: List<&2, ActCd>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      Nil{}
    case ActCd{p, nm, s} <> t:
      s <> act.cq.dvs(t)

def act.cq.binds(cs: List<&2, ActCd>) -> List<&2, ActBind>:
  match cs:
    case Nil{}:
      Nil{}
    case ActCd{p, nm, s} <> t:
      ActBind{p, T.BtVar{nm}} <> act.cq.binds(t)

def act.cq.iscon(ty: T.Bt) -> Bool:
  match ty:
    case T.BtEq{t, T.BtCon{c, a}, T.BtCon{d, b}}:
      True{}
    case _:
      False{}

def act.cq.anycon(ps: List<&2, T.BParam>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case T.BParam{m, x, +ty} <> t:
      Bool.or(act.cq.iscon(ty), act.cq.anycon(t))

def act.cq.top(p: T.Bt, +x: T.Bt, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +sv: List<&2, List<&2, U32>>, +env: ActEnv, +svars: List<&2, T.Bt>, +q: T.Bt) -> ActCq:
  match p:
    case T.BtCon{c, +args}:
      +fs = act.spine.list(args)
      +es = act.ds.eqs(fs, 1n, 0n)
      +xn = act.var.name(x)
      +cd = act.cq.dots(fs, bs, hps, sv)
      +on = act.cq.ons(cd)
      +ixs = act.list.last(List.length(&2, ActDe, es), act.ty.args(act.param.ty(hps, xn)))
      +eqs = act.cq.eqs(es, ixs, fs, xn, bs, on, env, hps, svars, q)
      ActCq{eqs, on, act.cq.binds(cd), act.cq.dvs(cd), act.cq.anycon(eqs), cd}
    case _:
      act.cq.none()

def act.cq.cat(a: ActCq, b: ActCq) -> ActCq:
  match a b:
    case ActCq{e1, o1, b1, d1, c1, f1} ActCq{e2, o2, b2, d2, c2, f2}:
      ActCq{List.append(&2, T.BParam, e1, e2), List.append(&2, List<&2, U32>, o1, o2), List.append(&2, ActBind, b1, b2), List.append(&2, List<&2, U32>, d1, d2), Bool.or(c1, c2), List.append(&2, ActCd, f1, f2)}

def act.cq.tops(ps: T.Bt, xs: List<&2, T.Bt>, +bs: List<&2, ActBind>, +hps: List<&2, T.BParam>, +sv: List<&2, List<&2, U32>>, +env: ActEnv, +svars: List<&2, T.Bt>, +q: T.Bt) -> ActCq:
  match ps xs:
    case T.BtArgs{p, rest} +x <> xt:
      act.cq.cat(act.cq.top(p, x, bs, hps, sv, env, svars, q), act.cq.tops(rest, xt, bs, hps, sv, env, svars, q))
    case _ _:
      act.cq.none()

def act.cq.inany(+n: List<&2, U32>, ps: List<&2, T.BParam>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case T.BParam{m, x, ty} <> t:
      Bool.or(act.occurs(n, ty), act.cq.inany(n, t))

# every bound dotted field in some equation
def act.cq.cover(ns: List<&2, List<&2, U32>>, +ps: List<&2, T.BParam>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case +n <> t:
      Bool.and(act.cq.inany(n, ps), act.cq.cover(t, ps))

def act.cq.nil.ns(xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _:
      False{}

def act.cq.ok(+c: ActCq) -> Bool:
  match c:
    case ActCq{+eqs, +on, bs, dv, con, cds}:
      Bool.and(Bool.and(Bool.or(con, Bool.not(act.cq.nil.ns(on))), Bool.not(act.nil.ps(eqs))), act.cq.cover(on, eqs))

# A parameter that is a function whose type mentions an outer variable
# (plfa's rename ρ : ∀ {A} → A ∈ Γ → A ∈ Δ, used twice in app, so a
# template Bend cannot bind in a motive) is not generalized: the body reads
# it transported to the fields, {(%e : R[Γ := _]; ρ) : R[Γ := Γd]} at each
# use, e the field's equation {Γ == Γd} (a projection of a constructor
# equation, act.inj).
type ActEv is Data:
  ActEv{a: T.Bt, b: T.Bt, v: T.Bt}

type ActTr is Data:
  ActTr{t: T.Bt, ty: T.Bt}

type ActCqt is Data:
  ActCqt{x: List<&2, U32>, b: ActBind}

def act.cq.isv(t: T.Bt, +x: List<&2, U32>) -> Bool:
  match t:
    case T.BtVar{y}:
      S.eq(x, y)
    case _:
      False{}

def act.cq.ev.inj(xs: List<&2, ActInj>) -> List<&2, ActEv>:
  match xs:
    case Nil{}:
      Nil{}
    case ActInj{x, h, T.BtEq{f, a, b}, v} <> t:
      ActEv{a, b, v} <> act.cq.ev.inj(t)
    case o <> t:
      act.cq.ev.inj(t)

def act.cq.ev1(+nm: List<&2, U32>, ty: T.Bt, +hps: List<&2, T.BParam>) -> List<&2, ActEv>:
  match ty:
    case T.BtEq{+t, T.BtCon{+c, +x}, T.BtCon{+d, +y}}:
      act.cq.ev.inj(act.inj.con(T.BtCon{c, x}, T.BtCon{d, y}, t, T.BtVar{nm}, hps))
    case T.BtEq{t, a, b}:
      [ActEv{a, b, T.BtVar{nm}}]
    case _:
      Nil{}

def act.cq.evs(ps: List<&2, T.BParam>, +hps: List<&2, T.BParam>) -> List<&2, ActEv>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, +x, ty} <> t:
      List.append(&2, ActEv, act.cq.ev1(x, ty, hps), act.cq.evs(t, hps))

def act.cq.ev.find(evs: List<&2, ActEv>, +s: List<&2, U32>, +d: List<&2, U32>) -> Maybe<&2, T.Bt>:
  match evs:
    case Nil{}:
      None{}
    case ActEv{+a, +b, +v} <> t:
      Bool.pick(Maybe<&2, T.Bt>, Bool.and(act.cq.isv(a, s), act.cq.isv(b, d)), Some{v}, act.cq.ev.find(t, s, d))

def act.cq.tr1(m: Maybe<&2, T.Bt>, +s: List<&2, U32>, +d: List<&2, U32>, r: ActTr) -> ActTr:
  match m r:
    case Some{+v} ActTr{+t, +ty}:
      +ty2 = T.tba.subst(ty, s, T.BtVar{d})
      Bool.pick(ActTr, act.mentions(ty, [s]), ActTr{T.BtAnn{T.BtRw{v, T.tba.subst(ty, s, T.BtWild{}), t}, ty2}, ty2}, ActTr{t, ty})
    case None{} r:
      r

def act.cq.trs1(cds: List<&2, ActCd>, +evs: List<&2, ActEv>, r: ActTr) -> ActTr:
  match cds:
    case Nil{}:
      r
    case ActCd{p, +nm, +s} <> t:
      act.cq.trs1(t, evs, act.cq.tr1(act.cq.ev.find(evs, s, nm), s, nm, r))

def act.cq.ispi(t: T.Bt) -> Bool:
  match t:
    case T.BtPi{m, x, d, a, b}:
      True{}
    case _:
      False{}

def act.cq.pos(bs: List<&2, ActBind>, +x: List<&2, U32>) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case ActBind{+p, +t} <> r:
      Bool.pick(Maybe<&2, Nat>, act.cq.isv(t, x), Some{p}, act.cq.pos(r, x))
    case ActBDot{p, y} <> r:
      act.cq.pos(r, x)

def act.cq.tp3(m: Maybe<&2, Nat>, +x: List<&2, U32>, r: ActTr) -> List<&2, ActCqt>:
  match m r:
    case Some{p} ActTr{+t, ty}:
      Bool.pick(List<&2, ActCqt>, act.cq.isv(t, x), Nil{}, [ActCqt{x, ActBind{p, t}}])
    case _ _:
      Nil{}

def act.cq.tps(ps: List<&2, T.BParam>, +cds: List<&2, ActCd>, +evs: List<&2, ActEv>, +bs: List<&2, ActBind>, +sv: List<&2, List<&2, U32>>) -> List<&2, ActCqt>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, +x, +ty} <> t:
      +ok = Bool.and(act.cq.ispi(ty), Bool.not(act.used(x, sv)))
      List.append(&2, ActCqt, Bool.pick(List<&2, ActCqt>, ok, act.cq.tp3(act.cq.pos(bs, x), x, act.cq.trs1(cds, evs, ActTr{T.BtVar{x}, ty})), Nil{}), act.cq.tps(t, cds, evs, bs, sv))

def act.cq.ct.names(cs: List<&2, ActCqt>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      Nil{}
    case ActCqt{x, b} <> t:
      x <> act.cq.ct.names(t)

def act.cq.ct.binds(cs: List<&2, ActCqt>) -> List<&2, ActBind>:
  match cs:
    case Nil{}:
      Nil{}
    case ActCqt{x, b} <> t:
      b <> act.cq.ct.binds(t)

def act.cq.cds.of(c: ActCq) -> List<&2, ActCd>:
  match c:
    case ActCq{eqs, on, bs, dv, con, cds}:
      cds

def act.cq.nilsd(xs: List<&2, ActSd>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _:
      False{}

def act.cq.eqs.of(c: ActCq) -> List<&2, T.BParam>:
  match c:
    case ActCq{eqs, on, bs, dv, con, cds}:
      eqs

def act.cq.on.of(c: ActCq) -> List<&2, List<&2, U32>>:
  match c:
    case ActCq{eqs, on, bs, dv, con, cds}:
      on

def act.cq.binds.of(c: ActCq) -> List<&2, ActBind>:
  match c:
    case ActCq{eqs, on, bs, dv, con, cds}:
      bs

def act.cq.dv.of(c: ActCq) -> List<&2, List<&2, U32>>:
  match c:
    case ActCq{eqs, on, bs, dv, con, cds}:
      dv

# a case: its patterns, and its body after the rewrites its refl patterns
# need (an absurd or cubical clause is left out)
def act.case.of(a: ActPat, +n: Nat, body: A.Ag, +env: ActEnv, rest: T.Bt, +rw: ActRw, abs: Maybe<&2, ActAbs>, +dots: List<&2, ActDot>, +svars: List<&2, T.Bt>, +hps: List<&2, T.BParam>, +ret: T.Bt, +tel: A.Ag, +uhps: List<&2, T.BParam>, +aps: List<&2, A.Ag>) -> T.Bt:
  match a:
    case ActPat{p, +bs, True{}}:
      rest
    case ActPat{+p, +bs, False{}}:
      +q00 = act.eq.spine(p, svars)
      +nr = act.nrf.has(q00, svars)
      +q0 = act.nrf.q(nr, q00, aps, svars)
      +dn = act.nrf.dnames.if(nr, q0)
      +qw = act.ds.undot(q0, dn, bs)
      +eqs0 = List.append(&2, T.BParam, act.eq.tops(qw, svars, hps, dots, act.ctx.of(n, bs), env), act.nrf.eqs.if(nr, qw, svars, uhps))
      +sd = act.sd.uniq(Bool.pick(List<&2, ActSd>, nr, Nil{}, act.sd.tops(p, svars, svars, qw, bs, uhps, p, svars)), bs)
      +cq0 = act.cq.tops(p, svars, bs, hps, act.names(svars), env, svars, qw)
      +cqon = Bool.and(Bool.and(act.rw.none(rw), Bool.not(nr)), Bool.and(act.cq.ok(cq0), act.cq.nilsd(sd)))
      +cq = Bool.pick(ActCq, cqon, cq0, act.cq.none())
      +con = act.cq.on.of(cq)
      +g = act.goal(svars, act.ds.undot(q0, List.append(&2, List<&2, U32>, dn, con), bs), ret)
      +eqs = List.append(&2, T.BParam, eqs0, act.cq.eqs.of(cq))
      +ds = act.ds.uniq(Bool.pick(List<&2, ActDs>, Bool.and(Bool.and(act.nil.ps(eqs), act.rw.none(rw)), Bool.not(nr)), act.ds.tops(p, svars, svars, qw, bs, uhps), Nil{}), bs)
      +cts = act.cq.tps(hps, act.cq.cds.of(cq), act.cq.evs(act.cq.eqs.of(cq), hps), bs, act.names(svars))
      +ctx = act.ctx.of(n, List.append(&2, ActBind, act.ds.binds(ds, bs), List.append(&2, ActBind, act.cq.binds.of(cq), List.append(&2, ActBind, act.cq.ct.binds(cts), bs))))
      +cvs = act.sd.plan(act.sd.allvs(sd, Nil{}), sd, tel, n, ctx, env, bs)
      +cvn = act.sd.cvnames(cvs)
      T.BtCase{act.sd.prn(act.ds.undot(q0, List.append(&2, List<&2, U32>, List.append(&2, List<&2, U32>, List.append(&2, List<&2, U32>, act.ds.names(ds), act.sd.names(sd)), dn), con), bs), cvn), act.case.body(eqs, act.nrf.rw(rw, List.append(&2, List<&2, U32>, dn, act.cq.dv.of(cq))), g, act.ps.minus(hps, act.cq.ct.names(cts)), act.names(svars), act.ds.wrap(ds, g, act.sd.lets(sd, cvn, act.sd.cvs(cvs, sd, act.abs.body(abs, body, ctx, env, g))))), rest}

# the cases of a match from the clauses (an absurd clause is left out)
def act.cases(cls: A.Ag, +scr: List<&2, Bool>, +ents: List<&2, T.Bt>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, +uhps: List<&2, T.BParam>) -> T.Bt:
  match cls:
    case A.AgCl{+tel, +ps, body, ty, ca, rest}:
      +n = act.tel.len(tel)
      act.case.of(act.top.d(ps, scr, ents, n, act.tel.hints(tel), pnames, env, Nil{}, 1n), n, body, env, act.cases(rest, scr, ents, pnames, env, hps, ret, uhps), act.rw.scan(ps, ents, env), act.abs.find(ps, ents, tel, n), act.dots(ps, ents), act.scr.vars(scr, ents), hps, ret, tel, uhps, act.nrf.sps(ps, scr))
    case _:
      T.BtCEnd{}

# which of the first k parameters a clause splits (a constructor or a
# literal pattern there)
def act.split.one(p: A.Ag, +env: ActEnv) -> Bool:
  match p:
    case A.AgPCon{+q, r, fo, ps}:
      Bool.not(act.is.refl(act.sym(env, q)))
    case A.AgPLit{l}:
      True{}
    case _:
      False{}

def act.split.pos(ps: A.Ag, +env: ActEnv) -> List<&2, Bool>:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      Nil{}
    case A.AgPArg{i, x, p, rest}:
      act.split.one(p, env) <> act.split.pos(rest, env)
    case _:
      Nil{}

def act.or.lists(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case x <> xs y <> ys:
      Bool.or(x, y) <> act.or.lists(xs, ys)
    case Nil{} b:
      b
    case a Nil{}:
      a

# the parameters any clause splits
def act.scr(cls: A.Ag, +env: ActEnv) -> List<&2, Bool>:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      act.or.lists(act.split.pos(ps, env), act.scr(rest, env))
    case _:
      Nil{}

# the parameters any clause has an absurd pattern variable at
def act.abs.pos(cls: A.Ag) -> List<&2, Bool>:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      act.or.lists(act.abs.ps(ps), act.abs.pos(rest))
    case _:
      Nil{}

def act.any(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(h, act.any(t))

def act.ent.names(ents: List<&2, T.Bt>) -> List<&2, List<&2, U32>>:
  act.names(ents)

# the first case's body (the def's, when no clause splits a parameter)
def act.body.first(cs: T.Bt) -> T.Bt:
  match cs:
    case T.BtCase{p, b, rest}:
      b
    case _:
      T.BtExpr{act.todo("a function with no clause")}

# Coverage: Agda leaves out the constructors unification rules out
# (`≤-pred (s≤s p) = p`: z≤n cannot have type suc m ≤ suc n); Bend wants
# every case.  A match on one indexed parameter gets a case for each
# constructor no clause has, refuting an index equation that clashes at
# the head (act.abs.fam.c; else a gap).  The family: the data type of the
# first clause's constructor there (a constructor's entry holds its data
# type's key).
def act.cov.con(ps: A.Ag, scr: List<&2, Bool>) -> Maybe<&2, A.AgQ>:
  match ps scr:
    case A.AgPArg{i, x, A.AgPCon{q, r, fo, sub}, rest} True{} <> st:
      Some{q}
    case A.AgPArg{i, x, p, rest} True{} <> st:
      None{}
    case A.AgPArg{i, x, p, rest} False{} <> st:
      act.cov.con(rest, st)
    case _ _:
      None{}

def act.cov.q(cls: A.Ag, +scr: List<&2, Bool>) -> Maybe<&2, A.AgQ>:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      act.cov.con(ps, scr)
    case _:
      None{}

def act.cov.names(cs: T.Bt) -> List<&2, List<&2, U32>>:
  match cs:
    case T.BtCase{T.BtArgs{T.BtCon{c, a}, r}, b, rest}:
      c <> act.cov.names(rest)
    case T.BtCase{p, b, rest}:
      act.cov.names(rest)
    case _:
      Nil{}

def act.cov.append(cs: T.Bt, more: T.Bt) -> T.Bt:
  match cs:
    case T.BtCase{p, b, rest}:
      T.BtCase{p, b, act.cov.append(rest, more)}
    case _:
      more

def act.cov.ref(s: ActSym, +env: ActEnv) -> List<&2, U32>:
  match s:
    case ActSym{+m, n, k, ms, ar, b, fs, c, cp}:
      act.ref.of(act.is.here(env, m), env, m, n)

def act.cov.one(+s: ActSym, +have: List<&2, List<&2, U32>>, +ixs: List<&2, T.Bt>, +x: List<&2, U32>, +env: ActEnv, +goal: T.Bt, +rest: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, act.used(act.cov.ref(s, env), have), rest, act.abs.fam.c(s, ixs, Nil{}, x, env, goal, rest))

def act.cov.add(ks: List<&2, String>, +have: List<&2, List<&2, U32>>, +ixs: List<&2, T.Bt>, +x: List<&2, U32>, +env: ActEnv, +goal: T.Bt) -> T.Bt:
  match ks:
    case Nil{}:
      T.BtCEnd{}
    case k <> t:
      act.cov.one(act.abs.sym.key(env, k), have, ixs, x, env, goal, act.cov.add(t, have, ixs, x, env, goal))

# the data type's constructors (none unless an indexed family's: one whose
# constructors have equation fields)
def act.cov.ks(d: ActSym) -> List<&2, String>:
  match d:
    case ActSym{m, n, A.AkData{}, ms, ar, AbNone{}, cs, c, cp}:
      cs
    case _:
      Nil{}

def act.cov.dkey(s: ActSym) -> String:
  match s:
    case ActSym{m, n, A.AkConstructor{}, ms, ar, AbNone{}, fs, c, cp}:
      S.str(c)
    case _:
      ""

def act.cov.data(m: Maybe<&2, A.AgQ>, +env: ActEnv) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{q}:
      act.cov.ks(act.abs.sym.key(env, act.cov.dkey(act.sym(env, q))))

def act.cov.full(+cs: T.Bt, ks: List<&2, String>, xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> T.Bt:
  match xs:
    case x <> Nil{}:
      +have = act.cov.names(cs)
      +xn = act.var.name(x)
      act.cov.append(cs, act.cov.add(ks, have, act.ty.args(act.param.ty(hps, xn)), xn, env, ret))
    case _:
      cs

# Coverage of a match on several parameters (`lookup (x ∷ xs) zero`: no
# clause has [] since Fin zero is empty; `≤-trans (s≤s p) (s≤s q)`: none
# has s≤s then z≤n): the rows no clause covers, column by column as Bend
# checks them (a variable covers every constructor; a constructor pattern
# its constructor, its fields not looked at), each refuted by an index
# equation that clashes at the head with the family's index (act.abs), or
# by two of the row's equations on one index whose heads clash (the one
# reversed, then the other: Equal.trans, then the disc rewrite), or else
# split at a later column of a data type and each of those rows refuted
# so.  All or none: when a row has no refutation none is added (Bend's
# coverage error stays).  Only columns of variables, 0n, 1n+p and
# constructor patterns.
type ActCf is Data:
  CfNone{}
  CfNat{}
  CfData{ks: List<&2, String>}

type ActCp is Data:
  CpWild{}
  CpZero{}
  CpSuc{}
  CpCon{k: String}

type ActCt is Data:
  CtCol{fams: List<&2, ActCf>, rows: List<&2, List<&2, T.Bt>>, pre: List<&2, ActCp>}
  CtMiss{row: List<&2, ActCp>}

type ActCe is Data:
  ActCe{h: String, i: T.Bt, ev: List<&2, U32>, rhs: Maybe<&2, T.Bt>}

type ActCj is Data:
  ActCj{j: Nat, ks: List<&2, String>}

def act.cv.catch(p: T.Bt) -> Bool:
  match p:
    case T.BtPv{m, x}:
      True{}
    case T.BtWild{}:
      True{}
    case _:
      False{}

def act.cv.isnat(p: T.Bt) -> Bool:
  match p:
    case T.BtNat{s}:
      True{}
    case T.BtSucc{a}:
      True{}
    case _:
      False{}

def act.cv.iscon(p: T.Bt) -> Bool:
  match p:
    case T.BtCon{c, a}:
      True{}
    case _:
      False{}

def act.cv.simple(p: T.Bt) -> Bool:
  match p:
    case T.BtNat{+s}:
      S.eq(s, S.b("0"))
    case T.BtSucc{a}:
      True{}
    case T.BtCon{c, a}:
      True{}
    case T.BtPv{m, x}:
      True{}
    case T.BtWild{}:
      True{}
    case _:
      False{}

def act.cv.simple.row(r: List<&2, T.Bt>) -> Bool:
  match r:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(act.cv.simple(h), act.cv.simple.row(t))

def act.cv.simple.rows(rows: List<&2, List<&2, T.Bt>>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(act.cv.simple.row(r), act.cv.simple.rows(t))

def act.cv.rows(cs: T.Bt) -> List<&2, List<&2, T.Bt>>:
  match cs:
    case T.BtCase{p, b, rest}:
      act.spine.list(p) <> act.cv.rows(rest)
    case _:
      Nil{}

def act.cv.head(r: List<&2, T.Bt>) -> T.Bt:
  match r:
    case h <> t:
      h
    case Nil{}:
      T.BtWild{}

def act.cv.tail(r: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match r:
    case h <> t:
      t
    case Nil{}:
      Nil{}

def act.cv.tails(rows: List<&2, List<&2, T.Bt>>) -> List<&2, List<&2, T.Bt>>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> t:
      act.cv.tail(r) <> act.cv.tails(t)

def act.cv.allcatch(rows: List<&2, List<&2, T.Bt>>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(act.cv.catch(act.cv.head(r)), act.cv.allcatch(t))

def act.cv.nil(rows: List<&2, List<&2, T.Bt>>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case _:
      False{}

def act.cv.none(f: ActCf) -> Bool:
  match f:
    case CfNone{}:
      True{}
    case _:
      False{}

def act.cv.covers(p: T.Bt, +k: ActCp, +ref: List<&2, U32>) -> Bool:
  match p k:
    case T.BtPv{m, x} _:
      True{}
    case T.BtWild{} _:
      True{}
    case T.BtNat{s} CpZero{}:
      True{}
    case T.BtSucc{a} CpSuc{}:
      True{}
    case T.BtCon{+c, a} CpCon{kk}:
      S.eq(c, ref)
    case _ _:
      False{}

def act.cv.sel(rows: List<&2, List<&2, T.Bt>>, +k: ActCp, +ref: List<&2, U32>) -> List<&2, List<&2, T.Bt>>:
  match rows:
    case Nil{}:
      Nil{}
    case +r <> t:
      +rest = act.cv.sel(t, k, ref)
      Bool.pick(List<&2, List<&2, T.Bt>>, act.cv.covers(act.cv.head(r), k, ref), act.cv.tail(r) <> rest, rest)

def act.cv.cons(ks: List<&2, String>) -> List<&2, ActCp>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      CpCon{k} <> act.cv.cons(t)

def act.cv.ks(f: ActCf) -> List<&2, ActCp>:
  match f:
    case CfNat{}:
      [CpZero{}, CpSuc{}]
    case CfData{ks}:
      act.cv.cons(ks)
    case CfNone{}:
      Nil{}

def act.cv.ref(k: ActCp, +env: ActEnv) -> List<&2, U32>:
  match k:
    case CpCon{kk}:
      act.cov.ref(act.abs.sym.key(env, kk), env)
    case _:
      Nil{}

def act.cv.wilds(n: Nat) -> List<&2, ActCp>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      CpWild{} <> act.cv.wilds(p)

def act.cv.tasks(ks: List<&2, ActCp>, +ft: List<&2, ActCf>, +rows: List<&2, List<&2, T.Bt>>, +pre: List<&2, ActCp>, +env: ActEnv) -> List<&2, ActCt>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> t:
      +sel = act.cv.sel(rows, k, act.cv.ref(k, env))
      Bool.pick(ActCt, act.cv.nil(sel), CtMiss{List.append(&2, ActCp, List.reverse(&2, ActCp, k <> pre), act.cv.wilds(List.length(&2, ActCf, ft)))}, CtCol{ft, sel, k <> pre}) <> act.cv.tasks(t, ft, rows, pre, env)

def act.cv.step(fams: List<&2, ActCf>, +rows: List<&2, List<&2, T.Bt>>, +pre: List<&2, ActCp>, +env: ActEnv) -> List<&2, ActCt>:
  match fams:
    case Nil{}:
      Nil{}
    case +f <> +ft:
      Bool.pick(List<&2, ActCt>, Bool.or(act.cv.none(f), act.cv.allcatch(rows)), [CtCol{ft, act.cv.tails(rows), CpWild{} <> pre}], act.cv.tasks(act.cv.ks(f), ft, rows, pre, env))

# the rows no clause covers (None: the search ran out of fuel)
def act.cv.go(fuel: Nat, ts: List<&2, ActCt>, acc: List<&2, List<&2, ActCp>>, +env: ActEnv) -> Maybe<&2, List<&2, List<&2, ActCp>>>:
  match fuel ts:
    case _ Nil{}:
      Some{acc}
    case 0n _:
      None{}
    case 1n+f CtMiss{r} <> rest:
      act.cv.go(f, rest, List.append(&2, List<&2, ActCp>, acc, [r]), env)
    case 1n+f CtCol{fams, rows, pre} <> rest:
      act.cv.go(f, List.append(&2, ActCt, act.cv.step(fams, rows, pre, env), rest), acc, env)

# the families of the columns
def act.cv.qat(j: Nat, ps: A.Ag, scr: List<&2, Bool>) -> Maybe<&2, A.AgQ>:
  match j ps scr:
    case 0n A.AgPArg{i, x, A.AgPCon{q, r, fo, sub}, rest} True{} <> st:
      Some{q}
    case 0n A.AgPArg{i, x, p, rest} True{} <> st:
      None{}
    case 1n+k A.AgPArg{i, x, p, rest} True{} <> st:
      act.cv.qat(k, rest, st)
    case jj A.AgPArg{i, x, p, rest} False{} <> st:
      act.cv.qat(jj, rest, st)
    case _ _ _:
      None{}

def act.cv.qor(a: Maybe<&2, A.AgQ>, b: Maybe<&2, A.AgQ>) -> Maybe<&2, A.AgQ>:
  match a:
    case None{}:
      b
    case a:
      a

def act.cv.qcol(cls: A.Ag, +scr: List<&2, Bool>, +j: Nat) -> Maybe<&2, A.AgQ>:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      act.cv.qor(act.cv.qat(j, ps, scr), act.cv.qcol(rest, scr, j))
    case _:
      None{}

def act.cv.col(rows: List<&2, List<&2, T.Bt>>, +j: Nat) -> List<&2, T.Bt>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> t:
      act.ds.nth(r, j) <> act.cv.col(t, j)

def act.cv.anynat(ps: List<&2, T.Bt>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(act.cv.isnat(h), act.cv.anynat(t))

def act.cv.anycon(ps: List<&2, T.Bt>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(act.cv.iscon(h), act.cv.anycon(t))

def act.cv.data(ks: List<&2, String>) -> ActCf:
  match ks:
    case Nil{}:
      CfNone{}
    case ks:
      CfData{ks}

def act.cv.fam(+hs: List<&2, T.Bt>, m: Maybe<&2, A.AgQ>, +env: ActEnv) -> ActCf:
  Bool.pick(ActCf, act.cv.anynat(hs), CfNat{}, Bool.pick(ActCf, act.cv.anycon(hs), act.cv.data(act.cov.data(m, env)), CfNone{}))

def act.cv.fams(n: Nat, +j: Nat, +rows: List<&2, List<&2, T.Bt>>, +cls: A.Ag, +scr: List<&2, Bool>, +env: ActEnv) -> List<&2, ActCf>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      act.cv.fam(act.cv.col(rows, j), act.cv.qcol(cls, scr, j), env) <> act.cv.fams(p, 1n+j, rows, cls, scr, env)

# a missing row's patterns: a constructor's fields named <x>_mf_i, its
# equation fields <x>_mx_i
def act.cv.fld(+xn: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xn, S.b("_mf"))

def act.cv.eqn(+xn: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xn, S.b("_mx"))

def act.cv.fpvs(n: Nat, +x: List<&2, U32>, +i: Nat) -> List<&2, T.Bt>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      T.BtPv{T.BmLive{}, act.at(x, i)} <> act.cv.fpvs(p, x, 1n+i)

def act.cv.conpat(s: ActSym, +xn: List<&2, U32>, +env: ActEnv) -> T.Bt:
  match s:
    case ActSym{+m, +n, A.AkConstructor{}, ms, +ar, b, +fs, c, cp}:
      T.BtCon{act.ref.of(act.is.here(env, m), env, m, n), T.tba.args(List.append(&2, T.Bt, act.cv.fpvs(ar, act.cv.fld(xn), 1n), act.abs.eqpvs(fs, act.cv.eqn(xn), 1n)))}
    case _:
      T.BtWild{}

def act.cv.pat(k: ActCp, +xn: List<&2, U32>, +env: ActEnv) -> T.Bt:
  match k:
    case CpWild{}:
      T.BtWild{}
    case CpZero{}:
      T.BtNat{S.b("0")}
    case CpSuc{}:
      T.BtSucc{T.BtPv{T.BmLive{}, List.append(&2, U32, xn, S.b("_mp"))}}
    case CpCon{kk}:
      act.cv.conpat(act.abs.sym.key(env, kk), xn, env)

def act.cv.pats(row: List<&2, ActCp>, xs: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.Bt>:
  match row xs:
    case k <> rt x <> xt:
      act.cv.pat(k, act.var.name(x), env) <> act.cv.pats(rt, xt, env)
    case _ _:
      Nil{}

# an equation's right side, from its tag (ix_eqz, ix_eqt, ix_eqf;
# ix_eqs_k<k>_f<i>: suc^k of field i; ix_eqv_k0_f<i>: field i)
def act.cv.sucrhs(n: Nat, +tag: String, +fx: List<&2, U32>, +i: Nat) -> Maybe<&2, T.Bt>:
  match n:
    case 0n:
      None{}
    case 1n+p:
      +k = act.ds.k(tag, i, 4n)
      Bool.pick(Maybe<&2, T.Bt>, Nat.is_eq(k, 0n), Bool.pick(Maybe<&2, T.Bt>, String.eq(tag, "ix_eqv_k0_f" ++ Nat.show(i)), Some{T.BtVar{act.at(fx, i)}}, act.cv.sucrhs(p, tag, fx, 1n+i)), Some{act.bt.sucs(k, T.BtVar{act.at(fx, i)})})

def act.cv.rhs(+tag: String, +ar: Nat, +fx: List<&2, U32>) -> Maybe<&2, T.Bt>:
  Bool.pick(Maybe<&2, T.Bt>, String.eq(tag, "ix_eqz"), Some{T.BtNat{S.b("0")}}, Bool.pick(Maybe<&2, T.Bt>, String.eq(tag, "ix_eqt"), Some{T.BtCon{S.b("True"), T.BtANil{}}}, Bool.pick(Maybe<&2, T.Bt>, String.eq(tag, "ix_eqf"), Some{T.BtCon{S.b("False"), T.BtANil{}}}, act.cv.sucrhs(ar, tag, fx, 1n))))

def act.cv.cent(fs: List<&2, String>, +j: Nat, ixs: List<&2, T.Bt>, +xn: List<&2, U32>, +ar: Nat, +sp: T.Bt, +svars: List<&2, T.Bt>) -> List<&2, ActCe>:
  match fs ixs:
    case +tag <> ft i <> it:
      ActCe{act.tag.base(tag), act.abs.nplus(act.undead(act.goal(svars, sp, i))), act.at(act.cv.eqn(xn), j), act.cv.rhs(tag, ar, act.cv.fld(xn))} <> act.cv.cent(ft, 1n+j, it, xn, ar, sp, svars)
    case _ _:
      Nil{}

def act.cv.cents(s: ActSym, +xn: List<&2, U32>, +sp: T.Bt, +svars: List<&2, T.Bt>, +hps: List<&2, T.BParam>) -> List<&2, ActCe>:
  match s:
    case ActSym{m, n, A.AkConstructor{}, ms, +ar, b, +fs, c, cp}:
      act.cv.cent(fs, 1n, act.list.last(List.length(&2, String, fs), act.ty.args(act.param.ty(hps, xn))), xn, ar, sp, svars)
    case _:
      Nil{}

def act.cv.ents(row: List<&2, ActCp>, xs: List<&2, T.Bt>, +sp: T.Bt, +svars: List<&2, T.Bt>, +hps: List<&2, T.BParam>, +env: ActEnv) -> List<&2, ActCe>:
  match row xs:
    case CpCon{kk} <> rt x <> xt:
      List.append(&2, ActCe, act.cv.cents(act.abs.sym.key(env, kk), act.var.name(x), sp, svars, hps), act.cv.ents(rt, xt, sp, svars, hps, env))
    case k <> rt x <> xt:
      act.cv.ents(rt, xt, sp, svars, hps, env)
    case _ _:
      Nil{}

def act.cv.mor(a: Maybe<&2, T.Bt>, b: Maybe<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match a:
    case None{}:
      b
    case a:
      a

def act.cv.single(es: List<&2, ActCe>, +goal: T.Bt) -> Maybe<&2, T.Bt>:
  match es:
    case Nil{}:
      None{}
    case ActCe{+h, +i, +ev, r} <> t:
      Bool.pick(Maybe<&2, T.Bt>, act.abs.clashes(h, i), Some{act.abs.refute(act.abs.disc(act.abs.tagty(h), i), ev, goal)}, act.cv.single(t, goal))

def act.cv.hclash(+a: String, +b: String) -> Bool:
  Bool.or(Bool.or(Bool.and(String.eq(a, "ix_eqz"), String.eq(b, "ix_eqs")), Bool.and(String.eq(a, "ix_eqs"), String.eq(b, "ix_eqz"))), Bool.or(Bool.and(String.eq(a, "ix_eqt"), String.eq(b, "ix_eqf")), Bool.and(String.eq(a, "ix_eqf"), String.eq(b, "ix_eqt"))))

def act.cv.pairmk(r: Maybe<&2, T.Bt>, r2: Maybe<&2, T.Bt>, +h: String, +i: T.Bt, +ev: List<&2, U32>, +ev2: List<&2, U32>, +goal: T.Bt) -> Maybe<&2, T.Bt>:
  match r r2:
    case Some{+a} Some{b}:
      +e = List.append(&2, U32, ev, S.b("_cl"))
      +ty = act.abs.tagty(h)
      Some{T.BtLet{e, act.bt.app("Equal.trans", [T.BtDead{T.BtVar{ty}}, T.BtDead{a}, T.BtDead{i}, T.BtDead{b}, act.bt.app("Equal.sym", [T.BtDead{T.BtVar{ty}}, T.BtDead{i}, T.BtDead{a}, T.BtVar{ev}]), T.BtVar{ev2}]), act.abs.refute(act.abs.disc(ty, a), e, goal)}}
    case _ _:
      None{}

def act.cv.pairb(+h: String, +i: T.Bt, +ev: List<&2, U32>, +r: Maybe<&2, T.Bt>, bs: List<&2, ActCe>, +goal: T.Bt) -> Maybe<&2, T.Bt>:
  match bs:
    case Nil{}:
      None{}
    case ActCe{+h2, +i2, +ev2, +r2} <> t:
      act.cv.mor(Bool.pick(Maybe<&2, T.Bt>, Bool.and(act.cv.hclash(h, h2), act.sd.same(i, i2)), act.cv.pairmk(r, r2, h, i, ev, ev2, goal), None{}), act.cv.pairb(h, i, ev, r, t, goal))

def act.cv.pair1(a: ActCe, +bs: List<&2, ActCe>, +goal: T.Bt) -> Maybe<&2, T.Bt>:
  match a:
    case ActCe{+h, +i, +ev, +r}:
      act.cv.pairb(h, i, ev, r, bs, goal)

def act.cv.pair(es: List<&2, ActCe>, +all: List<&2, ActCe>, +goal: T.Bt) -> Maybe<&2, T.Bt>:
  match es:
    case Nil{}:
      None{}
    case a <> t:
      act.cv.mor(act.cv.pair1(a, all, goal), act.cv.pair(t, all, goal))

def act.cv.case(+sp: T.Bt, m: Maybe<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Some{T.BtCase{sp, b, T.BtCEnd{}}}

def act.cv.refute(+row: List<&2, ActCp>, +xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> Maybe<&2, T.Bt>:
  +sp = T.tba.args(act.cv.pats(row, xs, env))
  +goal = act.goal(xs, sp, ret)
  +es = act.cv.ents(row, xs, sp, xs, hps, env)
  act.cv.case(sp, act.cv.mor(act.cv.single(es, goal), act.cv.pair(es, es, goal)))

def act.cv.chain(a: Maybe<&2, T.Bt>, b: Maybe<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match a b:
    case Some{x} Some{y}:
      Some{act.cov.append(x, y)}
    case _ _:
      None{}

def act.cv.all(rows: List<&2, List<&2, ActCp>>, +xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> Maybe<&2, T.Bt>:
  match rows:
    case Nil{}:
      Some{T.BtCEnd{}}
    case r <> t:
      act.cv.chain(act.cv.refute(r, xs, env, hps, ret), act.cv.all(t, xs, env, hps, ret))

def act.cv.setat(row: List<&2, ActCp>, j: Nat, +k: ActCp) -> List<&2, ActCp>:
  match row j:
    case h <> t 0n:
      k <> t
    case h <> t 1n+p:
      h <> act.cv.setat(t, p, k)
    case r _:
      r

def act.cv.splits(ks: List<&2, String>, +row: List<&2, ActCp>, +j: Nat) -> List<&2, List<&2, ActCp>>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      act.cv.setat(row, j, CpCon{k}) <> act.cv.splits(t, row, j)

def act.cv.iswild(k: ActCp) -> Bool:
  match k:
    case CpWild{}:
      True{}
    case _:
      False{}

def act.cv.wildat(row: List<&2, ActCp>, fams: List<&2, ActCf>, +j: Nat) -> Maybe<&2, ActCj>:
  match row fams:
    case k <> rt CfData{+ks} <> ft:
      Bool.pick(Maybe<&2, ActCj>, act.cv.iswild(k), Some{ActCj{j, ks}}, act.cv.wildat(rt, ft, 1n+j))
    case k <> rt f <> ft:
      act.cv.wildat(rt, ft, 1n+j)
    case _ _:
      None{}

def act.cv.split(m: Maybe<&2, ActCj>, +row: List<&2, ActCp>, +xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> Maybe<&2, T.Bt>:
  match m:
    case None{}:
      None{}
    case Some{ActCj{j, ks}}:
      act.cv.all(act.cv.splits(ks, row, j), xs, env, hps, ret)

def act.cv.one(+row: List<&2, ActCp>, +fams: List<&2, ActCf>, +xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> Maybe<&2, T.Bt>:
  act.cv.mor(act.cv.refute(row, xs, env, hps, ret), act.cv.split(act.cv.wildat(row, fams, 0n), row, xs, env, hps, ret))

def act.cv.close(rows: List<&2, List<&2, ActCp>>, +fams: List<&2, ActCf>, +xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> Maybe<&2, T.Bt>:
  match rows:
    case Nil{}:
      Some{T.BtCEnd{}}
    case r <> t:
      act.cv.chain(act.cv.one(r, fams, xs, env, hps, ret), act.cv.close(t, fams, xs, env, hps, ret))

def act.cv.fin2(m: Maybe<&2, T.Bt>, +cs: T.Bt) -> T.Bt:
  match m:
    case None{}:
      cs
    case Some{more}:
      act.cov.append(cs, more)

def act.cv.fin(m: Maybe<&2, List<&2, List<&2, ActCp>>>, +cs: T.Bt, +fams: List<&2, ActCf>, +xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> T.Bt:
  match m:
    case None{}:
      cs
    case Some{rows}:
      act.cv.fin2(act.cv.close(rows, fams, xs, env, hps, ret), cs)

def act.cv.full(+cs: T.Bt, +cls: A.Ag, +scr: List<&2, Bool>, +xs: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> T.Bt:
  +rows = act.cv.rows(cs)
  +n = List.length(&2, T.Bt, xs)
  +fams = act.cv.fams(n, 0n, rows, cls, scr, env)
  Bool.pick(T.Bt, Bool.and(Nat.is_lt(1n, n), act.cv.simple.rows(rows)), act.cv.fin(act.cv.go(4096n, [CtCol{fams, rows, Nil{}}], Nil{}, env), cs, fams, xs, env, hps, ret), cs)

def act.ps.ps(r: ActPs) -> List<&2, T.BParam>:
  match r:
    case ActPs{ps, ret, ctx, es, ok}:
      ps

def act.ps.ret(r: ActPs) -> T.Bt:
  match r:
    case ActPs{ps, ret, ctx, es, ok}:
      ret

# A constructor's own arguments as fields (a Level one is dropped), each
# type in the scope of the data type's parameters and the earlier fields.
def act.cfield.put(lv: Bool, +nm: List<&2, U32>, ty: T.Bt, fs: List<&2, T.BField>) -> List<&2, T.BField>:
  match lv:
    case True{}:
      fs
    case False{}:
      T.BField{nm, ty} <> fs

# an indexed family's constructor's equation fields: per index parameter
# (its name and type) and the index the constructor's type ends at, {i == t : T}
def act.ix.eqs(ixs: List<&2, T.BParam>, es: A.Ag, +ctx: List<&2, T.Bt>, +seen: List<&2, List<&2, U32>>, +env: ActEnv) -> List<&2, T.BField>:
  match ixs es:
    case T.BParam{m, +x, ty} <> pt A.AgEApp{i, a, rest}:
      +nm = act.fresh.in(S.b("ix_eq"), ctx, seen)
      T.BField{nm, T.BtEq{ty, T.BtVar{x}, act.t(a, ctx, env)}} <> act.ix.eqs(pt, rest, ctx, nm <> seen, env)
    case _ _:
      Nil{}

def act.ix.fields(ixs: List<&2, T.BParam>, +pars: Nat, t: A.Ag, +ctx: List<&2, T.Bt>, +seen: List<&2, List<&2, U32>>, +env: ActEnv) -> List<&2, T.BField>:
  match t:
    case A.AgEl{s, A.AgDef{q, es}}:
      act.ix.eqs(ixs, act.es.after(pars, es), ctx, seen, env)
    case _:
      Nil{}

# (the index parameters' names are in seen, so no field hides one)
def act.cfields(t: A.Ag, +ctx: List<&2, T.Bt>, +seen: List<&2, List<&2, U32>>, +env: ActEnv, +ixs: List<&2, T.BParam>, +pars: Nat) -> List<&2, T.BField>:
  match t:
    case A.AgEl{s, A.AgPi{i, +x, +a, d, b}}:
      +lv = act.ty.level(a)
      +nm = act.fresh.in(x, ctx, seen)
      act.cfield.put(lv, nm, act.t(a, ctx, env), act.cfields(b, act.bind(d, Bool.pick(T.Bt, lv, act.level(), T.BtVar{nm}), ctx), nm <> seen, env, ixs, pars))
    case t:
      act.ix.fields(ixs, pars, t, ctx, seen, env)

# a TYPE after its first n Pis
def act.after(n: Nat, t: A.Ag) -> A.Ag:
  match n t:
    case 1n+p A.AgEl{s, A.AgPi{i, x, a, d, b}}:
      act.after(p, b)
    case _ t:
      t

def act.ps.ctx(r: ActPs) -> List<&2, T.Bt>:
  match r:
    case ActPs{ps, ret, ctx, es, ok}:
      ctx

def act.ps.names(ps: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      x <> act.ps.names(t)

def act.ctor.of(s: ActSym, +pars: Nat, +t: A.Ag, +env: ActEnv, +ixs: List<&2, T.BParam>) -> T.BCtor:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, cp}:
      T.BCtor{n, act.cfields(act.after(pars, t), act.ps.ctx(act.params(64n, pars, t, act.modes(t, True{}), Nil{}, env)), act.ps.names(ixs), env, ixs, pars)}

def act.ps.take(n: Nat, ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match n ps:
    case 1n+p h <> t:
      h <> act.ps.take(p, t)
    case _ ps:
      Nil{}

# the last n of a list of parameters (an indexed family's indices)
def act.ps.last(+n: Nat, ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  List.reverse(&2, T.BParam, act.ps.take(n, List.reverse(&2, T.BParam, ps)))

# Nested patterns (act.nu) -----------------------------------------------------

# A clause with a constructor pattern of an indexed family inside another
# constructor pattern (`<⇒<ᵇ (s≤s (s≤s m<n))`, `≤-pred₂ (s≤s (s≤s p))`,
# `¬2≤1 (s≤s ())`) needs the index equations of every level, not only the
# top one's.  A def any clause of which has one takes this path whole:
# each constructor pattern binds all its fields (a dotted one as a
# variable) and its equation fields; the equations are solved as Agda's
# unification solves them (suc's injectivity, a zero/suc or true/false
# clash, a variable Agda dotted given its value), each solution with an
# Equal proof; the case then rewrites the goal and casts (a2b_cast) the
# pattern variables to the values Agda's clause has, and the body reads
# Agda's variables as the binders Agda kept.  The combinations of nested
# patterns the clauses leave out (an absurd clause, or one Agda's coverage
# saw impossible) are found by Maranget's algorithm and refuted from the
# same equations, splitting a wildcard of an indexed family when no
# equation clashes yet.  A def with a pattern this path does not know
# (refl, a copattern, a literal other than a Nat) takes the other path.

# A pattern: an Agda variable (its telescope position, absurd or not), a
# dotted one (the telescope position it is exactly, when one) or a
# wildcard, a constructor (by key; "$z" "$s" "$t" "$f" "$u": zero, suc,
# true, false, tt) with its arguments as a spine (NuPS ... NuPE), a
# cubical clause's (NuPR: the clause is left out), or one this path does
# not write (NuPX).
type NuP is Data:
  NuPV{pos: Nat, abs: Bool}
  NuPD{pos: Maybe<&2, Nat>}
  NuPC{k: String, ps: NuP}
  NuPS{p: NuP, rest: NuP}
  NuPE{}
  NuPR{}
  NuPX{}

type NuK is Data:
  NkReal{}
  NkZ{}
  NkS{}
  NkT{}
  NkF{}
  NkU{}

# a constructor pattern's field: its placeholder name (the field types
# after it name it so), its type, and its type's data key ("$nat",
# "$bool", "$unit", a data type's key, or "" when none)
type NuF is Data:
  NuF{x: List<&2, U32>, ty: T.Bt, hk: String}

# a constructor at a pattern of a given type: whether it could be read,
# its kind, its Bend name, its fields (the equation fields last)
type NuCi is Data:
  NuCi{ok: Bool, k: NuK, ref: List<&2, U32>, fs: List<&2, NuF>}

# an equation {a == b : ty} and its proof
type NuEq is Data:
  NuEq{ty: T.Bt, a: T.Bt, b: T.Bt, pf: T.Bt}

# a binder of an Agda variable, its telescope position and Bend type
type NuVt is Data:
  NuVt{pos: Nat, x: List<&2, U32>, ty: T.Bt}

# a flexible variable that is exactly the Agda variable at pos (a dotted
# field `.(m)`, or an erased parameter's variable pattern), its type, and
# whether it is live
type NuDot is Data:
  NuDot{x: List<&2, U32>, pos: Nat, ty: T.Bt, live: Bool}

# a wildcard (a dotted field), its path (innermost first) and its type's data key
type NuHole is Data:
  NuHole{path: List<&2, Nat>, dk: String}

type NuSg is Data:
  NuSg{x: List<&2, U32>, t: T.Bt}

# A row's walk: whether it could be written, the bindings of Agda's
# variables, the flexible variables, the equations, the binders' types,
# the dotted fields, the erased parameters' variables, the wildcards, the
# substitution (placeholders and split parameters to their terms), and
# the stacks of patterns and terms built.
type NuSt is Data:
  NuSt{ok: Bool, bs: List<&2, ActBind>, fl: List<&2, List<&2, U32>>, eqs: List<&2, NuEq>, vts: List<&2, NuVt>, dots: List<&2, NuDot>, weak: List<&2, NuDot>, holes: List<&2, NuHole>, sg: List<&2, NuSg>, ps: List<&2, T.Bt>, ts: List<&2, T.Bt>, vty: List<&2, NuSg>}

type NuTk is Data:
  NuTk{xs: List<&2, T.Bt>, rest: List<&2, T.Bt>}

# x := t, and its proof pf : {x == t : ty}
type NuSol is Data:
  NuSol{x: List<&2, U32>, ty: T.Bt, t: T.Bt, pf: T.Bt}

# the solutions, and the clashes found
type NuU is Data:
  NuU{sols: List<&2, NuSol>, cl: List<&2, NuEq>}

# a term and a proof of {t0 == t} for the term t0 it was made from (None: t is t0)
type NuPf is Data:
  NuPf{t: T.Bt, pf: Maybe<&2, T.Bt>}

type NuC is Data:
  NcSame{}
  NcInj{}
  NcSuc{}
  NcClash{}
  NcVarL{}
  NcVarR{}
  NcStuck{}

type NuStm is Data:
  NsLet{x: List<&2, U32>, v: T.Bt}
  NsRw{e: T.Bt, p: T.Bt}

type NuCs is Data:
  NuCs{ss: List<&2, NuStm>, x: List<&2, U32>, ty: T.Bt}

type NuBd is Data:
  NuBd{ss: List<&2, NuStm>, bs: List<&2, ActBind>}

type NuGl is Data:
  NuGl{ss: List<&2, NuStm>, g: T.Bt}

type NuCase is Data:
  NuCase{p: T.Bt, b: T.Bt}

type NuAcc is Data:
  NuAcc{ok: Bool, cs: List<&2, NuCase>, rows: List<&2, NuP>}

type NuWr is Data:
  NwWild{}
  NwCon{k: String, ar: Nat}

type NuMj is Data:
  NuMj{rows: List<&2, NuP>, w: Nat, cx: List<&2, NuWr>}

type NuRj is Data:
  NuRj{row: NuP, d: Nat}

type NuCx is Data:
  NuCx{scr: List<&2, Bool>, ents: List<&2, T.Bt>, ks: List<&2, String>, hps: List<&2, T.BParam>, pnames: List<&2, List<&2, U32>>, env: ActEnv, ret: T.Bt}

# Patterns ---------------------------------------------------------------------

def act.nu.lit(k: Nat) -> NuP:
  match k:
    case 0n:
      NuPC{"$z", NuPE{}}
    case 1n+p:
      NuPC{"$s", NuPS{act.nu.lit(p), NuPE{}}}

def act.nu.litp.of(small: Bool, k: Nat) -> NuP:
  match small:
    case True{}:
      act.nu.lit(k)
    case False{}:
      NuPX{}

def act.nu.litp(+k: Nat) -> NuP:
  act.nu.litp.of(Nat.is_lt(k, 65n), k)

def act.nu.dot(t: A.Ag, +n: Nat) -> NuP:
  match t:
    case A.AgVar{ix, x, A.AgENil{}}:
      NuPD{Some{Nat.sub(Nat.sub(n, 1n), ix)}}
    case _:
      NuPD{None{}}

def act.nu.con(s: ActSym, k: String, sub: NuP) -> NuP:
  match s:
    case ActSym{m, nm, kd, ms, ar, AbZero{}, fs, c, cp}:
      NuPC{"$z", NuPE{}}
    case ActSym{m, nm, kd, ms, ar, AbSuc{}, fs, c, cp}:
      NuPC{"$s", sub}
    case ActSym{m, nm, kd, ms, ar, AbTrue{}, fs, c, cp}:
      NuPC{"$t", NuPE{}}
    case ActSym{m, nm, kd, ms, ar, AbFalse{}, fs, c, cp}:
      NuPC{"$f", NuPE{}}
    case ActSym{m, nm, kd, ms, ar, AbTt{}, fs, c, cp}:
      NuPC{"$u", NuPE{}}
    case ActSym{m, nm, A.AkConstructor{}, ms, ar, AbNone{}, fs, c, cp}:
      NuPC{k, sub}
    case _:
      NuPX{}

def act.nu.p(a: A.Ag, +n: Nat, +env: ActEnv) -> NuP:
  match a:
    case A.AgPArg{i, x, q, rest}:
      NuPS{act.nu.p(q, n, env), act.nu.p(rest, n, env)}
    case A.AgPEnd{}:
      NuPE{}
    case A.AgPVar{x, ix, o}:
      NuPV{Nat.sub(Nat.sub(n, 1n), ix), A.aas.kw.eq(o, A.AkAbsurd{})}
    case A.AgPDot{t}:
      act.nu.dot(t, n)
    case A.AgPCon{+q, r, fo, ps}:
      act.nu.con(act.sym(env, q), act.key(q), act.nu.p(ps, n, env))
    case A.AgPLit{A.AgLNat{s}}:
      act.nu.litp(act.cq.digits(s, 0n))
    case A.AgRaw{c, x}:
      NuPR{}
    case _:
      NuPX{}

def act.nu.raw(p: NuP) -> Bool:
  match p:
    case NuPR{}:
      True{}
    case NuPC{k, ps}:
      act.nu.raw(ps)
    case NuPS{h, t}:
      Bool.or(act.nu.raw(h), act.nu.raw(t))
    case _:
      False{}

def act.nu.bad(p: NuP) -> Bool:
  match p:
    case NuPX{}:
      True{}
    case NuPC{k, ps}:
      act.nu.bad(ps)
    case NuPS{h, t}:
      Bool.or(act.nu.bad(h), act.nu.bad(t))
    case _:
      False{}

def act.nu.absp(p: NuP) -> Bool:
  match p:
    case NuPV{pos, ab}:
      ab
    case NuPC{k, ps}:
      act.nu.absp(ps)
    case NuPS{h, t}:
      Bool.or(act.nu.absp(h), act.nu.absp(t))
    case _:
      False{}

def act.nu.kind(+k: String) -> NuK:
  Bool.pick(NuK, String.eq(k, "$z"), NkZ{}, Bool.pick(NuK, String.eq(k, "$s"), NkS{}, Bool.pick(NuK, String.eq(k, "$t"), NkT{}, Bool.pick(NuK, String.eq(k, "$f"), NkF{}, Bool.pick(NuK, String.eq(k, "$u"), NkU{}, NkReal{})))))

def act.nu.real(+k: String) -> Bool:
  Bool.not(S.prefix(S.b(k), S.b("$")))

# the entry of a key in the symbol table
def act.nu.symk(+env: ActEnv, k: String) -> ActSym:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.sym.got(Map.get(ActSym, act.sym0(), tab, k))

def act.nu.tag.ix(fs: List<&2, String>) -> Bool:
  match fs:
    case h <> t:
      S.prefix(S.b(h), S.b("ix_eq"))
    case Nil{}:
      False{}

def act.nu.ixd.of(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, A.AkConstructor{}, ms, ar, AbNone{}, fs, c, cp}:
      act.nu.tag.ix(fs)
    case _:
      False{}

# an indexed family's constructor (it has equation fields)
def act.nu.ixd(+env: ActEnv, k: String) -> Bool:
  act.nu.ixd.of(act.nu.symk(env, k))

# an indexed family's constructor pattern, or an absurd one, inside a constructor pattern
def act.nu.deep(p: NuP, +under: Bool, +env: ActEnv) -> Bool:
  match p:
    case NuPC{+k, ps}:
      Bool.or(Bool.and(under, act.nu.ixd(env, k)), act.nu.deep(ps, Bool.or(under, act.nu.real(k)), env))
    case NuPS{h, t}:
      Bool.or(act.nu.deep(h, under, env), act.nu.deep(t, under, env))
    case NuPV{pos, ab}:
      Bool.and(under, ab)
    case _:
      False{}

def act.nu.want(cls: A.Ag, +env: ActEnv) -> Bool:
  match cls:
    case A.AgCl{+tel, ps, body, ty, ca, rest}:
      Bool.or(act.nu.deep(act.nu.p(ps, act.tel.len(tel), env), False{}, env), act.nu.want(rest, env))
    case _:
      False{}

def act.nu.anybad(cls: A.Ag, +env: ActEnv) -> Bool:
  match cls:
    case A.AgCl{+tel, ps, body, ty, ca, rest}:
      Bool.or(act.nu.bad(act.nu.p(ps, act.tel.len(tel), env)), act.nu.anybad(rest, env))
    case _:
      False{}

# Constructors -----------------------------------------------------------------

# A constructor's type (with its data type's parameter count) and its data
# type's name, in the unfoldings by the constructor's key (Agda2Bend.bend
# a2b.syms.one), so another module's patterns read them.
def act.nu.cty.key(k: String) -> String:
  "cty:" ++ k

def act.nu.cdq.key(k: String) -> String:
  "cdq:" ++ k

def act.nu.cty.of(d: A.AgDecl) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDCon{dq, pars, ar, ck, src}}:
      Some{ActCopy{pars, ty}}
    case _:
      None{}

def act.nu.cdq.of(d: A.AgDecl) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDCon{dq, pars, ar, ck, src}}:
      Some{ActCopy{0n, A.AgDef{dq, A.AgENil{}}}}
    case _:
      None{}

def act.nu.unf(+env: ActEnv, k: String) -> ActCopy:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, k))

def act.nu.dkey.of(c: ActCopy) -> String:
  match c:
    case ActCopy{n, A.AgDef{q, es}}:
      act.key(q)
    case _:
      ""

def act.nu.dkey.k(c: NuK, +env: ActEnv, k: String) -> String:
  match c:
    case NkReal{}:
      act.nu.dkey.of(act.nu.unf(env, act.nu.cdq.key(k)))
    case NkZ{}:
      "$nat"
    case NkS{}:
      "$nat"
    case NkT{}:
      "$bool"
    case NkF{}:
      "$bool"
    case NkU{}:
      "$unit"

# the data key of a constructor key
def act.nu.dkey(+env: ActEnv, +k: String) -> String:
  act.nu.dkey.k(act.nu.kind(k), env, k)

def act.nu.sym.fields(s: ActSym) -> List<&2, String>:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, cp}:
      fs

# a data key's constructors
def act.nu.sibs(+env: ActEnv, +dk: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(dk, "$nat"), ["$z", "$s"], Bool.pick(List<&2, String>, String.eq(dk, "$bool"), ["$t", "$f"], Bool.pick(List<&2, String>, String.eq(dk, "$unit"), ["$u"], Bool.pick(List<&2, String>, String.eq(dk, ""), Nil{}, act.nu.sym.fields(act.nu.symk(env, dk))))))

def act.nu.npis(t: A.Ag) -> Nat:
  match t:
    case A.AgEl{s, A.AgPi{i, x, a, d, b}}:
      1n+act.nu.npis(b)
    case _:
      0n

def act.nu.ar.of(c: ActCopy) -> Nat:
  match c:
    case ActCopy{pars, ty}:
      act.nu.npis(act.after(pars, ty))

def act.nu.arity.k(c: NuK, +env: ActEnv, k: String) -> Nat:
  match c:
    case NkS{}:
      1n
    case NkReal{}:
      act.nu.ar.of(act.nu.unf(env, act.nu.cty.key(k)))
    case _:
      0n

# a constructor's argument count (its patterns' spine length)
def act.nu.arity(+env: ActEnv, +k: String) -> Nat:
  act.nu.arity.k(act.nu.kind(k), env, k)

def act.nu.spine(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      h <> act.nu.spine(t)
    case _:
      Nil{}

def act.nu.fnames(fs: List<&2, T.BField>) -> List<&2, List<&2, U32>>:
  match fs:
    case T.BField{x, ty} <> t:
      x <> act.nu.fnames(t)
    case Nil{}:
      Nil{}

def act.nu.tmps(xs: List<&2, List<&2, U32>>, +b: String, +i: Nat) -> List<&2, List<&2, U32>>:
  match xs:
    case x <> t:
      S.b(b ++ Nat.show(i)) <> act.nu.tmps(t, b, 1n+i)
    case Nil{}:
      Nil{}

def act.nu.phs(xs: List<&2, List<&2, U32>>, +pre: List<&2, U32>, +i: Nat) -> List<&2, List<&2, U32>>:
  match xs:
    case x <> t:
      List.append(&2, U32, pre, S.b("_" ++ Nat.show(i))) <> act.nu.phs(t, pre, 1n+i)
    case Nil{}:
      Nil{}

def act.nu.vars(xs: List<&2, List<&2, U32>>) -> List<&2, T.Bt>:
  match xs:
    case x <> t:
      T.BtVar{x} <> act.nu.vars(t)
    case Nil{}:
      Nil{}

# t with each x replaced by its v, one after another
def act.nu.ren(xs: List<&2, List<&2, U32>>, vs: List<&2, T.Bt>, t: T.Bt) -> T.Bt:
  match xs vs:
    case x <> xt v <> vt:
      act.nu.ren(xt, vt, T.tba.subst(t, x, v))
    case _ _:
      t

def act.nu.head.b(b: ActB, k: String) -> String:
  match b:
    case AbNat{}:
      "$nat"
    case AbBool{}:
      "$bool"
    case AbUnit{}:
      "$unit"
    case _:
      k

def act.nu.head.of(a: A.Ag) -> String:
  match a:
    case A.AgEl{s, A.AgDef{+q, es}}:
      act.nu.head.b(act.builtin(act.qs(q)), act.key(q))
    case _:
      ""

def act.nu.heads.put(lv: Bool, h: String, t: List<&2, String>) -> List<&2, String>:
  match lv:
    case True{}:
      t
    case False{}:
      h <> t

# a constructor's own arguments' data keys (a Level one is dropped, as a field)
def act.nu.heads(t: A.Ag) -> List<&2, String>:
  match t:
    case A.AgEl{s, A.AgPi{i, x, +a, d, b}}:
      act.nu.heads.put(act.ty.level(a), act.nu.head.of(a), act.nu.heads(b))
    case _:
      Nil{}

def act.nu.hd.or(hs: List<&2, String>) -> String:
  match hs:
    case h <> t:
      h
    case Nil{}:
      ""

def act.nu.tl.or(hs: List<&2, String>) -> List<&2, String>:
  match hs:
    case h <> t:
      t
    case Nil{}:
      Nil{}

# the fields, their types with the data type's parameters (ps, the
# scrutinee's type's arguments as) and the fields (fns, the placeholders
# all) put in, through fresh names first (t1, t2) so none is caught
def act.nu.fs.inst(fs: List<&2, T.BField>, +ps: List<&2, List<&2, U32>>, +t1: List<&2, List<&2, U32>>, +fns: List<&2, List<&2, U32>>, +t2: List<&2, List<&2, U32>>, +as: List<&2, T.Bt>, phs: List<&2, List<&2, U32>>, +all: List<&2, List<&2, U32>>, +hs: List<&2, String>) -> List<&2, NuF>:
  match fs phs:
    case T.BField{x, ty} <> ft ph <> pt:
      NuF{ph, act.nu.ren(t2, act.nu.vars(all), act.nu.ren(t1, as, act.nu.ren(fns, act.nu.vars(t2), act.nu.ren(ps, act.nu.vars(t1), ty)))), act.nu.hd.or(hs)} <> act.nu.fs.inst(ft, ps, t1, fns, t2, as, pt, all, act.nu.tl.or(hs))
    case _ _:
      Nil{}

def act.nu.ci.mk3(+ok: Bool, ref: List<&2, U32>, +ps: List<&2, List<&2, U32>>, fs: List<&2, T.BField>, +fns: List<&2, List<&2, U32>>, +as: List<&2, T.Bt>, +pre: List<&2, U32>, hs: List<&2, String>) -> NuCi:
  +phs = act.nu.phs(fns, pre, 1n)
  NuCi{Bool.and(ok, Nat.is_eq(List.length(&2, List<&2, U32>, ps), List.length(&2, T.Bt, as))), NkReal{}, ref, act.nu.fs.inst(fs, ps, act.nu.tmps(ps, "a2b_nut_p", 0n), fns, act.nu.tmps(fns, "a2b_nut_f", 0n), as, phs, phs, hs)}

def act.nu.ci.mk(bc: T.BCtor, ps: List<&2, List<&2, U32>>, ty: T.Bt, ref: List<&2, U32>, hs: List<&2, String>, pre: List<&2, U32>, ok: Bool) -> NuCi:
  match bc ty:
    case T.BCtor{c, +fs} T.BtTyApp{tn, args}:
      act.nu.ci.mk3(ok, ref, ps, fs, act.nu.fnames(fs), act.nu.spine(args), pre, hs)
    case T.BCtor{c, +fs} T.BtVar{tn}:
      act.nu.ci.mk3(ok, ref, ps, fs, act.nu.fnames(fs), Nil{}, pre, hs)
    case _ _:
      NuCi{False{}, NkReal{}, ref, Nil{}}

def act.nu.cbody(c: ActCopy) -> A.Ag:
  match c:
    case ActCopy{n, b}:
      b

def act.nu.isty(t: A.Ag) -> Bool:
  match t:
    case A.AgNone{}:
      False{}
    case _:
      True{}

def act.nu.ci.of(s: ActSym, c: ActCopy, +dt: A.Ag, ds: ActSym, ty: T.Bt, pre: List<&2, U32>, +env: ActEnv) -> NuCi:
  match s c ds:
    case ActSym{+m, +nm, kd, ms, ar, b, +tags, cn, cp} ActCopy{+pars, +cty} ActSym{dm, dn, dk, dms, dar, db, dfs, dc, dcp}:
      +ixs = List.length(&2, String, tags)
      +ok = Bool.and(act.nu.isty(cty), act.nu.isty(dt))
      +r = act.params(64n, Nat.add(pars, ixs), act.inline(100000n, dt, env), dms, Nil{}, env)
      +ict = act.inline(100000n, cty, env)
      act.nu.ci.mk(act.ctor.of(ActSym{m, nm, kd, ms, ar, b, tags, cn, cp}, pars, ict, env, act.ps.last(ixs, act.ps.ps(r))), act.ps.names(act.ps.ps(r)), ty, act.ref.of(act.is.here(env, m), env, m, nm), act.nu.heads(act.after(pars, ict)), pre, ok)

def act.nu.ci.real(+env: ActEnv, +k: String, ty: T.Bt, pre: List<&2, U32>) -> NuCi:
  +dk = act.nu.dkey.of(act.nu.unf(env, act.nu.cdq.key(k)))
  act.nu.ci.of(act.nu.symk(env, k), act.nu.unf(env, act.nu.cty.key(k)), act.nu.cbody(act.nu.unf(env, "fty:" ++ dk)), act.nu.symk(env, dk), ty, pre, env)

def act.nu.ci.k(c: NuK, +env: ActEnv, k: String, ty: T.Bt, pre: List<&2, U32>) -> NuCi:
  match c:
    case NkReal{}:
      act.nu.ci.real(env, k, ty, pre)
    case NkS{}:
      NuCi{True{}, NkS{}, Nil{}, [NuF{List.append(&2, U32, pre, S.b("_1")), T.BtVar{S.b("Nat")}, "$nat"}]}
    case c:
      NuCi{True{}, c, Nil{}, Nil{}}

# a constructor pattern's constructor at a pattern of type ty (pre: its placeholder)
def act.nu.ci(+env: ActEnv, +k: String, ty: T.Bt, pre: List<&2, U32>) -> NuCi:
  act.nu.ci.k(act.nu.kind(k), env, k, ty, pre)

def act.nu.ci.ok(c: NuCi) -> Bool:
  match c:
    case NuCi{ok, k, ref, fs}:
      ok

def act.nu.ci.fs(c: NuCi) -> List<&2, NuF>:
  match c:
    case NuCi{ok, k, ref, fs}:
      fs

# The walk ---------------------------------------------------------------------

def act.nu.st0() -> NuSt:
  NuSt{True{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

def act.nu.sgs(sg: List<&2, NuSg>, t: T.Bt) -> T.Bt:
  match sg:
    case NuSg{x, v} <> rest:
      act.nu.sgs(rest, T.tba.subst(t, x, v))
    case Nil{}:
      t

# a type with the substitution put in
def act.nu.st.ty(st: NuSt, t: T.Bt) -> T.Bt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      act.nu.sgs(List.reverse(&2, NuSg, sg), t)

def act.nu.st.ok(st: NuSt) -> Bool:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      ok

def act.nu.st.bs(st: NuSt) -> List<&2, ActBind>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      bs

def act.nu.st.fl(st: NuSt) -> List<&2, List<&2, U32>>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      fl

def act.nu.st.eqs(st: NuSt) -> List<&2, NuEq>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      eqs

def act.nu.st.vts(st: NuSt) -> List<&2, NuVt>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      vts

def act.nu.st.dots(st: NuSt) -> List<&2, NuDot>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      dots

def act.nu.st.weak(st: NuSt) -> List<&2, NuDot>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      weak

def act.nu.st.vty(st: NuSt) -> List<&2, NuSg>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      vty

def act.nu.st.holes(st: NuSt) -> List<&2, NuHole>:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      holes

def act.nu.first(xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case h <> t:
      h
    case Nil{}:
      T.BtWild{}

def act.nu.pop(k: Nat, xs: List<&2, T.Bt>, acc: List<&2, T.Bt>) -> NuTk:
  match k xs:
    case 1n+p h <> t:
      act.nu.pop(p, t, h <> acc)
    case _ xs:
      NuTk{acc, xs}

def act.nu.tk.args(t: NuTk) -> T.Bt:
  match t:
    case NuTk{xs, rest}:
      T.tba.args(xs)

# the patterns a row's walk left on its stack: the first n, in order
def act.nu.st.pats(st: NuSt, n: Nat) -> T.Bt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      act.nu.tk.args(act.nu.pop(n, ps, Nil{}))

def act.nu.st.bad(st: NuSt) -> NuSt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{False{}, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}

def act.nu.st.okif(b: Bool, st: NuSt) -> NuSt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{Bool.and(b, ok), bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}

def act.nu.st.push(p: T.Bt, t: T.Bt, st: NuSt) -> NuSt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, p <> ps, t <> ts, vty}

# x stands for the term on top of the stack (a placeholder, a split parameter)
def act.nu.st.sgtop(x: List<&2, U32>, st: NuSt) -> NuSt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, +ts, vty}:
      NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, NuSg{x, act.nu.first(ts)} <> sg, ps, ts, vty}

def act.nu.st.var(+pos: Nat, +x: List<&2, U32>, +ty: T.Bt, st: NuSt) -> NuSt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, ActBind{pos, T.BtVar{x}} <> bs, fl, eqs, NuVt{pos, x, ty} <> vts, dots, weak, holes, sg, T.BtPv{T.BmLive{}, x} <> ps, T.BtVar{x} <> ts, NuSg{x, ty} <> vty}

def act.nu.dots.put(m: Maybe<&2, Nat>, x: List<&2, U32>, ty: T.Bt, ds: List<&2, NuDot>) -> List<&2, NuDot>:
  match m:
    case Some{p}:
      NuDot{x, p, ty, True{}} <> ds
    case None{}:
      ds

def act.nu.st.dot(m: Maybe<&2, Nat>, +x: List<&2, U32>, +ty: T.Bt, path: List<&2, Nat>, dk: String, st: NuSt) -> NuSt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, bs, x <> fl, eqs, vts, act.nu.dots.put(m, x, ty, dots), weak, NuHole{path, dk} <> holes, sg, T.BtPv{T.BmLive{}, x} <> ps, T.BtVar{x} <> ts, NuSg{x, ty} <> vty}

def act.nu.st.eqv(x0: List<&2, U32>, +x: List<&2, U32>, ty: T.Bt, st: NuSt) -> NuSt:
  match ty st:
    case T.BtEq{ety, a, b} NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, bs, fl, List.append(&2, NuEq, eqs, [NuEq{ety, a, b, T.BtVar{x}}]), vts, dots, weak, holes, NuSg{x0, T.BtVar{x}} <> sg, T.BtPv{T.BmLive{}, x} <> ps, T.BtVar{x} <> ts, vty}
    case _ NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{False{}, bs, fl, eqs, vts, dots, weak, holes, sg, T.BtPv{T.BmLive{}, x} <> ps, T.BtVar{x} <> ts, vty}

# a constructor pattern's equation fields: x_<i>_eq
def act.nu.eqf(fs: List<&2, NuF>, +nm: List<&2, U32>, +i: Nat, +st: NuSt) -> NuSt:
  match fs:
    case NuF{fx, fty, hk} <> ft:
      act.nu.eqf(ft, nm, 1n+i, act.nu.st.eqv(fx, List.append(&2, U32, nm, S.b("_" ++ Nat.show(i) ++ "_eq")), act.nu.st.ty(st, fty), st))
    case Nil{}:
      st

def act.nu.mk(k: NuK, ref: List<&2, U32>, xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case NkReal{}:
      T.BtCon{ref, T.tba.args(xs)}
    case NkZ{}:
      T.BtNat{S.b("0")}
    case NkS{}:
      T.BtSucc{act.nu.first(xs)}
    case NkT{}:
      T.BtCon{S.b("True"), T.BtANil{}}
    case NkF{}:
      T.BtCon{S.b("False"), T.BtANil{}}
    case NkU{}:
      T.BtCon{S.b("Unit"), T.BtANil{}}

def act.nu.st.con2(+k: NuK, +ref: List<&2, U32>, a: NuTk, b: NuTk, st: NuSt) -> NuSt:
  match a b st:
    case NuTk{xs, ps} NuTk{ys, ts} NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, p0, t0, vty}:
      NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, act.nu.mk(k, ref, xs) <> ps, act.nu.mk(k, ref, ys) <> ts, vty}

# the constructor pattern (and term) from its fields' on the stacks
def act.nu.st.con(c: NuCi, st: NuSt) -> NuSt:
  match c st:
    case NuCi{ok, +k, +ref, fs} NuSt{ok2, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      +n = List.length(&2, NuF, fs)
      act.nu.st.con2(k, ref, act.nu.pop(n, ps, Nil{}), act.nu.pop(n, ts, Nil{}), NuSt{Bool.and(ok, ok2), bs, fl, eqs, vts, dots, weak, holes, sg, Nil{}, Nil{}, vty})

# a name for a variable this path makes, apart from Agda's and the parameters'
def act.nu.fresh(+b: List<&2, U32>, +used: List<&2, List<&2, U32>>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, act.used(b, used), List.append(&2, U32, b, S.b("_v")), b)

def act.nu.cnm(+nm: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  List.append(&2, U32, nm, S.b("_" ++ Nat.show(i)))

# The walk of a pattern p of type ty (pre: its placeholder, nm: the base of
# its variables' names, hk: its type's data key, path: where it is), or of
# a constructor pattern's arguments (a spine: fs its fields from the i-th).
def act.nu.w(p: NuP, fs: List<&2, NuF>, +ty: T.Bt, +pre: List<&2, U32>, +nm: List<&2, U32>, +hk: String, +path: List<&2, Nat>, +i: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>, +used: List<&2, List<&2, U32>>, +env: ActEnv, +st: NuSt) -> NuSt:
  match p fs:
    case NuPS{h, t} NuF{+fx, fty, fhk} <> ft:
      act.nu.w(t, ft, ty, pre, nm, hk, path, 1n+i, hints, pnames, used, env, act.nu.st.sgtop(fx, act.nu.w(h, Nil{}, act.nu.st.ty(st, fty), fx, act.nu.cnm(nm, i), fhk, i <> path, 0n, hints, pnames, used, env, st)))
    case NuPS{h, t} Nil{}:
      act.nu.st.bad(st)
    case NuPE{} fs:
      act.nu.eqf(fs, nm, i, st)
    case NuPV{+pos, ab} fs:
      act.nu.st.var(pos, act.pv.name(pos, hints, pnames), ty, st)
    case NuPD{m} fs:
      act.nu.st.dot(m, act.nu.fresh(nm, used), ty, path, hk, st)
    case NuPC{+k, ps} fs:
      +ci = act.nu.ci(env, k, ty, pre)
      act.nu.st.con(ci, act.nu.w(ps, act.nu.ci.fs(ci), ty, pre, nm, hk, path, 1n, hints, pnames, used, env, act.nu.st.okif(act.nu.ci.ok(ci), st)))
    case _ fs:
      act.nu.st.bad(act.nu.st.push(T.BtWild{}, T.BtWild{}, st))

def act.nu.live.m(m: T.BMode) -> Bool:
  match m:
    case T.BmErased{}:
      False{}
    case _:
      True{}

# whether parameter x is live (a Level one, absent, is)
def act.nu.live(ps: List<&2, T.BParam>, +x: List<&2, U32>) -> Bool:
  match ps:
    case T.BParam{m, +n, ty} <> t:
      Bool.pick(Bool, S.eq(n, x), act.nu.live.m(m), act.nu.live(t, x))
    case Nil{}:
      True{}

def act.nu.st.topv(live: Bool, +pos: Nat, +x: List<&2, U32>, e: T.Bt, +ty: T.Bt, st: NuSt) -> NuSt:
  match live st:
    case True{} NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, ActBind{pos, e} <> bs, fl, eqs, NuVt{pos, x, ty} <> vts, dots, weak, holes, sg, ps, ts, NuSg{x, ty} <> vty}
    case False{} NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, bs, x <> fl, eqs, vts, dots, NuDot{x, pos, ty, False{}} <> weak, holes, sg, ps, ts, NuSg{x, ty} <> vty}

def act.nu.st.flexd(m: Maybe<&2, Nat>, +x: List<&2, U32>, +ty: T.Bt, st: NuSt) -> NuSt:
  match st:
    case NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, bs, x <> fl, eqs, vts, act.nu.dots.put(m, x, ty, dots), weak, holes, sg, ps, ts, NuSg{x, ty} <> vty}

# a parameter the match does not split: Agda's variable there is bound to it
# (an erased one only when no dotted field is that variable), else it is flexible
def act.nu.st.top(p: NuP, +x: List<&2, U32>, e: T.Bt, live: Bool, ty: T.Bt, st: NuSt) -> NuSt:
  match p:
    case NuPV{pos, ab}:
      act.nu.st.topv(live, pos, x, e, ty, st)
    case NuPD{m}:
      act.nu.st.flexd(m, x, ty, st)
    case _:
      act.nu.st.flexd(None{}, x, ty, st)

# A clause's (or a missing case's) patterns, one per parameter: a split
# one's is walked (its stack holds the case's patterns in order, and the
# parameter stands for its term after it), another's binds or flexes the
# parameter.
def act.nu.row(p: NuP, scr: List<&2, Bool>, ents: List<&2, T.Bt>, ks: List<&2, String>, +hps: List<&2, T.BParam>, +i: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>, +used: List<&2, List<&2, U32>>, +env: ActEnv, +st: NuSt) -> NuSt:
  match p scr ents ks:
    case NuPS{h, t} True{} <> sr e <> er k <> kr:
      +x = act.var.name(e)
      act.nu.row(t, sr, er, kr, hps, 1n+i, hints, pnames, used, env, act.nu.st.sgtop(x, act.nu.w(h, Nil{}, act.nu.st.ty(st, act.param.ty(hps, x)), S.b("a2b_nup" ++ Nat.show(i)), x, k, [i], 0n, hints, pnames, used, env, st)))
    case NuPS{h, t} False{} <> sr +e <> er k <> kr:
      +x = act.var.name(e)
      act.nu.row(t, sr, er, kr, hps, 1n+i, hints, pnames, used, env, act.nu.st.top(h, x, e, act.nu.live(hps, x), act.nu.st.ty(st, act.param.ty(hps, x)), st))
    case _ _ _ _:
      st

def act.nu.bound(+pos: Nat, bs: List<&2, ActBind>) -> Bool:
  match bs:
    case ActBind{p, t} <> rest:
      Bool.or(Nat.is_eq(p, pos), act.nu.bound(pos, rest))
    case ActBDot{p, x} <> rest:
      act.nu.bound(pos, rest)
    case Nil{}:
      False{}

def act.nu.rm.put(drop: Bool, h: List<&2, U32>, t: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match drop:
    case True{}:
      t
    case False{}:
      h <> t

def act.nu.rm(+x: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      act.nu.rm.put(S.eq(h, x), h, act.nu.rm(x, t))
    case Nil{}:
      Nil{}

def act.nu.vts.put(live: Bool, v: NuVt, vts: List<&2, NuVt>) -> List<&2, NuVt>:
  match live:
    case True{}:
      v <> vts
    case False{}:
      vts

def act.nu.promote1(b: Bool, +x: List<&2, U32>, +pos: Nat, ty: T.Bt, live: Bool, st: NuSt) -> NuSt:
  match b st:
    case True{} st:
      st
    case False{} NuSt{ok, bs, fl, eqs, vts, dots, weak, holes, sg, ps, ts, vty}:
      NuSt{ok, ActBind{pos, T.BtVar{x}} <> bs, act.nu.rm(x, fl), eqs, act.nu.vts.put(live, NuVt{pos, x, ty}, vts), dots, weak, holes, sg, ps, ts, vty}

# an Agda variable no pattern binds is bound to a flexible variable that is exactly it
def act.nu.promote(ds: List<&2, NuDot>, +st: NuSt) -> NuSt:
  match ds:
    case NuDot{+x, +pos, ty, live} <> rest:
      act.nu.promote(rest, act.nu.promote1(act.nu.bound(pos, act.nu.st.bs(st)), x, pos, ty, live, st))
    case Nil{}:
      st

def act.nu.prom(+st: NuSt) -> NuSt:
  +s1 = act.nu.promote(List.reverse(&2, NuDot, act.nu.st.dots(st)), st)
  act.nu.promote(List.reverse(&2, NuDot, act.nu.st.weak(s1)), s1)

# Equations --------------------------------------------------------------------

def act.nu.nat() -> T.Bt:
  T.BtVar{S.b("Nat")}

def act.nu.esym(+ty: T.Bt, a: T.Bt, b: T.Bt, e: T.Bt) -> T.Bt:
  act.bt.app("Equal.sym", [T.BtDead{ty}, T.BtDead{a}, T.BtDead{b}, e])

def act.nu.etrans(ty: T.Bt, a: T.Bt, b: T.Bt, c: T.Bt, p: T.Bt, q: T.Bt) -> T.Bt:
  act.bt.app("Equal.trans", [T.BtDead{ty}, T.BtDead{a}, T.BtDead{b}, T.BtDead{c}, p, q])

def act.nu.econg(ta: T.Bt, tb: T.Bt, f: T.Bt, a: T.Bt, b: T.Bt, e: T.Bt) -> T.Bt:
  act.bt.app("Equal.cong", [T.BtDead{ta}, T.BtDead{tb}, T.BtDead{f}, T.BtDead{a}, T.BtDead{b}, e])

def act.nu.sucs(k: Nat) -> T.Bt:
  match k:
    case 0n:
      T.BtNat{S.b("0")}
    case 1n+p:
      T.BtSucc{act.nu.sucs(p)}

def act.nu.lit.t(small: Bool, k: Nat, s: List<&2, U32>) -> T.Bt:
  match small:
    case True{}:
      act.nu.sucs(k)
    case False{}:
      T.BtNat{s}

# a term with its literals as suc chains (up to 64) and no BtDead
def act.nu.norm(t: T.Bt) -> T.Bt:
  match t:
    case T.BtDead{x}:
      act.nu.norm(x)
    case T.BtNat{+s}:
      +k = act.cq.digits(s, 0n)
      act.nu.lit.t(Nat.is_lt(k, 65n), k, s)
    case T.BtSucc{x}:
      T.BtSucc{act.nu.norm(x)}
    case T.BtCon{c, as}:
      T.BtCon{c, act.nu.norm(as)}
    case T.BtArgs{h, t}:
      T.BtArgs{act.nu.norm(h), act.nu.norm(t)}
    case t:
      t

def act.nu.same(a: T.Bt, b: T.Bt) -> Bool:
  match a b:
    case T.BtVar{x} T.BtVar{y}:
      S.eq(x, y)
    case T.BtSucc{x} T.BtSucc{y}:
      act.nu.same(x, y)
    case T.BtNat{x} T.BtNat{y}:
      S.eq(x, y)
    case T.BtDead{x} y:
      act.nu.same(x, y)
    case x T.BtDead{y}:
      act.nu.same(x, y)
    case T.BtCon{x, xs} T.BtCon{y, ys}:
      Bool.and(S.eq(x, y), act.nu.same(xs, ys))
    case T.BtApp{f, xs} T.BtApp{g, ys}:
      Bool.and(act.nu.same(f, g), act.nu.same(xs, ys))
    case T.BtArgs{x, xs} T.BtArgs{y, ys}:
      Bool.and(act.nu.same(x, y), act.nu.same(xs, ys))
    case T.BtANil{} T.BtANil{}:
      True{}
    case T.BtTyApp{x, xs} T.BtTyApp{y, ys}:
      Bool.and(S.eq(x, y), act.nu.same(xs, ys))
    case _ _:
      False{}

def act.nu.pf.chain(m: Maybe<&2, T.Bt>, ty: T.Bt, t0: T.Bt, t: T.Bt, t2: T.Bt, st: T.Bt) -> T.Bt:
  match m:
    case None{}:
      st
    case Some{p}:
      act.nu.etrans(ty, t0, t, t2, p, st)

def act.nu.isvar(+x: List<&2, U32>, t: T.Bt) -> Bool:
  match t:
    case T.BtVar{y}:
      S.eq(x, y)
    case _:
      False{}

# {t == t[x := s]} from q : {x == s}
def act.nu.step.pf(b: Bool, +x: List<&2, U32>, xty: T.Bt, +s: T.Bt, q: T.Bt, ty: T.Bt, t: T.Bt) -> T.Bt:
  match b:
    case True{}:
      q
    case False{}:
      act.nu.econg(xty, ty, T.BtLam{T.BmLive{}, S.b("a2b_y"), T.tba.subst(t, x, T.BtVar{S.b("a2b_y")})}, T.BtVar{x}, s, q)

def act.nu.sub.step(+x: List<&2, U32>, xty: T.Bt, +s: T.Bt, q: T.Bt, +ty: T.Bt, t0: T.Bt, cur: NuPf) -> NuPf:
  match cur:
    case NuPf{+t, m}:
      +t2 = T.tba.subst(t, x, s)
      NuPf{t2, Some{act.nu.pf.chain(m, ty, t0, t, t2, act.nu.step.pf(act.nu.isvar(x, t), x, xty, s, q, ty, t))}}

def act.nu.pf.t(c: NuPf) -> T.Bt:
  match c:
    case NuPf{t, m}:
      t

def act.nu.sub.at(b: Bool, +x: List<&2, U32>, xty: T.Bt, +s: T.Bt, q: T.Bt, +ty: T.Bt, t0: T.Bt, cur: NuPf) -> NuPf:
  match b:
    case True{}:
      act.nu.sub.step(x, xty, s, q, ty, t0, cur)
    case False{}:
      cur

def act.nu.sub1(sols: List<&2, NuSol>, +ty: T.Bt, +t0: T.Bt, +cur: NuPf) -> NuPf:
  match sols:
    case NuSol{+x, xty, s, q} <> rest:
      act.nu.sub1(rest, ty, t0, act.nu.sub.at(act.occurs(x, act.nu.pf.t(cur)), x, xty, s, q, ty, t0, cur))
    case Nil{}:
      cur

# t with the solutions put in until none is left, and its proof
def act.nu.subn(fuel: Nat, +sols: List<&2, NuSol>, +ty: T.Bt, +t0: T.Bt, cur: NuPf) -> NuPf:
  match fuel:
    case 1n+f:
      act.nu.subn(f, sols, ty, t0, act.nu.sub1(sols, ty, t0, cur))
    case 0n:
      cur

def act.nu.pf.join(+ty: T.Bt, +a: T.Bt, +b: T.Bt, +a2: T.Bt, +b2: T.Bt, ma: Maybe<&2, T.Bt>, p: T.Bt, mb: Maybe<&2, T.Bt>) -> T.Bt:
  match ma mb:
    case None{} None{}:
      p
    case None{} Some{q}:
      act.nu.etrans(ty, a, b, b2, p, q)
    case Some{r} None{}:
      act.nu.etrans(ty, a2, a, b, act.nu.esym(ty, a, a2, r), p)
    case Some{r} Some{q}:
      act.nu.etrans(ty, a2, a, b2, act.nu.esym(ty, a, a2, r), act.nu.etrans(ty, a, b, b2, p, q))

def act.nu.eq.mk(+ty: T.Bt, +a: T.Bt, +b: T.Bt, p: T.Bt, ra: NuPf, rb: NuPf) -> NuEq:
  match ra rb:
    case NuPf{+a2, ma} NuPf{+b2, mb}:
      NuEq{ty, a2, b2, act.nu.pf.join(ty, a, b, a2, b2, ma, p, mb)}

def act.nu.eq.sub(+sols: List<&2, NuSol>, e: NuEq) -> NuEq:
  match e:
    case NuEq{+ty, +a, +b, p}:
      +n = Nat.add(1n, List.length(&2, NuSol, sols))
      act.nu.eq.mk(ty, a, b, p, act.nu.subn(n, sols, ty, a, NuPf{a, None{}}), act.nu.subn(n, sols, ty, b, NuPf{b, None{}}))

def act.nu.eq.norm(e: NuEq) -> NuEq:
  match e:
    case NuEq{ty, a, b, p}:
      NuEq{ty, act.nu.norm(a), act.nu.norm(b), p}

# suc's injectivity: {1n+a == 1n+b} gives {a == b}
def act.nu.peel(fuel: Nat, e: NuEq) -> NuEq:
  match fuel e:
    case 1n+f NuEq{ty, T.BtSucc{+a}, T.BtSucc{+b}, p}:
      act.nu.peel(f, NuEq{ty, a, b, act.nu.econg(act.nu.nat(), act.nu.nat(), T.BtVar{S.b("a2b_pred")}, T.BtSucc{a}, T.BtSucc{b}, p)})
    case _ e:
      e

def act.nu.iszero(t: T.Bt) -> Bool:
  match t:
    case T.BtNat{s}:
      S.eq(s, S.b("0"))
    case _:
      False{}

def act.nu.issuc(t: T.Bt) -> Bool:
  match t:
    case T.BtSucc{x}:
      True{}
    case _:
      False{}

def act.nu.iscon(+c: String, t: T.Bt) -> Bool:
  match t:
    case T.BtCon{x, as}:
      S.eq(x, S.b(c))
    case _:
      False{}

def act.nu.cons2(a: T.Bt, b: T.Bt) -> Nat:
  match a b:
    case T.BtCon{x, as} T.BtCon{y, bs}:
      Bool.pick(Nat, S.eq(x, y), 2n, 1n)
    case _ _:
      0n

def act.nu.clash(+a: T.Bt, +b: T.Bt) -> Bool:
  Bool.or(Bool.or(Bool.and(act.nu.iszero(a), act.nu.issuc(b)), Bool.and(act.nu.issuc(a), act.nu.iszero(b))), Nat.is_eq(act.nu.cons2(a, b), 1n))

# a is a flexible variable b does not mention
def act.nu.flexv(a: T.Bt, +b: T.Bt, +fl: List<&2, List<&2, U32>>) -> Bool:
  match a:
    case T.BtVar{+x}:
      Bool.and(act.used(x, fl), Bool.not(act.occurs(x, b)))
    case _:
      False{}

def act.nu.cls(+a: T.Bt, +b: T.Bt, +fl: List<&2, List<&2, U32>>) -> NuC:
  Bool.pick(NuC, act.nu.same(a, b), NcSame{}, Bool.pick(NuC, act.nu.flexv(a, b, fl), NcVarL{}, Bool.pick(NuC, act.nu.flexv(b, a, fl), NcVarR{}, Bool.pick(NuC, act.nu.clash(a, b), NcClash{}, Bool.pick(NuC, Nat.is_eq(act.nu.cons2(a, b), 2n), NcInj{}, NcStuck{})))))

def act.nu.cls.e(e: NuEq, +fl: List<&2, List<&2, U32>>) -> NuC:
  match e:
    case NuEq{ty, +a, +b, p}:
      act.nu.cls(a, b, fl)

def act.nu.u.add(c: NuC, e: NuEq, u: NuU) -> NuU:
  match c e u:
    case NcVarL{} NuEq{ty, T.BtVar{x}, b, p} NuU{sols, cl}:
      NuU{List.append(&2, NuSol, sols, [NuSol{x, ty, b, p}]), cl}
    case NcVarR{} NuEq{+ty, +a, T.BtVar{+y}, p} NuU{sols, cl}:
      NuU{List.append(&2, NuSol, sols, [NuSol{y, ty, a, act.nu.esym(ty, a, T.BtVar{y}, p)}]), cl}
    case NcClash{} e NuU{sols, cl}:
      NuU{sols, List.append(&2, NuEq, cl, [e])}
    case _ _ u:
      u

def act.nu.u.sols(u: NuU) -> List<&2, NuSol>:
  match u:
    case NuU{sols, cl}:
      sols

def act.nu.u.cl(u: NuU) -> List<&2, NuEq>:
  match u:
    case NuU{sols, cl}:
      cl

def act.nu.isnat(t: T.Bt) -> Bool:
  match t:
    case T.BtSucc{x}:
      True{}
    case T.BtNat{s}:
      True{}
    case _:
      False{}

def act.nu.vty.or(b: Bool, ty: T.Bt, m: Maybe<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match b:
    case True{}:
      Some{ty}
    case False{}:
      m

def act.nu.vty.find(tys: List<&2, NuSg>, +x: List<&2, U32>) -> Maybe<&2, T.Bt>:
  match tys:
    case NuSg{+y, ty} <> rest:
      act.nu.vty.or(S.eq(x, y), ty, act.nu.vty.find(rest, x))
    case Nil{}:
      None{}

def act.nu.vty.mk(x: List<&2, U32>, m: Maybe<&2, T.Bt>) -> Maybe<&2, NuSg>:
  match m:
    case Some{ty}:
      Some{NuSg{x, ty}}
    case None{}:
      None{}

def act.nu.vty.var(+tys: List<&2, NuSg>, t: T.Bt) -> Maybe<&2, NuSg>:
  match t:
    case T.BtVar{+x}:
      act.nu.vty.mk(x, act.nu.vty.find(tys, x))
    case _:
      None{}

def act.nu.vty.alt(m: Maybe<&2, NuSg>, n: Maybe<&2, NuSg>) -> Maybe<&2, NuSg>:
  match m:
    case Some{v}:
      Some{v}
    case None{}:
      n

def act.nu.iscc(+c: List<&2, U32>, t: T.Bt) -> Bool:
  match t:
    case T.BtCon{x, as}:
      S.eq(x, c)
    case _:
      False{}

def act.nu.ty.of(m: Maybe<&2, NuSg>) -> Maybe<&2, T.Bt>:
  match m:
    case Some{NuSg{x, ty}}:
      Some{ty}
    case None{}:
      None{}

# a field's type at an equation between two applications of constructor
# c (of type ty): a side that is a variable of known type, else Nat for a
# Nat term, else ty itself when a side applies c (a recursive field)
def act.nu.vty.of(+tys: List<&2, NuSg>, +x: T.Bt, +y: T.Bt, +c: List<&2, U32>, +ty: T.Bt) -> Maybe<&2, T.Bt>:
  act.nu.ty.of(act.nu.vty.alt(act.nu.vty.var(tys, x), act.nu.vty.alt(act.nu.vty.var(tys, y), Bool.pick(Maybe<&2, NuSg>, Bool.or(act.nu.isnat(x), act.nu.isnat(y)), Some{NuSg{Nil{}, act.nu.nat()}}, Bool.pick(Maybe<&2, NuSg>, Bool.or(act.nu.iscc(c, x), act.nu.iscc(c, y)), Some{NuSg{Nil{}, ty}}, None{})))))

# c's projection of field i of n at type ty -> ti, its other arms the default d
def act.nu.proj(+c: List<&2, U32>, +n: Nat, +i: Nat, d: T.Bt, +ty: T.Bt, +ti: T.Bt) -> T.Bt:
  T.BtApp{T.BtAnn{T.BtLam{T.BmLive{}, S.b("a2b_d"), act.inj.prj(c, n, i, S.b("a2b_d"), ty, ti)}, T.BtPi{T.BmLive{}, S.b("_"), False{}, ti, T.BtPi{T.BmLive{}, S.b("_"), False{}, ty, ti}}}, T.tba.args([d])}

def act.nu.inj.one(m: Maybe<&2, T.Bt>, +x: T.Bt, y: T.Bt, +i: Nat, +n: Nat, +c: List<&2, U32>, +ty: T.Bt, +a: T.Bt, +b: T.Bt, +p: T.Bt) -> List<&2, NuEq>:
  match m:
    case Some{+ti}:
      [NuEq{ti, x, y, act.nu.econg(ty, ti, act.nu.proj(c, n, i, x, ty, ti), a, b, p)}]
    case None{}:
      Nil{}

def act.nu.inj.eqs(xs: List<&2, T.Bt>, ys: List<&2, T.Bt>, +i: Nat, +n: Nat, +c: List<&2, U32>, +ty: T.Bt, +a: T.Bt, +b: T.Bt, +p: T.Bt, +tys: List<&2, NuSg>) -> List<&2, NuEq>:
  match xs ys:
    case +x <> xt +y <> yt:
      List.append(&2, NuEq, act.nu.inj.one(act.nu.vty.of(tys, x, y, c, ty), x, y, i, n, c, ty, a, b, p), act.nu.inj.eqs(xt, yt, 1n+i, n, c, ty, a, b, p, tys))
    case _ _:
      Nil{}

def act.nu.inj(a: T.Bt, b: T.Bt, +ty: T.Bt, +p: T.Bt, +tys: List<&2, NuSg>) -> List<&2, NuEq>:
  match a b:
    case T.BtCon{+c, +as} T.BtCon{cb, +bs}:
      +xs = act.nu.spine(as)
      act.nu.inj.eqs(xs, act.nu.spine(bs), 1n, List.length(&2, T.Bt, xs), c, ty, T.BtCon{c, as}, T.BtCon{cb, bs}, p, tys)
    case _ _:
      Nil{}

# the equations an equation between two applications of one constructor
# splits into (its fields', by the constructor's projections)
def act.nu.u.new(c: NuC, e: NuEq, +tys: List<&2, NuSg>) -> List<&2, NuEq>:
  match c e:
    case NcInj{} NuEq{ty, a, b, p}:
      act.nu.inj(a, b, ty, p, tys)
    case _ _:
      Nil{}

def act.nu.u.prep(+sols: List<&2, NuSol>, e: NuEq) -> NuEq:
  act.nu.peel(64n, act.nu.eq.norm(act.nu.eq.sub(sols, e)))

def act.nu.u.eqs(fuel: Nat, eqs: List<&2, NuEq>, +fl: List<&2, List<&2, U32>>, +tys: List<&2, NuSg>, +u: NuU) -> NuU:
  match fuel eqs:
    case 1n+f e <> rest:
      +e2 = act.nu.u.prep(act.nu.u.sols(u), e)
      +c = act.nu.cls.e(e2, fl)
      act.nu.u.eqs(f, List.append(&2, NuEq, act.nu.u.new(c, e2, tys), rest), fl, tys, act.nu.u.add(c, e2, u))
    case _ _:
      u

# the equations solved for the flexible variables (twice: one stuck the
# first time may be solved by a later one)
def act.nu.unify(+eqs: List<&2, NuEq>, +fl: List<&2, List<&2, U32>>, +tys: List<&2, NuSg>) -> NuU:
  act.nu.u.eqs(512n, List.append(&2, NuEq, eqs, eqs), fl, tys, NuU{Nil{}, Nil{}})

def act.nu.xty(sols: List<&2, NuSol>, +x: List<&2, U32>) -> T.Bt:
  match sols:
    case NuSol{+y, ty, t, pf} <> rest:
      Bool.pick(T.Bt, S.eq(x, y), ty, act.nu.xty(rest, x))
    case Nil{}:
      act.nu.nat()

# x's value, and the proof of {x == it} (None: no solution)
def act.nu.solve(+sols: List<&2, NuSol>, +x: List<&2, U32>) -> NuPf:
  act.nu.subn(Nat.add(1n, List.length(&2, NuSol, sols)), sols, act.nu.xty(sols, x), T.BtVar{x}, NuPf{T.BtVar{x}, None{}})

# Cases ------------------------------------------------------------------------

def act.nu.wrap(ss: List<&2, NuStm>, body: T.Bt) -> T.Bt:
  match ss:
    case NsLet{x, v} <> t:
      T.BtLet{x, v, act.nu.wrap(t, body)}
    case NsRw{e, p} <> t:
      T.BtRw{e, p, act.nu.wrap(t, body)}
    case Nil{}:
      body

def act.nu.cs.ty(c: NuCs) -> T.Bt:
  match c:
    case NuCs{ss, x, ty}:
      ty

def act.nu.cast1(b: Bool, +y: List<&2, U32>, r: NuPf, yty: T.Bt, k: Nat, c: NuCs) -> NuCs:
  match b r c:
    case True{} NuPf{+t, Some{pf}} NuCs{ss, +x, +ty}:
      +x2 = List.append(&2, U32, x, S.b("_c" ++ Nat.show(k)))
      NuCs{List.append(&2, NuStm, ss, [NsLet{x2, act.bt.app("a2b_cast", [T.BtDead{yty}, T.BtDead{T.BtLam{T.BmLive{}, S.b("a2b_k"), T.tba.subst(ty, y, T.BtVar{S.b("a2b_k")})}}, T.BtDead{T.BtVar{y}}, T.BtDead{t}, pf, T.BtVar{x}])}]), x2, T.tba.subst(ty, y, t)}
    case _ _ c:
      c

# a binder of type ty cast along each flexible variable ty mentions that has a value
def act.nu.casts(fl: List<&2, List<&2, U32>>, +sols: List<&2, NuSol>, +k: Nat, +c: NuCs) -> NuCs:
  match fl:
    case +y <> rest:
      act.nu.casts(rest, sols, 1n+k, act.nu.cast1(act.occurs(y, act.nu.cs.ty(c)), y, act.nu.solve(sols, y), act.nu.xty(sols, y), k, c))
    case Nil{}:
      c

def act.nu.vcast.put(pos: Nat, c: NuCs, d: NuBd) -> NuBd:
  match c d:
    case NuCs{ss, x2, ty2} NuBd{ss0, bs}:
      NuBd{List.append(&2, NuStm, ss0, ss), ActBind{pos, T.BtVar{x2}} <> bs}

def act.nu.vcasts(vts: List<&2, NuVt>, +fl: List<&2, List<&2, U32>>, +sols: List<&2, NuSol>, d: NuBd) -> NuBd:
  match vts:
    case NuVt{pos, x, ty} <> rest:
      act.nu.vcasts(rest, fl, sols, act.nu.vcast.put(pos, act.nu.casts(fl, sols, 1n, NuCs{Nil{}, x, ty}), d))
    case Nil{}:
      d

def act.nu.gl.g(g: NuGl) -> T.Bt:
  match g:
    case NuGl{ss, g}:
      g

def act.nu.rw1(b: Bool, +y: List<&2, U32>, r: NuPf, yty: T.Bt, g: NuGl) -> NuGl:
  match b r g:
    case True{} NuPf{+t, Some{pf}} NuGl{ss, +goal}:
      +h = List.append(&2, U32, y, S.b("_is"))
      NuGl{List.append(&2, NuStm, ss, [NsLet{h, act.nu.esym(yty, T.BtVar{y}, t, pf)}, NsRw{T.BtVar{h}, T.tba.subst(goal, y, T.BtWild{})}]), T.tba.subst(goal, y, t)}
    case _ _ g:
      g

# the goal rewritten along each flexible variable it mentions that has a value
def act.nu.rws(fl: List<&2, List<&2, U32>>, +sols: List<&2, NuSol>, +g: NuGl) -> NuGl:
  match fl:
    case +y <> rest:
      act.nu.rws(rest, sols, act.nu.rw1(act.occurs(y, act.nu.gl.g(g)), y, act.nu.solve(sols, y), act.nu.xty(sols, y), g))
    case Nil{}:
      g

# an impossible case: a clash {a == b} through Bool.pick at the goal
def act.nu.refute.e(e: NuEq, +g: T.Bt) -> T.Bt:
  match e:
    case NuEq{+ty, +a, +b, p}:
      T.BtLet{S.b("a2b_cl"), p, act.abs.refute.or(act.abs.disc.ty(act.nu.norm(ty), a), act.abs.lm.ab(a, b, ty), S.b("a2b_cl"), g)}

def act.nu.bd.ss(d: NuBd) -> List<&2, NuStm>:
  match d:
    case NuBd{ss, bs}:
      ss

def act.nu.bd.bs(d: NuBd) -> List<&2, ActBind>:
  match d:
    case NuBd{ss, bs}:
      bs

def act.nu.gl.ss(g: NuGl) -> List<&2, NuStm>:
  match g:
    case NuGl{ss, g}:
      ss

def act.nu.clause.of(cl: List<&2, NuEq>, +sols: List<&2, NuSol>, +st: NuSt, body: A.Ag, +n: Nat, +env: ActEnv, +g0: T.Bt) -> T.Bt:
  match cl:
    case e <> t:
      act.nu.refute.e(e, g0)
    case Nil{}:
      +fl = act.nu.st.fl(st)
      +bd = act.nu.vcasts(act.nu.st.vts(st), fl, sols, NuBd{Nil{}, act.nu.st.bs(st)})
      +gl = act.nu.rws(fl, sols, NuGl{Nil{}, g0})
      act.nu.wrap(List.append(&2, NuStm, act.nu.bd.ss(bd), act.nu.gl.ss(gl)), act.abs.body(None{}, body, act.ctx.of(n, act.nu.bd.bs(bd)), env, act.nu.gl.g(gl)))

# a clause's case body: its equations solved, the binders cast, the goal
# rewritten, the body
def act.nu.clause(+st: NuSt, body: A.Ag, +n: Nat, +env: ActEnv, ret: T.Bt) -> T.Bt:
  +u = act.nu.unify(act.nu.st.eqs(st), act.nu.st.fl(st), act.nu.st.vty(st))
  act.nu.clause.of(act.nu.u.cl(u), act.nu.u.sols(u), st, body, n, env, act.nu.st.ty(st, ret))

# Coverage ---------------------------------------------------------------------

def act.nu.app(a: NuP, b: NuP) -> NuP:
  match a:
    case NuPS{h, t}:
      NuPS{h, act.nu.app(t, b)}
    case _:
      b

def act.nu.wilds(k: Nat) -> NuP:
  match k:
    case 1n+p:
      NuPS{NuPD{None{}}, act.nu.wilds(p)}
    case 0n:
      NuPE{}

def act.nu.takes(k: Nat, p: NuP) -> NuP:
  match k p:
    case 1n+q NuPS{h, t}:
      NuPS{h, act.nu.takes(q, t)}
    case _ _:
      NuPE{}

def act.nu.drops(k: Nat, p: NuP) -> NuP:
  match k p:
    case 1n+q NuPS{h, t}:
      act.nu.drops(q, t)
    case _ p:
      p

# a clause's patterns at the split parameters
def act.nu.cols(p: NuP, scr: List<&2, Bool>) -> NuP:
  match p scr:
    case NuPS{h, t} True{} <> st:
      NuPS{h, act.nu.cols(t, st)}
    case NuPS{h, t} False{} <> st:
      act.nu.cols(t, st)
    case _ _:
      NuPE{}

# a missing case's patterns at every parameter (a wildcard at one not split)
def act.nu.uncols(scr: List<&2, Bool>, p: NuP) -> NuP:
  match scr p:
    case True{} <> st NuPS{h, t}:
      NuPS{h, act.nu.uncols(st, t)}
    case False{} <> st p:
      NuPS{NuPD{None{}}, act.nu.uncols(st, p)}
    case _ _:
      NuPE{}

def act.nu.ncols(scr: List<&2, Bool>) -> Nat:
  match scr:
    case True{} <> t:
      1n+act.nu.ncols(t)
    case False{} <> t:
      act.nu.ncols(t)
    case Nil{}:
      0n

def act.nu.key0(rows: List<&2, NuP>) -> String:
  match rows:
    case NuPS{NuPC{k, ps}, t} <> rest:
      k
    case r <> rest:
      act.nu.key0(rest)
    case Nil{}:
      ""

def act.nu.tails(rows: List<&2, NuP>) -> List<&2, NuP>:
  match rows:
    case NuPS{h, t} <> rest:
      t <> act.nu.tails(rest)
    case r <> rest:
      act.nu.tails(rest)
    case Nil{}:
      Nil{}

def act.nu.spec1(r: NuP, +c: String, +ar: Nat) -> List<&2, NuP>:
  match r:
    case NuPS{NuPC{k, ps}, t}:
      Bool.pick(List<&2, NuP>, String.eq(k, c), [act.nu.app(ps, t)], Nil{})
    case NuPS{NuPV{p, a}, t}:
      [act.nu.app(act.nu.wilds(ar), t)]
    case NuPS{NuPD{m}, t}:
      [act.nu.app(act.nu.wilds(ar), t)]
    case _:
      Nil{}

# the rows a constructor c of ar arguments at the first column leaves
def act.nu.spec(rows: List<&2, NuP>, +c: String, +ar: Nat) -> List<&2, NuP>:
  match rows:
    case r <> rest:
      List.append(&2, NuP, act.nu.spec1(r, c, ar), act.nu.spec(rest, c, ar))
    case Nil{}:
      Nil{}

def act.nu.build(cx: List<&2, NuWr>, +sp: NuP) -> NuP:
  match cx:
    case NwWild{} <> rest:
      act.nu.build(rest, NuPS{NuPD{None{}}, sp})
    case NwCon{k, +ar} <> rest:
      act.nu.build(rest, NuPS{NuPC{k, act.nu.takes(ar, sp)}, act.nu.drops(ar, sp)})
    case Nil{}:
      sp

def act.nu.isnil(rows: List<&2, NuP>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case _:
      False{}

def act.nu.mj.out(j: NuMj) -> List<&2, NuP>:
  match j:
    case NuMj{+rows, +w, cx}:
      Bool.pick(List<&2, NuP>, act.nu.isnil(rows), [act.nu.build(cx, act.nu.wilds(w))], Nil{})

def act.nu.mj.sibs(ks: List<&2, String>, +rows: List<&2, NuP>, +w: Nat, +cx: List<&2, NuWr>, +env: ActEnv) -> List<&2, NuMj>:
  match ks:
    case +c <> rest:
      +ar = act.nu.arity(env, c)
      NuMj{act.nu.spec(rows, c, ar), Nat.sub(Nat.add(ar, w), 1n), NwCon{c, ar} <> cx} <> act.nu.mj.sibs(rest, rows, w, cx, env)
    case Nil{}:
      Nil{}

def act.nu.mj.split(con: Bool, +k0: String, rows: List<&2, NuP>, w: Nat, cx: List<&2, NuWr>, +env: ActEnv) -> List<&2, NuMj>:
  match con:
    case False{}:
      [NuMj{act.nu.tails(rows), Nat.sub(w, 1n), NwWild{} <> cx}]
    case True{}:
      act.nu.mj.sibs(act.nu.sibs(env, act.nu.dkey(env, k0)), rows, w, cx, env)

def act.nu.mj.next2(stop: Bool, +rows: List<&2, NuP>, w: Nat, cx: List<&2, NuWr>, +env: ActEnv) -> List<&2, NuMj>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      +k0 = act.nu.key0(rows)
      act.nu.mj.split(Bool.not(String.eq(k0, "")), k0, rows, w, cx, env)

def act.nu.mj.next(j: NuMj, +env: ActEnv) -> List<&2, NuMj>:
  match j:
    case NuMj{+rows, +w, cx}:
      act.nu.mj.next2(Bool.or(act.nu.isnil(rows), Nat.is_eq(w, 0n)), rows, w, cx, env)

# Maranget's missing patterns: a job is the rows left, their width, and
# how to put a missing row of them back into the whole (innermost first)
def act.nu.miss(fuel: Nat, js: List<&2, NuMj>, +env: ActEnv, acc: List<&2, NuP>) -> List<&2, NuP>:
  match fuel js:
    case 1n+f +j <> rest:
      act.nu.miss(f, List.append(&2, NuMj, act.nu.mj.next(j, env), rest), env, List.append(&2, NuP, act.nu.mj.out(j), acc))
    case _ _:
      acc

# a pattern with the one at path (from the root: a parameter's place, then
# a constructor field's, from 1) replaced
def act.nu.put(p: NuP, sp: Bool, i: Nat, path: List<&2, Nat>, +new: NuP) -> NuP:
  match p sp i path:
    case NuPS{h, t} True{} 0n path:
      NuPS{act.nu.put(h, False{}, 0n, path, new), t}
    case NuPS{h, t} True{} 1n+q path:
      NuPS{h, act.nu.put(t, True{}, q, path, new)}
    case p False{} i Nil{}:
      new
    case NuPC{k, ps} False{} i j <> rest:
      NuPC{k, act.nu.put(ps, True{}, Nat.sub(j, 1n), rest, new)}
    case p sp i path:
      p

def act.nu.put.at(row: NuP, path: List<&2, Nat>, new: NuP) -> NuP:
  match path:
    case j <> rest:
      act.nu.put(row, True{}, j, rest, new)
    case Nil{}:
      row

def act.nu.hole.ok(+dk: String) -> Bool:
  Bool.and(act.nu.real(dk), Bool.not(String.eq(dk, "")))

def act.nu.hole.or(b: Bool, h: NuHole, m: Maybe<&2, NuHole>) -> Maybe<&2, NuHole>:
  match b:
    case True{}:
      Some{h}
    case False{}:
      m

# the first wildcard of a data type's (not Nat's, Bool's) to split
def act.nu.hole.pick(hs: List<&2, NuHole>, +env: ActEnv) -> Maybe<&2, NuHole>:
  match hs:
    case NuHole{path, +dk} <> rest:
      act.nu.hole.or(act.nu.hole.ok(dk), NuHole{path, dk}, act.nu.hole.pick(rest, env))
    case Nil{}:
      None{}

def act.nu.split.rows(ks: List<&2, String>, +row: NuP, +path: List<&2, Nat>, +d: Nat, +env: ActEnv) -> List<&2, NuRj>:
  match ks:
    case +c <> rest:
      NuRj{act.nu.put.at(row, path, NuPC{c, act.nu.wilds(act.nu.arity(env, c))}), d} <> act.nu.split.rows(rest, row, path, d, env)
    case Nil{}:
      Nil{}

def act.nu.cx.row(+cx: NuCx, row: NuP) -> NuSt:
  match cx:
    case NuCx{scr, ents, ks, hps, pnames, env, ret}:
      act.nu.row(row, scr, ents, ks, hps, 0n, Nil{}, pnames, pnames, env, act.nu.st0())

def act.nu.cx.env(cx: NuCx) -> ActEnv:
  match cx:
    case NuCx{scr, ents, ks, hps, pnames, env, ret}:
      env

def act.nu.cx.ret(cx: NuCx) -> T.Bt:
  match cx:
    case NuCx{scr, ents, ks, hps, pnames, env, ret}:
      ret

def act.nu.cx.n(cx: NuCx) -> Nat:
  match cx:
    case NuCx{scr, ents, ks, hps, pnames, env, ret}:
      act.nu.ncols(scr)

# a missing case: refuted by a clash among its equations, else split at a
# wildcard (depth d), else a gap
def act.nu.ref.out(cl: List<&2, NuEq>, d: Nat, m: Maybe<&2, NuHole>, +st: NuSt, +cx: NuCx) -> List<&2, NuCase>:
  match cl d m:
    case e <> t d m:
      [NuCase{act.nu.st.pats(st, act.nu.cx.n(cx)), act.nu.refute.e(e, act.nu.st.ty(st, act.nu.cx.ret(cx)))}]
    case Nil{} 1n+p Some{h}:
      Nil{}
    case Nil{} d m:
      [NuCase{act.nu.st.pats(st, act.nu.cx.n(cx)), T.BtExpr{act.todo("a case nested patterns leave out that no index equation refutes")}}]

def act.nu.ref.more(cl: List<&2, NuEq>, d: Nat, m: Maybe<&2, NuHole>, row: NuP, +cx: NuCx) -> List<&2, NuRj>:
  match cl d m:
    case Nil{} 1n+p Some{NuHole{path, +dk}}:
      +env = act.nu.cx.env(cx)
      act.nu.split.rows(act.nu.sibs(env, dk), row, List.reverse(&2, Nat, path), p, env)
    case _ _ _:
      Nil{}

def act.nu.refs(fuel: Nat, js: List<&2, NuRj>, +cx: NuCx, acc: List<&2, NuCase>) -> List<&2, NuCase>:
  match fuel js:
    case 1n+f NuRj{+row, +d} <> rest:
      +st = act.nu.cx.row(cx, row)
      +cl = act.nu.u.cl(act.nu.unify(act.nu.st.eqs(st), act.nu.st.fl(st), act.nu.st.vty(st)))
      +h = act.nu.hole.pick(act.nu.st.holes(st), act.nu.cx.env(cx))
      act.nu.refs(f, List.append(&2, NuRj, act.nu.ref.more(cl, d, h, row, cx), rest), cx, List.append(&2, NuCase, acc, act.nu.ref.out(cl, d, h, st, cx)))
    case _ _:
      acc

def act.nu.rjs(ms: List<&2, NuP>, +scr: List<&2, Bool>) -> List<&2, NuRj>:
  match ms:
    case m <> rest:
      NuRj{act.nu.uncols(scr, m), 3n} <> act.nu.rjs(rest, scr)
    case Nil{}:
      Nil{}

# The def ----------------------------------------------------------------------

def act.nu.ks.of(p: NuP, +env: ActEnv) -> List<&2, String>:
  match p:
    case NuPS{NuPC{+k, ps}, t}:
      act.nu.dkey(env, k) <> act.nu.ks.of(t, env)
    case NuPS{h, t}:
      "" <> act.nu.ks.of(t, env)
    case _:
      Nil{}

def act.nu.ks.merge(a: List<&2, String>, b: List<&2, String>) -> List<&2, String>:
  match a b:
    case +x <> xs y <> ys:
      Bool.pick(String, String.eq(x, ""), y, x) <> act.nu.ks.merge(xs, ys)
    case Nil{} b:
      b
    case a Nil{}:
      a

# each parameter's data key, from the first constructor pattern there
def act.nu.ks(cls: A.Ag, +env: ActEnv) -> List<&2, String>:
  match cls:
    case A.AgCl{+tel, ps, body, ty, ca, rest}:
      act.nu.ks.merge(act.nu.ks.of(act.nu.p(ps, act.tel.len(tel), env), env), act.nu.ks(rest, env))
    case _:
      Nil{}

def act.nu.pvs(k: Nat, +hints: List<&2, List<&2, U32>>, +pnames: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match k:
    case 1n+(+p):
      act.pv.name(p, hints, pnames) <> act.nu.pvs(p, hints, pnames)
    case 0n:
      pnames

def act.nu.acc.put(ok: Bool, c: NuCase, row: NuP, acc: NuAcc) -> NuAcc:
  match acc:
    case NuAcc{o, cs, rows}:
      NuAcc{Bool.and(ok, o), List.append(&2, NuCase, cs, [c]), List.append(&2, NuP, rows, [row])}

def act.nu.cl.add(skip: Bool, +p: NuP, +n: Nat, +hints: List<&2, List<&2, U32>>, body: A.Ag, +scr: List<&2, Bool>, ents: List<&2, T.Bt>, ks: List<&2, String>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, hps: List<&2, T.BParam>, ret: T.Bt, acc: NuAcc) -> NuAcc:
  match skip:
    case True{}:
      acc
    case False{}:
      +st = act.nu.prom(act.nu.row(p, scr, ents, ks, hps, 0n, hints, pnames, act.nu.pvs(n, hints, pnames), env, act.nu.st0()))
      act.nu.acc.put(act.nu.st.ok(st), NuCase{act.nu.st.pats(st, act.nu.ncols(scr)), act.nu.clause(st, body, n, env, ret)}, act.nu.cols(p, scr), acc)

def act.nu.cases(cls: A.Ag, +scr: List<&2, Bool>, +ents: List<&2, T.Bt>, +ks: List<&2, String>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, acc: NuAcc) -> NuAcc:
  match cls:
    case A.AgCl{+tel, ps, body, ty, ca, rest}:
      +n = act.tel.len(tel)
      +p = act.nu.p(ps, n, env)
      act.nu.cases(rest, scr, ents, ks, pnames, env, hps, ret, act.nu.cl.add(Bool.or(act.nu.raw(p), act.nu.absp(p)), p, n, act.tel.hints(tel), body, scr, ents, ks, pnames, env, hps, ret, acc))
    case _:
      acc

def act.nu.chain(cs: List<&2, NuCase>) -> T.Bt:
  match cs:
    case NuCase{p, b} <> rest:
      T.BtCase{p, b, act.nu.chain(rest)}
    case Nil{}:
      T.BtCEnd{}

def act.nu.body.of(acc: NuAcc, +scr: List<&2, Bool>, +ents: List<&2, T.Bt>, ks: List<&2, String>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, hps: List<&2, T.BParam>, ret: T.Bt) -> Maybe<&2, T.Bt>:
  match acc:
    case NuAcc{True{}, cs, rows}:
      +ms = act.nu.miss(4096n, [NuMj{rows, act.nu.ncols(scr), Nil{}}], env, Nil{})
      Some{T.BtMatch{T.tba.args(act.scr.vars(scr, ents)), act.nu.chain(List.append(&2, NuCase, cs, act.nu.refs(512n, act.nu.rjs(ms, scr), NuCx{scr, ents, ks, hps, pnames, env, ret}, Nil{})))}}
    case NuAcc{False{}, cs, rows}:
      None{}

# the def's match by this path, or None when a clause cannot be written so
def act.nu.body(+cls: A.Ag, +scr: List<&2, Bool>, +ents: List<&2, T.Bt>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt) -> Maybe<&2, T.Bt>:
  +ks = act.nu.ks(cls, env)
  act.nu.body.of(act.nu.cases(cls, scr, ents, ks, pnames, env, hps, ret, NuAcc{True{}, Nil{}, Nil{}}), scr, ents, ks, pnames, env, hps, ret)


# the match the clauses make (act.cases, then the coverage passes)
def act.body.split(+scr: List<&2, Bool>, +cls: A.Ag, +ents: List<&2, T.Bt>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, +uhps: List<&2, T.BParam>) -> T.Bt:
  T.BtMatch{T.tba.args(act.scr.vars(scr, ents)), act.cv.full(act.cov.full(act.cases(cls, scr, ents, pnames, env, hps, ret, uhps), act.cov.data(act.cov.q(cls, scr), env), act.scr.vars(scr, ents), env, uhps, ret), cls, scr, act.scr.vars(scr, ents), env, uhps, ret)}

def act.body.nu2(m: Maybe<&2, T.Bt>, +scr: List<&2, Bool>, +cls: A.Ag, +ents: List<&2, T.Bt>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, +uhps: List<&2, T.BParam>) -> T.Bt:
  match m:
    case Some{b}:
      b
    case None{}:
      act.body.split(scr, cls, ents, pnames, env, hps, ret, uhps)

# a def with nested patterns of an indexed family takes act.nu's path
def act.body.nu(nu: Bool, +scr: List<&2, Bool>, +cls: A.Ag, +ents: List<&2, T.Bt>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, +uhps: List<&2, T.BParam>) -> T.Bt:
  match nu:
    case True{}:
      act.body.nu2(act.nu.body(cls, scr, ents, pnames, env, uhps, ret), scr, cls, ents, pnames, env, hps, ret, uhps)
    case False{}:
      act.body.split(scr, cls, ents, pnames, env, hps, ret, uhps)

def act.body.of(split: Bool, +scr: List<&2, Bool>, +cls: A.Ag, +ents: List<&2, T.Bt>, +pnames: List<&2, List<&2, U32>>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, +uhps: List<&2, T.BParam>) -> T.Bt:
  match split:
    case True{}:
      act.body.nu(Bool.and(act.nu.want(cls, env), Bool.not(act.nu.anybad(cls, env))), scr, cls, ents, pnames, env, hps, ret, uhps)
    case False{}:
      act.body.first(act.cases(cls, scr, ents, pnames, env, hps, ret, uhps))

def act.body.with(+scr: List<&2, Bool>, cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, +uhps: List<&2, T.BParam>) -> T.Bt:
  act.body.of(act.any(scr), scr, cls, ents, act.names(ents), env, hps, ret, uhps)


# A def's body from its clauses: one match on the parameters they split,
# in parameter order, or the one clause's body when none splits.
def act.body(+cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, +hps: List<&2, T.BParam>, +ret: T.Bt, +uhps: List<&2, T.BParam>) -> T.Bt:
  act.body.with(act.scr(cls, env), cls, ents, env, hps, ret, uhps)
# Items ------------------------------------------------------------------------

# A parameter a clause splits must be live (Bend matches erased values only
# in dead regions): the header's modes with those made live.  ms walks
# every parameter, ps only the kept ones.
def act.live.ps(ps: List<&2, T.BParam>, scr: List<&2, Bool>, ms: List<&2, ActM>) -> List<&2, T.BParam>:
  match ps scr ms:
    case ps s <> st AmDrop{} <> mt:
      act.live.ps(ps, st, mt)
    case T.BParam{T.BmErased{}, x, ty} <> pt True{} <> st m2 <> mt:
      T.BParam{T.BmLive{}, x, ty} <> act.live.ps(pt, st, mt)
    case p <> pt True{} <> st m2 <> mt:
      p <> act.live.ps(pt, st, mt)
    case p <> pt False{} <> st m2 <> mt:
      p <> act.live.ps(pt, st, mt)
    case ps _ _:
      ps

# the comment above a def: its Agda name and binding site
def act.doc(+qs: List<&2, U32>, +file: List<&2, U32>, +line: Nat) -> List<&2, List<&2, U32>>:
  [List.append(&2, U32, S.b("Agda: "), qs), S.b(S.base(S.str(file)) ++ ", line " ++ Nat.show(line))]

def act.last.of(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case h <> Nil{}:
      h
    case h <> t:
      act.last.of(t)
    case Nil{}:
      S.b("f")

def act.last.part(+n: List<&2, U32>) -> List<&2, U32>:
  act.last.of(S.split(n, 46))

def act.key.pos(+k: String, ks: List<&2, String>) -> Nat:
  match ks:
    case Nil{}:
      0n
    case h <> t:
      Bool.pick(Nat, String.eq(h, k), 0n, 1n+act.key.pos(k, t))

def act.field.var(s: ActSym) -> List<&2, U32>:
  match s:
    case ActSym{m, +n, k, ms, ar, b, fs, c, cp}:
      List.append(&2, U32, S.b("f_"), act.last.part(n))

def act.sym.key(+env: ActEnv, k: String) -> ActSym:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.sym.got(Map.get(ActSym, act.sym0(), tab, k))

# a record's fields as pattern variables: their names' last parts
def act.field.vars(ks: List<&2, String>, +env: ActEnv) -> List<&2, T.Bt>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      T.BtVar{act.field.var(act.sym.key(env, k))} <> act.field.vars(t, env)

def act.nth.t(n: Nat, xs: List<&2, T.Bt>) -> T.Bt:
  match n xs:
    case 0n h <> t:
      h
    case 1n+p h <> t:
      act.nth.t(p, t)
    case _ Nil{}:
      act.todo("a field the record does not have")

def act.last.t(xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case h <> Nil{}:
      h
    case h <> t:
      act.last.t(t)
    case Nil{}:
      act.todo("a projection with no record argument")

# A record field's projection: a match on the record (its last parameter)
# that answers the field.
def act.proj.body(r: ActSym, +env: ActEnv, +own: String, +ents: List<&2, T.Bt>) -> T.Bt:
  match r:
    case ActSym{+m, n, k, ms, ar, b, +fs, +c, cp}:
      +vs = act.field.vars(fs, env)
      T.BtMatch{T.tba.args([act.last.t(ents)]), T.BtCase{T.tba.args([T.BtCon{act.ref.of(act.is.here(env, m), env, m, c), T.tba.args(vs)}]), T.BtExpr{act.nth.t(act.key.pos(own, fs), vs)}, T.BtCEnd{}}}

def act.proj.rec(p: A.AgProj) -> Maybe<&2, A.AgQ>:
  match p:
    case A.AgPrOf{Some{r}, o, ix}:
      Some{r}
    case _:
      None{}

# Copatterns: each field's clause, its value a lambda over the patterns
# after the projection.

def act.copat.hit(ps: A.Ag, +key: String) -> Bool:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      String.eq(act.key(q), key)
    case A.AgPArg{i, x, p, rest}:
      act.copat.hit(rest, key)
    case _:
      False{}

# the patterns after the projection
def act.copat.extra(ps: A.Ag) -> A.Ag:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      rest
    case A.AgPArg{i, x, p, rest}:
      act.copat.extra(rest)
    case _:
      A.AgPEnd{}

def act.lams(xs: T.Bt, b: T.Bt) -> T.Bt:
  match xs:
    case T.BtArgs{T.BtPv{m, x}, rest}:
      T.BtLam{T.BmLive{}, x, act.lams(rest, b)}
    case T.BtArgs{p, rest}:
      act.todo("a copattern clause that matches after its projection")
    case _:
      b

def act.falses(xs: List<&2, T.Bt>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      False{} <> act.falses(t)

def act.copat.value(a: ActPat, b: ActPat, +n: Nat, body: A.Ag, +env: ActEnv) -> T.Bt:
  match a b:
    case ActPat{p, bs, x} ActPat{q, cs, y}:
      act.lams(q, act.t(act.inline(100000n, body, env), act.ctx.of(n, List.append(&2, ActBind, bs, cs)), env))

# Copattern clauses that match their parameters (`pr1 (is-equiv-comp g h
# (sh , rh) (sg , rg)) = …`): the parameters with a constructor pattern
# (not refl) are split, its variables bound in every field's value, and the
# record value sits in one case of a match on them, its pattern the first
# clause's (every field's clause must match the same way: its names come
# from the same telescope positions)
def act.copat.scr1(p: A.Ag, +env: ActEnv) -> Bool:
  match p:
    case A.AgPCon{+q, r, fo, ps}:
      Bool.not(act.is.refl(act.sym(env, q)))
    case _:
      False{}

def act.copat.scr(ps: A.Ag, ents: List<&2, T.Bt>, +env: ActEnv) -> List<&2, Bool>:
  match ps ents:
    case A.AgPArg{i, x, p, rest} e <> et:
      act.copat.scr1(p, env) <> act.copat.scr(rest, et, env)
    case _ _:
      Nil{}

def act.copat.of(+tel: A.Ag, +ps: A.Ag, body: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv) -> T.Bt:
  +n = act.tel.len(tel)
  +hints = act.tel.hints(tel)
  act.copat.value(act.top(ps, act.copat.scr(ps, ents, env), ents, n, hints, act.names(ents), env), act.pat(act.copat.extra(ps), n, hints, act.names(ents), env), n, body, env)

def act.pat.p(a: ActPat) -> T.Bt:
  match a:
    case ActPat{p, bs, ab}:
      p

def act.copat.wrap.go(any: Bool, xs: List<&2, T.Bt>, sp: T.Bt, inner: T.Bt) -> T.Bt:
  match any:
    case True{}:
      T.BtMatch{T.tba.args(xs), T.BtCase{sp, T.BtExpr{inner}, T.BtCEnd{}}}
    case False{}:
      T.BtExpr{inner}

def act.copat.wrap(cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, inner: T.Bt) -> T.Bt:
  match cls:
    case A.AgCl{+tel, +ps, body, ty, ca, rest}:
      +scr = act.copat.scr(ps, ents, env)
      act.copat.wrap.go(act.any(scr), act.scr.vars(scr, ents), act.pat.p(act.top(ps, scr, ents, act.tel.len(tel), act.tel.hints(tel), act.names(ents), env)), inner)
    case _:
      T.BtExpr{inner}

def act.copat.hit.cl(cls: A.Ag, +key: String) -> Bool:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      act.copat.hit(ps, key)
    case _:
      False{}

# hit: whether the first clause defines the field key (decided by the caller)
def act.copat.find(cls: A.Ag, +key: String, +ents: List<&2, T.Bt>, +env: ActEnv, hit: Bool) -> T.Bt:
  match cls hit:
    case A.AgCl{tel, ps, body, ty, ca, rest} True{}:
      act.copat.of(tel, ps, body, ents, env)
    case A.AgCl{tel, ps, body, ty, ca, +rest} False{}:
      act.copat.find(rest, key, ents, env, act.copat.hit.cl(rest, key))
    case _ _:
      act.todo("a field no copattern clause defines")

def act.copat.fields(ks: List<&2, String>, +cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv) -> List<&2, T.Bt>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> t:
      act.copat.find(cls, k, ents, env, act.copat.hit.cl(cls, k)) <> act.copat.fields(t, cls, ents, env)

# Nested copatterns: a record value inside a record value (unimath's
# `triple a b c = (a , b , c)`, Σ a record with eta, is elaborated as the
# clauses `.pr1 = a`, `.pr2 .pr1 = b`, `.pr2 .pr2 = c`).  A field whose
# clause has a second projection right after its own is a record value of
# the same record (the projection must be one of its fields, else a field
# is missing: the item drops), built from that field's clauses with their
# first projection taken out.  Only the same record: Σ in Σ, × and the
# definitions that unfold to Σ (section, is-equiv).
def act.copat.after.proj(ps: A.Ag) -> Bool:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, A.AgPArg{i2, x2, A.AgPProj{q2}, r2}}:
      True{}
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      False{}
    case A.AgPArg{i, x, p, rest}:
      act.copat.after.proj(rest)
    case _:
      False{}

def act.copat.nested.cl(cls: A.Ag, +key: String) -> Bool:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      Bool.pick(Bool, act.copat.hit(ps, key), act.copat.after.proj(ps), act.copat.nested.cl(rest, key))
    case _:
      False{}

def act.copat.nest.head(ks: List<&2, String>, +cls: A.Ag) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case +k <> t:
      act.copat.nested.cl(cls, k)

# the patterns without their first projection
def act.copat.strip(ps: A.Ag) -> A.Ag:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      rest
    case A.AgPArg{i, x, p, rest}:
      A.AgPArg{i, x, p, act.copat.strip(rest)}
    case p:
      p

def act.copat.sub.one(hit: Bool, tel: A.Ag, +ps: A.Ag, body: A.Ag, ty: A.Ag, ca: Bool, rest: A.Ag) -> A.Ag:
  match hit:
    case True{}:
      A.AgCl{tel, act.copat.strip(ps), body, ty, ca, rest}
    case False{}:
      rest

# the clauses of field key, its projection taken out
def act.copat.sub(cls: A.Ag, +key: String) -> A.Ag:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      act.copat.sub.one(act.copat.hit(ps, key), tel, ps, body, ty, ca, act.copat.sub(rest, key))
    case c:
      c


# the head name of a TYPE after n Pis (a copattern definition's record)
def act.cod.q(n: Nat, t: A.Ag) -> Maybe<&2, A.AgQ>:
  match n t:
    case n A.AgEl{s, x}:
      act.cod.q(n, x)
    case 1n+p A.AgPi{i, x, a, d, b}:
      act.cod.q(p, b)
    case 0n A.AgDef{q, es}:
      Some{q}
    case 0n A.AgDefX{q, es}:
      Some{q}
    case _ _:
      None{}

def act.pats.all(ps: A.Ag) -> Nat:
  match ps:
    case A.AgPArg{i, x, p, rest}:
      1n+act.pats.all(rest)
    case _:
      0n

def act.copat.is(cls: A.Ag) -> Bool:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      Bool.not(Nat.is_eq(act.pats.len(ps), act.pats.all(ps)))
    case _:
      False{}

def act.sym.is.rec(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, A.AkRecord{}, ms, ar, b, fs, c, cp}:
      True{}
    case _:
      False{}

# the head of the leaf a type-valued definition unfolds to (None when it
# does not)
def act.copat.unf.q(c: ActCopy) -> Maybe<&2, A.AgQ>:
  match c:
    case ActCopy{n, body}:
      act.cod.q(0n, body)

def act.copat.unf(+env: ActEnv, +r: A.AgQ) -> Maybe<&2, A.AgQ>:
  match env:
    case ActEnv{mod, tab, al, unf}:
      act.copat.unf.q(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(r))))

# the record a copattern definition builds: its type's head, or where that
# is a type-valued definition, the head it unfolds to, fuel times
# (agda-unimath's section f = Σ (B → A) …: section-comp's clauses are
# Σ's pr1 and pr2)
def act.copat.isrec(+env: ActEnv, m: Maybe<&2, A.AgQ>) -> Bool:
  match m:
    case Some{r}:
      act.sym.is.rec(act.sym(env, r))
    case None{}:
      True{}

def act.copat.recq(fuel: Nat, q: Maybe<&2, A.AgQ>, isrec: Bool, +env: ActEnv) -> Maybe<&2, A.AgQ>:
  match fuel q isrec:
    case 1n+f Some{+r} False{}:
      act.copat.recq(f, act.copat.unf(env, r), act.copat.isrec(env, act.copat.unf(env, r)), env)
    case _ x _:
      x


# Copattern clauses that match after their projection (agda-algebras'
# `⟨ 𝑆 ⟩ A ._≈_ (f , u) (g , v) = …`, `⟨ 𝑆 ⟩ A .isEqv .sym (≡.refl , g)
# = …`): Bend matches only a def's own parameters, never a lambda's, so
# each such field path is a helper definition (act.cop.hs, added to the
# module's declarations by Agda2Bend.bend) whose parameters are D's then
# the field's, whose clauses are D's for that path with the projections
# taken out, and whose case tree is D's below them.  Its type is D's Pis,
# then the field's type (its projection's, "fty:" in the unfoldings) at
# the record's arguments and D's own value (D applied to its parameters,
# projected along the path).  The field's value is the helper applied to
# D's parameters (act.t eta-expands it over the rest).  Only paths whose
# clauses have variables before the projection and that take two clauses,
# or a pattern other than a variable after it.
def act.fty.key(+k: String) -> String:
  "fty:" ++ k

def act.fty.of(d: A.AgDecl) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDFun{A.AgPrOf{Some{r}, o, ix}, rs, w, e, t, mu, cls, tree}}:
      Some{ActCopy{0n, ty}}
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDData{pars, ixs, cs, srt, dcl}}:
      Some{ActCopy{0n, ty}}
    case _:
      None{}

def act.copy.body(c: ActCopy) -> A.Ag:
  match c:
    case ActCopy{n, b}:
      b

# a field's projection's type, by the field's key (AgNone when unknown)
def act.fty(+unf: Map<&2, ActCopy>, +k: String) -> A.Ag:
  act.copy.body(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.fty.key(k))))

def act.fty.env(+env: ActEnv, +k: String) -> A.Ag:
  match env:
    case ActEnv{mod, tab, al, +unf}:
      act.fty(unf, k)

# the projections in a row from the first one on
def act.cop.run(ps: A.Ag) -> List<&2, A.AgQ>:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      q <> act.cop.run(rest)
    case _:
      Nil{}

def act.cop.path(ps: A.Ag) -> List<&2, A.AgQ>:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      q <> act.cop.run(rest)
    case A.AgPArg{i, x, p, rest}:
      act.cop.path(rest)
    case _:
      Nil{}

def act.cop.pstr(ks: List<&2, A.AgQ>) -> String:
  match ks:
    case Nil{}:
      ""
    case q <> t:
      "/" ++ act.key(q) ++ act.cop.pstr(t)

# the patterns after the projections
def act.cop.post1(ps: A.Ag) -> A.Ag:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      act.cop.post1(rest)
    case p:
      p

def act.cop.post(ps: A.Ag) -> A.Ag:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      act.cop.post1(rest)
    case A.AgPArg{i, x, p, rest}:
      act.cop.post(rest)
    case p:
      p

# whether the patterns before the first projection are variables
def act.cop.topv(ps: A.Ag) -> Bool:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      True{}
    case A.AgPArg{i, x, A.AgPVar{v, n, o}, rest}:
      act.cop.topv(rest)
    case _:
      False{}

def act.cop.allv(ps: A.Ag) -> Bool:
  match ps:
    case A.AgPArg{i, x, A.AgPVar{v, n, o}, rest}:
      act.cop.allv(rest)
    case A.AgPArg{i, x, p, rest}:
      False{}
    case _:
      True{}

# the clauses of a path: how many, whether every one has variables before
# its projection, whether one has another pattern after it
type ActCst is Data:
  ActCst{n: Nat, tv: Bool, nv: Bool}

def act.cop.st1(hit: Bool, +ps: A.Ag, s: ActCst) -> ActCst:
  match hit s:
    case True{} ActCst{n, tv, nv}:
      ActCst{1n+n, Bool.and(tv, act.cop.topv(ps)), Bool.or(nv, Bool.not(act.cop.allv(act.cop.post(ps))))}
    case False{} s:
      s

def act.cop.st(cls: A.Ag, +p: String) -> ActCst:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      act.cop.st1(String.eq(act.cop.pstr(act.cop.path(ps)), p), ps, act.cop.st(rest, p))
    case _:
      ActCst{0n, True{}, False{}}

def act.cop.needs.st(s: ActCst) -> Bool:
  match s:
    case ActCst{+n, tv, nv}:
      Bool.and(tv, Bool.or(Nat.is_lt(1n, n), Bool.and(Nat.is_lt(0n, n), nv)))

def act.cop.needs(+cls: A.Ag, +p: String) -> Bool:
  act.cop.needs.st(act.cop.st(cls, p))

# the helper's arguments in D: the clause's variables before the projection
def act.cop.topes(ps: A.Ag) -> A.Ag:
  match ps:
    case A.AgPArg{i, x, A.AgPVar{v, n, o}, rest}:
      A.AgEApp{i, A.AgVar{n, v, A.AgENil{}}, act.cop.topes(rest)}
    case _:
      A.AgENil{}

def act.cop.hq(+hk: String) -> A.AgQ:
  A.AgQ{S.b("a2b.cop"), S.b(hk), S.b("0")}

def act.cop.hval.top(a: ActPat, +n: Nat, +ps: A.Ag, +env: ActEnv, +hk: String) -> T.Bt:
  match a:
    case ActPat{p, bs, ab}:
      act.t(A.AgDef{act.cop.hq(hk), act.cop.topes(ps)}, act.ctx.of(n, bs), env)

def act.cop.hval.cl(+tel: A.Ag, +ps: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, +hk: String) -> T.Bt:
  +n = act.tel.len(tel)
  act.cop.hval.top(act.top(ps, act.copat.scr(ps, ents, env), ents, n, act.tel.hints(tel), act.names(ents), env), n, ps, env, hk)

def act.cop.hval(cls: A.Ag, +key: String, +ents: List<&2, T.Bt>, +env: ActEnv, +hk: String, hit: Bool) -> T.Bt:
  match cls hit:
    case A.AgCl{+tel, +ps, body, ty, ca, rest} True{}:
      act.cop.hval.cl(tel, ps, ents, env, hk)
    case A.AgCl{tel, ps, body, ty, ca, +rest} False{}:
      act.cop.hval(rest, key, ents, env, hk, act.copat.hit.cl(rest, key))
    case _ _:
      act.todo("a field no copattern clause defines")

# a field's value: the helper's call when its clauses need one
def act.copat.leaf(+cls: A.Ag, +key: String, +ents: List<&2, T.Bt>, +env: ActEnv, +dk: String, +path: String, need: Bool) -> T.Bt:
  match need:
    case True{}:
      act.cop.hval(cls, key, ents, env, dk ++ "/cop" ++ path, act.copat.hit.cl(cls, key))
    case False{}:
      act.copat.find(cls, key, ents, env, act.copat.hit.cl(cls, key))

# A nested field's record: the one its type is (the projection's, past the
# record's parameters and the record) when that is a record; else the same
# record, as before (Σ in Σ: unimath's pr2 : B pr1)
type ActNr is Data:
  ActNr{fs: List<&2, String>, c: List<&2, U32>, ar: Nat}

def act.copat.nr.sym(s: ActSym, +env: ActEnv, d: ActNr) -> ActNr:
  match s:
    case ActSym{+m, n, A.AkRecord{}, ms, ar, b, fs, +c, cp}:
      ActNr{fs, act.ref.of(act.is.here(env, m), env, m, c), ar}
    case _:
      d

def act.copat.nr.of(m: Maybe<&2, A.AgQ>, +env: ActEnv, d: ActNr) -> ActNr:
  match m:
    case Some{+q}:
      act.copat.nr.sym(act.sym(env, q), env, d)
    case None{}:
      d

def act.copat.nr.h(+h: Maybe<&2, A.AgQ>, +env: ActEnv, d: ActNr) -> ActNr:
  act.copat.nr.of(act.copat.recq(4n, h, act.copat.isrec(env, h), env), env, d)

def act.copat.nr(+env: ActEnv, +k: String, +ar: Nat, d: ActNr) -> ActNr:
  act.copat.nr.h(act.cod.q(1n+ar, act.fty.env(env, k)), env, d)

def act.nr.fs(r: ActNr) -> List<&2, String>:
  match r:
    case ActNr{fs, c, ar}:
      fs

def act.nr.c(r: ActNr) -> List<&2, U32>:
  match r:
    case ActNr{fs, c, ar}:
      c

def act.nr.ar(r: ActNr) -> Nat:
  match r:
    case ActNr{fs, c, ar}:
      ar

# The helpers themselves (Agda2Bend.bend a2b.cop.go): each path of D's
# clauses that needs one
def act.cop.has(ps: List<&2, List<&2, A.AgQ>>, +p: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(String.eq(act.cop.pstr(h), p), act.cop.has(t, p))

def act.cop.nilq(ks: List<&2, A.AgQ>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case _:
      False{}

def act.cop.add1(seen: Bool, ks: List<&2, A.AgQ>, acc: List<&2, List<&2, A.AgQ>>) -> List<&2, List<&2, A.AgQ>>:
  match seen:
    case True{}:
      acc
    case False{}:
      ks <> acc

def act.cop.paths(cls: A.Ag, +acc: List<&2, List<&2, A.AgQ>>) -> List<&2, List<&2, A.AgQ>>:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      +ks = act.cop.path(ps)
      act.cop.paths(rest, act.cop.add1(Bool.or(act.cop.nilq(ks), act.cop.has(acc, act.cop.pstr(ks))), ks, acc))
    case _:
      acc

# D's Pis (each one binding: a non-dependent one's codomain shifted), then
# the field's type along ks at D's value (self, D at its parameters)
def act.cop.abs(dep: Bool, b: A.Ag) -> A.Ag:
  match dep:
    case True{}:
      b
    case False{}:
      asb.shift(b, 1n, 0n)

def act.cop.pi(s: A.Ag, i: A.AgI, x: List<&2, U32>, a: A.Ag, m: Maybe<&2, A.Ag>) -> Maybe<&2, A.Ag>:
  match m:
    case Some{b}:
      Some{A.AgEl{s, A.AgPi{i, x, a, True{}, b}}}
    case None{}:
      None{}

type ActRa is Data:
  ActRa{q: A.AgQ, es: A.Ag}

def act.cop.rec.args(c: A.Ag) -> Maybe<&2, ActRa>:
  match c:
    case A.AgEl{s, x}:
      act.cop.rec.args(x)
    case A.AgDef{q, es}:
      Some{ActRa{q, es}}
    case _:
      None{}

def act.sym.ar(s: ActSym) -> Nat:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, cp}:
      ar

# the record's first n arguments, then self
def act.cop.vs(n: Nat, es: A.Ag, self: A.Ag) -> List<&2, A.Ag>:
  match n es:
    case 1n+p A.AgEApp{i, t, rest}:
      t <> act.cop.vs(p, rest, self)
    case _ _:
      [self]

# a closed type's first n Pis taken at vs (in order), a non-binding one's
# value dropped
def act.cop.inst(n: Nat, t: A.Ag, vs: List<&2, A.Ag>, +acc: List<&2, A.Ag>) -> A.Ag:
  match n t vs:
    case 0n t vs:
      asb.subst(t, 0n, acc, List.length(&2, A.Ag, acc))
    case 1n+p A.AgEl{s, A.AgPi{i, x, a, True{}, b}} v <> vt:
      act.cop.inst(p, b, vt, v <> acc)
    case 1n+p A.AgEl{s, A.AgPi{i, x, a, False{}, b}} v <> vt:
      act.cop.inst(p, b, vt, acc)
    case _ _ _:
      A.AgNone{}

def act.cop.step(m: Maybe<&2, ActRa>, +k: A.AgQ, +self: A.Ag, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> A.Ag:
  match m:
    case Some{ActRa{+r, es}}:
      +pars = act.sym.ar(act.sym.got(Map.get(ActSym, act.sym.none(r), tab, act.key(r))))
      act.cop.inst(1n+pars, act.fty(unf, act.key(k)), act.cop.vs(pars, es, self), Nil{})
    case None{}:
      A.AgNone{}

def act.cop.ft(fuel: Nat, ks: List<&2, A.AgQ>, c: A.Ag, +self: A.Ag, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> A.Ag:
  match fuel ks:
    case _ Nil{}:
      c
    case 1n+f +k <> rest:
      act.cop.ft(f, rest, act.cop.step(act.cop.rec.args(c), k, self, unf, tab), asb.push(self, A.AgEProj{k, A.AgENil{}}), unf, tab)
    case _ _:
      A.AgNone{}

def act.cop.some(t: A.Ag) -> Maybe<&2, A.Ag>:
  match t:
    case A.AgNone{}:
      None{}
    case t:
      Some{t}

def act.cop.hty(n: Nat, t: A.Ag, +dq: A.AgQ, +es: A.Ag, +ks: List<&2, A.AgQ>, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> Maybe<&2, A.Ag>:
  match n t:
    case 0n c:
      act.cop.some(act.inline(1024n, act.cop.ft(8n, ks, c, A.AgDef{dq, es}, unf, tab), ActEnv{Nil{}, tab, Map.new(&2, List<&2, U32>), unf}))
    case 1n+p A.AgEl{s, A.AgPi{+i, +x, a, dep, b}}:
      act.cop.pi(s, i, x, a, act.cop.hty(p, act.cop.abs(dep, b), dq, asb.elims.cat(asb.shift(es, 1n, 0n), A.AgEApp{i, A.AgVar{0n, x, A.AgENil{}}, A.AgENil{}}), ks, unf, tab))
    case _ _:
      None{}

# the helper's name: D's, then each field's last part
def act.cop.last(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case h <> Nil{}:
      h
    case h <> t:
      act.cop.last(t)
    case Nil{}:
      Nil{}

def act.cop.hname(ks: List<&2, A.AgQ>, ds: List<&2, U32>) -> List<&2, U32>:
  match ks:
    case Nil{}:
      ds
    case A.AgQ{+s, w, k} <> t:
      act.cop.hname(t, List.append(&2, U32, ds, 46 <> act.cop.last(S.split(s, 46))))

# D's case tree below the path's copattern splits
def act.cop.pick(hit: Bool, a: A.Ag, b: A.Ag) -> A.Ag:
  match hit:
    case True{}:
      a
    case False{}:
      b

def act.cop.br(bs: A.Ag, +k: String) -> A.Ag:
  match bs:
    case A.AgBr{q, n, t, rest}:
      act.cop.pick(String.eq(act.key(q), k), t, act.cop.br(rest, k))
    case _:
      A.AgNone{}

def act.cop.sub1(tr: A.Ag, +q: A.AgQ) -> A.Ag:
  match tr:
    case A.AgCase{i, n, A.AgBranches{True{}, cons, eta, lits, ca}}:
      act.cop.br(cons, act.key(q))
    case _:
      A.AgNone{}

def act.cop.subtree(ks: List<&2, A.AgQ>, tr: A.Ag) -> A.Ag:
  match ks:
    case Nil{}:
      tr
    case q <> rest:
      act.cop.subtree(rest, act.cop.sub1(tr, q))

def act.cop.ntop(ps: A.Ag) -> Nat:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      0n
    case A.AgPArg{i, x, p, rest}:
      1n+act.cop.ntop(rest)
    case _:
      0n

def act.cop.ntop.of(cls: A.Ag, +p: String) -> Nat:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      Bool.pick(Nat, String.eq(act.cop.pstr(act.cop.path(ps)), p), act.cop.ntop(ps), act.cop.ntop.of(rest, p))
    case _:
      0n

def act.cop.noproj(ps: A.Ag) -> A.Ag:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      act.cop.noproj(rest)
    case A.AgPArg{i, x, p, rest}:
      A.AgPArg{i, x, p, act.cop.noproj(rest)}
    case p:
      p

def act.cop.hcl1(hit: Bool, tel: A.Ag, +ps: A.Ag, body: A.Ag, ty: A.Ag, ca: Bool, rest: A.Ag) -> A.Ag:
  match hit:
    case True{}:
      A.AgCl{tel, act.cop.noproj(ps), body, ty, ca, rest}
    case False{}:
      rest

def act.cop.hcls(cls: A.Ag, +p: String) -> A.Ag:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      act.cop.hcl1(String.eq(act.cop.pstr(act.cop.path(ps)), p), tel, ps, body, ty, ca, act.cop.hcls(rest, p))
    case c:
      c

def act.cop.h1(m: Maybe<&2, A.Ag>, d: A.AgDecl, +ks: List<&2, A.AgQ>, +p: String) -> List<&2, A.AgDecl>:
  match m d:
    case Some{hty} A.AgDecl{+q, +qn, md, f, l, l0, l1, kd, mm, fl, lang, ty, A.AgDFun{pr, rs, wi, e, t, mu, +cls, +tree}}:
      [A.AgDecl{A.AgQ{act.cop.hname(ks, act.qs(q)), S.b(act.key(q) ++ "/cop" ++ p), S.b("0")}, act.cop.hname(ks, qn), md, f, l, l0, l1, kd, mm, Nil{}, lang, hty, A.AgDFun{A.AgPrNone{}, rs, None{}, False{}, t, mu, act.cop.hcls(cls, p), act.cop.subtree(ks, tree)}}]
    case _ _:
      Nil{}

def act.cop.hs.one(need: Bool, +ks: List<&2, A.AgQ>, +p: String, +d: A.AgDecl, +q: A.AgQ, +ty: A.Ag, +cls: A.Ag, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, A.AgDecl>:
  match need:
    case True{}:
      act.cop.h1(act.cop.hty(act.cop.ntop.of(cls, p), ty, q, A.AgENil{}, ks, unf, tab), d, ks, p)
    case False{}:
      Nil{}

def act.cop.hs.ps(ps: List<&2, List<&2, A.AgQ>>, +d: A.AgDecl, +q: A.AgQ, +ty: A.Ag, +cls: A.Ag, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, A.AgDecl>:
  match ps:
    case Nil{}:
      Nil{}
    case +ks <> rest:
      +p = act.cop.pstr(ks)
      List.append(&2, A.AgDecl, act.cop.hs.one(act.cop.needs(cls, p), ks, p, d, q, ty, cls, unf, tab), act.cop.hs.ps(rest, d, q, ty, cls, unf, tab))

def act.cop.hs.d(+d: A.AgDecl, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, A.AgDecl>:
  match d:
    case A.AgDecl{+q, qn, md, f, l, l0, l1, k, m, fl, lang, +ty, A.AgDFun{A.AgPrNone{}, rs, w, e, t, mu, +cls, tree}}:
      act.cop.hs.ps(act.cop.paths(cls, Nil{}), d, q, ty, cls, unf, tab)
    case _:
      Nil{}

def act.cop.hs(ds: List<&2, A.AgDecl>, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, A.AgDecl>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> t:
      List.append(&2, A.AgDecl, act.cop.hs.d(d, unf, tab), act.cop.hs(t, unf, tab))

# the fields' values (ks the ones left, fs all of the record's, cref its
# constructor; nest: whether ks's first is a nested record value)
def act.copat.vals(fuel: Nat, ks: List<&2, String>, +fs: List<&2, String>, +cref: List<&2, U32>, +cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, nest: Bool, +ar: Nat, +dk: String, +pre: String) -> List<&2, T.Bt>:
  match fuel ks nest:
    case _ Nil{} _:
      Nil{}
    case 1n+(+f) +k <> +t True{}:
      +sub = act.copat.sub(cls, k)
      +nr = act.copat.nr(env, k, ar, ActNr{fs, cref, ar})
      +fs2 = act.nr.fs(nr)
      +c2 = act.nr.c(nr)
      T.BtCon{c2, T.tba.args(act.copat.vals(f, fs2, fs2, c2, sub, ents, env, act.copat.nest.head(fs2, sub), act.nr.ar(nr), dk, pre ++ "/" ++ k))} <> act.copat.vals(1n+f, t, fs, cref, cls, ents, env, act.copat.nest.head(t, cls), ar, dk, pre)
    case +fuel +k <> +t _:
      act.copat.leaf(cls, k, ents, env, dk, pre ++ "/" ++ k, act.cop.needs(cls, "/" ++ k)) <> act.copat.vals(fuel, t, fs, cref, cls, ents, env, act.copat.nest.head(t, cls), ar, dk, pre)

# Copattern clauses that split differently field by field (the stdlib's
# Decidable map′: `does (map′ f g a?) = does a?`, then `proof (map′ f g
# (true because [a])) = …` and `proof (… (false because [¬a])) = …`): the
# first clause splits nothing, a later one does.  The record value sits in
# a match on the parameters the first splitting field's clauses split, a
# case for each of them; the other fields' (unsplit) clauses are read at
# the case's patterns (the split parameters substituted by them).
def act.copat.key(ps: A.Ag) -> String:
  match ps:
    case A.AgPArg{i, x, A.AgPProj{q}, rest}:
      act.key(q)
    case A.AgPArg{i, x, p, rest}:
      act.copat.key(rest)
    case _:
      ""

def act.copat.split.cl(cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv) -> Bool:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      act.any(act.copat.scr(ps, ents, env))
    case _:
      False{}

# the field of the first clause that splits a parameter ("" when none does)
def act.copat.split.key(cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv) -> String:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      Bool.pick(String, act.any(act.copat.scr(ps, ents, env)), act.copat.key(ps), act.copat.split.key(rest, ents, env))
    case _:
      ""

def act.bools.or(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case x <> at y <> bt:
      Bool.or(x, y) <> act.bools.or(at, bt)
    case Nil{} b:
      b
    case a _:
      a

# the parameters field k's clauses split, together
def act.copat.scr.k(cls: A.Ag, +k: String, +ents: List<&2, T.Bt>, +env: ActEnv) -> List<&2, Bool>:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      act.bools.or(Bool.pick(List<&2, Bool>, String.eq(act.copat.key(ps), k), act.copat.scr(ps, ents, env), Nil{}), act.copat.scr.k(rest, k, ents, env))
    case _:
      Nil{}

def act.copat.kcl.put(hit: Bool, c: A.Ag, rest: List<&2, A.Ag>) -> List<&2, A.Ag>:
  match hit:
    case True{}:
      c <> rest
    case False{}:
      rest

# field k's clauses, each alone
def act.copat.kcls(cls: A.Ag, +k: String) -> List<&2, A.Ag>:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      act.copat.kcl.put(String.eq(act.copat.key(ps), k), A.AgCl{tel, ps, body, ty, ca, A.AgNone{}}, act.copat.kcls(rest, k))
    case _:
      Nil{}

def act.copat.only.one(keep: Bool, tel: A.Ag, ps: A.Ag, body: A.Ag, ty: A.Ag, ca: Bool, rest: A.Ag) -> A.Ag:
  match keep:
    case True{}:
      A.AgCl{tel, ps, body, ty, ca, rest}
    case False{}:
      rest

# the clauses with field k's j-th (from 0) the only one of k's
def act.copat.only(cls: A.Ag, +k: String, +j: Nat, +at: Nat) -> A.Ag:
  match cls:
    case A.AgCl{tel, +ps, body, ty, ca, rest}:
      +isk = String.eq(act.copat.key(ps), k)
      act.copat.only.one(Bool.or(Bool.not(isk), Nat.is_eq(j, at)), tel, ps, body, ty, ca, act.copat.only(rest, k, j, Bool.pick(Nat, isk, 1n+at, at)))
    case c:
      c

# t with each split parameter replaced by its pattern (as a term)
def act.copat.substs(xs: List<&2, T.Bt>, sp: T.Bt, t: T.Bt) -> T.Bt:
  match xs sp:
    case x <> xt T.BtArgs{p, rest}:
      act.copat.substs(xt, rest, T.tba.subst(t, act.var.name(x), act.pat.term(p)))
    case _ _:
      t

def act.copat.recval(+cref: List<&2, U32>, +fs: List<&2, String>, +ar: Nat, +cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, +dk: String) -> T.Bt:
  T.BtCon{cref, T.tba.args(act.copat.vals(8n, fs, fs, cref, cls, ents, env, act.copat.nest.head(fs, cls), ar, dk, ""))}

def act.copat.case1(c: A.Ag, cls: A.Ag, +scr: List<&2, Bool>, +cref: List<&2, U32>, +fs: List<&2, String>, +ar: Nat, +ents: List<&2, T.Bt>, +env: ActEnv, +dk: String, rest: T.Bt) -> T.Bt:
  match c:
    case A.AgCl{+tel, +ps, body, ty, ca, r}:
      +sp = act.pat.p(act.top(ps, scr, ents, act.tel.len(tel), act.tel.hints(tel), act.names(ents), env))
      T.BtCase{sp, T.BtExpr{act.copat.substs(act.scr.vars(scr, ents), sp, act.copat.recval(cref, fs, ar, cls, ents, env, dk))}, rest}
    case _:
      rest

def act.copat.cases(kc: List<&2, A.Ag>, +j: Nat, +all: A.Ag, +k: String, +scr: List<&2, Bool>, +cref: List<&2, U32>, +fs: List<&2, String>, +ar: Nat, +ents: List<&2, T.Bt>, +env: ActEnv, +dk: String) -> T.Bt:
  match kc:
    case Nil{}:
      T.BtCEnd{}
    case c <> t:
      act.copat.case1(c, act.copat.only(all, k, j, 0n), scr, cref, fs, ar, ents, env, dk, act.copat.cases(t, 1n+j, all, k, scr, cref, fs, ar, ents, env, dk))

def act.copat.rec.go(split: Bool, +k: String, +cref: List<&2, U32>, +fs: List<&2, String>, +ar: Nat, +cls: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, +dk: String) -> T.Bt:
  match split:
    case False{}:
      act.copat.wrap(cls, ents, env, act.copat.recval(cref, fs, ar, cls, ents, env, dk))
    case True{}:
      +scr = act.copat.scr.k(cls, k, ents, env)
      T.BtMatch{T.tba.args(act.scr.vars(scr, ents)), act.copat.cases(act.copat.kcls(cls, k), 0n, cls, k, scr, cref, fs, ar, ents, env, dk)}

def act.copat.rec(r: ActSym, +env: ActEnv, +cls: A.Ag, +ents: List<&2, T.Bt>, +dk: String) -> T.Bt:
  match r:
    case ActSym{+m, n, A.AkRecord{}, ms, +ar, b, +fs, +c, cp}:
      +k = act.copat.split.key(cls, ents, env)
      act.copat.rec.go(Bool.and(Bool.not(act.copat.split.cl(cls, ents, env)), Bool.not(String.eq(k, ""))), k, act.ref.of(act.is.here(env, m), env, m, c), fs, ar, cls, ents, env, dk)
    case _:
      T.BtExpr{act.todo("copattern clauses whose type is not a record")}

def act.copat.body(q: Maybe<&2, A.AgQ>, +env: ActEnv, +cls: A.Ag, +ents: List<&2, T.Bt>, +dk: String) -> T.Bt:
  match q:
    case Some{r}:
      act.copat.rec(act.sym(env, r), env, cls, ents, dk)
    case None{}:
      T.BtExpr{act.todo("copattern clauses whose type is not a record")}

def act.ps.ents(r: ActPs) -> List<&2, T.Bt>:
  match r:
    case ActPs{ps, ret, ctx, es, ok}:
      es

# a function: its header from its type, its body from its clauses (or, for
# a record field, a match on the record; for copattern clauses, the
# record's constructor)
# the kept (not dropped) parameters among the first n
def act.kept.n(n: Nat, ms: List<&2, ActM>) -> Nat:
  match n ms:
    case 1n+p AmDrop{} <> t:
      act.kept.n(p, t)
    case 1n+p m <> t:
      1n+act.kept.n(p, t)
    case _ _:
      0n

def act.bp.names(ps: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      x <> act.bp.names(t)

def act.mem.name(+n: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(S.eq(h, n), act.mem.name(n, t))

# a body (match, cases, rewrites, lets, expressions) with the variable n
# renamed n2, a case or let binding n shadowing it
def act.sub.deep(t: T.Bt, +n: List<&2, U32>, +n2: List<&2, U32>) -> T.Bt:
  match t:
    case T.BtExpr{e}:
      T.BtExpr{T.tba.subst(e, n, T.BtVar{n2})}
    case T.BtMatch{xs, cs}:
      T.BtMatch{T.tba.subst(xs, n, T.BtVar{n2}), act.sub.deep(cs, n, n2)}
    case T.BtCase{+p, +b, rest}:
      T.BtCase{p, Bool.pick(T.Bt, act.mem.name(n, T.tba.pvars(p, Nil{})), b, act.sub.deep(b, n, n2)), act.sub.deep(rest, n, n2)}
    case T.BtRw{e, p, b}:
      T.BtRw{T.tba.subst(e, n, T.BtVar{n2}), T.tba.subst(p, n, T.BtVar{n2}), act.sub.deep(b, n, n2)}
    case T.BtLet{+y, v, +b}:
      T.BtLet{y, T.tba.subst(v, n, T.BtVar{n2}), Bool.pick(T.Bt, S.eq(y, n), b, act.sub.deep(b, n, n2))}
    case t:
      T.tba.subst(t, n, T.BtVar{n2})

# a case pattern with its variable n renamed n2
def act.alpha.pat(p: T.Bt, +n: List<&2, U32>, +n2: List<&2, U32>) -> T.Bt:
  match p:
    case T.BtVar{+y}:
      Bool.pick(T.Bt, S.eq(y, n), T.BtVar{n2}, T.BtVar{y})
    case T.BtPv{+m, +y}:
      Bool.pick(T.Bt, S.eq(y, n), T.BtPv{m, n2}, T.BtPv{m, y})
    case T.BtCon{c, a}:
      T.BtCon{c, act.alpha.pat(a, n, n2)}
    case T.BtArgs{a, rest}:
      T.BtArgs{act.alpha.pat(a, n, n2), act.alpha.pat(rest, n, n2)}
    case T.BtSucc{a}:
      T.BtSucc{act.alpha.pat(a, n, n2)}
    case p:
      p

# t with each binder named n (a lambda's, a Pi's, a let's, a case's
# pattern variable) renamed n2 in its scope; a free n, the lifted
# parameter itself, stays
def act.alpha(t: T.Bt, +n: List<&2, U32>, +n2: List<&2, U32>) -> T.Bt:
  match t:
    case T.BtLam{+m, +y, b}:
      +b2 = act.alpha(b, n, n2)
      Bool.pick(T.Bt, S.eq(y, n), T.BtLam{m, n2, T.tba.subst(b2, n, T.BtVar{n2})}, T.BtLam{m, y, b2})
    case T.BtPi{+m, +y, +d, +a, b}:
      +b2 = act.alpha(b, n, n2)
      +a2 = act.alpha(a, n, n2)
      Bool.pick(T.Bt, S.eq(y, n), T.BtPi{m, n2, d, a2, T.tba.subst(b2, n, T.BtVar{n2})}, T.BtPi{m, y, d, a2, b2})
    case T.BtLet{+y, +v, b}:
      +b2 = act.alpha(b, n, n2)
      +v2 = act.alpha(v, n, n2)
      Bool.pick(T.Bt, S.eq(y, n), T.BtLet{n2, v2, T.tba.subst(b2, n, T.BtVar{n2})}, T.BtLet{y, v2, b2})
    case T.BtCase{+p, b, +rest}:
      +b2 = act.alpha(b, n, n2)
      +r2 = act.alpha(rest, n, n2)
      Bool.pick(T.Bt, act.mem.name(n, T.tba.pvars(p, Nil{})), T.BtCase{act.alpha.pat(p, n, n2), act.sub.deep(b2, n, n2), r2}, T.BtCase{p, b2, r2})
    case T.BtApp{f, a}:
      T.BtApp{act.alpha(f, n, n2), act.alpha(a, n, n2)}
    case T.BtArgs{a, rest}:
      T.BtArgs{act.alpha(a, n, n2), act.alpha(rest, n, n2)}
    case T.BtTplArg{a}:
      T.BtTplArg{act.alpha(a, n, n2)}
    case T.BtCon{c, a}:
      T.BtCon{c, act.alpha(a, n, n2)}
    case T.BtTyApp{c, a}:
      T.BtTyApp{c, act.alpha(a, n, n2)}
    case T.BtEq{ty, a, b}:
      T.BtEq{act.alpha(ty, n, n2), act.alpha(a, n, n2), act.alpha(b, n, n2)}
    case T.BtSucc{a}:
      T.BtSucc{act.alpha(a, n, n2)}
    case T.BtAnn{a, ty}:
      T.BtAnn{act.alpha(a, n, n2), act.alpha(ty, n, n2)}
    case T.BtDead{a}:
      T.BtDead{act.alpha(a, n, n2)}
    case T.BtRw{e, p, b}:
      T.BtRw{act.alpha(e, n, n2), act.alpha(p, n, n2), act.alpha(b, n, n2)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{act.alpha(xs, n, n2), act.alpha(cs, n, n2)}
    case T.BtExpr{e}:
      T.BtExpr{act.alpha(e, n, n2)}
    case t:
      t

# a body applied to one more parameter, n: a head lambda takes it (in each
# case of a match, under a rewrite or a let), else the value is applied, an
# erased parameter (dead: m) in a dead place so Copy does not raise it
def act.lift.arg(m: T.BMode, +n: List<&2, U32>) -> T.Bt:
  match m:
    case T.BmErased{}:
      T.BtDead{T.BtVar{n}}
    case _:
      T.BtVar{n}

# an impossible case's Empty.absurd is at the goal the header has after the
# lift already (`invertⁿ : Reflects A false → ¬ A`, its ofʸ case refuted
# at ⊥ under x_3), so it takes no argument (2026-10-29)
def act.lift.absurd(+e: T.Bt) -> Bool:
  match e:
    case T.BtApp{T.BtVar{+f}, a}:
      S.eq(f, S.b("Empty.absurd"))
    case _:
      False{}

def act.lift.one(b: T.Bt, +m: T.BMode, +n: List<&2, U32>) -> T.Bt:
  match b:
    case T.BtExpr{T.BtLam{lm, x, e}}:
      T.BtExpr{T.tba.subst(e, x, T.BtVar{n})}
    case T.BtExpr{+e}:
      Bool.pick(T.Bt, act.lift.absurd(e), T.BtExpr{e}, T.BtExpr{T.BtApp{e, T.BtArgs{act.lift.arg(m, n), T.BtANil{}}}})
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, act.lift.one(cs, m, n)}
    case T.BtCase{p, cb, rest}:
      T.BtCase{p, act.lift.one(cb, m, n), act.lift.one(rest, m, n)}
    case T.BtRw{e, p, rb}:
      T.BtRw{e, p, act.lift.one(rb, m, n)}
    case T.BtLet{x, v, rb}:
      T.BtLet{x, v, act.lift.one(rb, m, n)}
    case b:
      b

# (a binder in the body named like n is renamed first, so n is not captured)
def act.lift.app(ps: List<&2, T.BParam>, b: T.Bt) -> T.Bt:
  match ps:
    case Nil{}:
      b
    case T.BParam{m, +n, ty} <> t:
      act.lift.app(t, act.lift.one(act.alpha(b, n, List.append(&2, U32, n, S.b("_b"))), m, n))

# Forced patterns at live parameters (`≤-trans {o = suc o} (s≤s p) (s≤s
# {n} {o} q)`, o kept for z≤n's field): Ast.bend's unforce bound o at the
# constructor's field and left the parameter unsplit, so the recursive
# call passes the field, which does not shrink the parameter (Bend's
# termination check refuses it).  At a live parameter whose pattern is the
# unforced `.(suc v)`, the split goes back to the parameter (1n+v) and the
# field is the dot again (act.sd proves it equal and casts the fields
# after it; act.cv refutes the 0n rows).
type ActRf is Data:
  ActRf{q: A.AgQ, i: A.AgI, k: Nat, x: List<&2, U32>}

def act.rf.cand(p: A.Ag) -> Maybe<&2, ActRf>:
  match p:
    case A.AgPDot{A.AgCon{+q, A.AkSystem{}, A.AgEApp{i, A.AgVar{k, x, A.AgENil{}}, A.AgENil{}}}}:
      Bool.pick(Maybe<&2, ActRf>, act.ix.is.suc(act.builtin(act.qs(q))), Some{ActRf{q, i, k, x}}, None{})
    case _:
      None{}

def act.rf.has(+k: Nat, ks: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case j <> t:
      Bool.or(Nat.is_eq(j, k), act.rf.has(k, t))

def act.rf.bound(p: A.Ag, +k: Nat) -> Bool:
  match p:
    case A.AgPArg{i, x, q, rest}:
      Bool.or(act.rf.bound(q, k), act.rf.bound(rest, k))
    case A.AgPVar{x, +n, o}:
      Nat.is_eq(n, k)
    case A.AgPCon{q, r, f, ps}:
      act.rf.bound(ps, k)
    case _:
      False{}

def act.rf.k(m: Maybe<&2, ActRf>, +ps: A.Ag) -> List<&2, Nat>:
  match m:
    case Some{ActRf{q, i, +k, x}}:
      Bool.pick(List<&2, Nat>, act.rf.bound(ps, k), [k], Nil{})
    case None{}:
      Nil{}

def act.rf.ks(p: A.Ag, live: List<&2, Bool>, +ps: A.Ag) -> List<&2, Nat>:
  match p live:
    case A.AgPArg{i, x, q, rest} True{} <> lt:
      List.append(&2, Nat, act.rf.k(act.rf.cand(q), ps), act.rf.ks(rest, lt, ps))
    case A.AgPArg{i, x, q, rest} b <> lt:
      act.rf.ks(rest, lt, ps)
    case _ _:
      Nil{}

def act.rf.dot(p: A.Ag, +ks: List<&2, Nat>) -> A.Ag:
  match p:
    case A.AgPArg{i, x, q, rest}:
      A.AgPArg{i, x, act.rf.dot(q, ks), act.rf.dot(rest, ks)}
    case A.AgPVar{+x, +n, o}:
      Bool.pick(A.Ag, act.rf.has(n, ks), A.AgPDot{A.AgVar{n, x, A.AgENil{}}}, A.AgPVar{x, n, o})
    case A.AgPCon{q, r, f, ps}:
      A.AgPCon{q, r, f, act.rf.dot(ps, ks)}
    case p:
      p

def act.rf.put(m: Maybe<&2, ActRf>, +ks: List<&2, Nat>, p: A.Ag) -> A.Ag:
  match m:
    case Some{ActRf{q, i, +k, +x}}:
      Bool.pick(A.Ag, act.rf.has(k, ks), A.AgPCon{q, False{}, True{}, A.AgPArg{i, x, A.AgPVar{x, k, A.AkSystem{}}, A.AgPEnd{}}}, p)
    case None{}:
      p

def act.rf.set(p: A.Ag, live: List<&2, Bool>, +ks: List<&2, Nat>) -> A.Ag:
  match p live:
    case A.AgPArg{i, x, +q, rest} True{} <> lt:
      A.AgPArg{i, x, act.rf.put(act.rf.cand(q), ks, q), act.rf.set(rest, lt, ks)}
    case A.AgPArg{i, x, q, rest} b <> lt:
      A.AgPArg{i, x, q, act.rf.set(rest, lt, ks)}
    case p _:
      p

def act.rf.ps(+ps: A.Ag, +live: List<&2, Bool>) -> A.Ag:
  +ks = act.rf.ks(ps, live, ps)
  act.rf.set(act.rf.dot(ps, ks), live, ks)

def act.rf.cls(cls: A.Ag, +live: List<&2, Bool>) -> A.Ag:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      A.AgCl{tel, act.rf.ps(ps, live), body, ty, ca, act.rf.cls(rest, live)}
    case c:
      c

# whether each parameter (ms: all of them; ps: the kept ones) is live
def act.rf.live(ms: List<&2, ActM>, ps: List<&2, T.BParam>) -> List<&2, Bool>:
  match ms ps:
    case AmDrop{} <> mt ps:
      False{} <> act.rf.live(mt, ps)
    case m <> mt T.BParam{T.BmErased{}, x, ty} <> pt:
      False{} <> act.rf.live(mt, pt)
    case m <> mt p <> pt:
      True{} <> act.rf.live(mt, pt)
    case _ _:
      Nil{}

# The header's parameters with each split one's type opened (`x : m < n`
# is `suc m ≤ n`: the indices the coverage, the dotted fields and the
# refutations read are le's, not _<_'s arguments); the others as the
# header has them.  Same names as act.params.
def act.uty.open2(u: A.Ag, s: A.Ag, a: A.Ag, +env: ActEnv) -> A.Ag:
  match u:
    case A.AgNone{}:
      a
    case u:
      A.AgEl{s, act.inline(1024n, u, env)}

# a type-valued definition at the head opened (up to fuel times)
def act.uty.open(fuel: Nat, a: A.Ag, +env: ActEnv) -> A.Ag:
  match fuel a:
    case 1n+f A.AgEl{+s, A.AgDef{+q, +es}}:
      act.uty.open(f, act.uty.open2(act.unfold(env, q, es), s, A.AgEl{s, A.AgDef{q, es}}, env), env)
    case _ a:
      a

def act.uty.ty(sc: Bool, +a: A.Ag, +ctx: List<&2, T.Bt>, +env: ActEnv) -> T.Bt:
  match sc:
    case True{}:
      act.t(act.inline(100000n, act.uty.open(4n, a, env), env), ctx, env)
    case False{}:
      act.t(a, ctx, env)

def act.uty.put(m: ActM, +nm: List<&2, U32>, ty: T.Bt, rest: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match m:
    case AmDrop{}:
      rest
    case m:
      T.BParam{act.bmode(m), nm, ty} <> rest

def act.uty.go(fuel: Nat, n: Nat, t: A.Ag, ms: List<&2, ActM>, scr: List<&2, Bool>, +ctx: List<&2, T.Bt>, +seen: List<&2, List<&2, U32>>, +env: ActEnv) -> List<&2, T.BParam>:
  match fuel n t ms scr:
    case f 0n t ms sc:
      Nil{}
    case f 1n+p A.AgEl{s, A.AgPi{i, +x, +a, d, b}} +m <> mt sc <> st:
      +nm = act.fresh.in(x, ctx, seen)
      act.uty.put(m, nm, act.uty.ty(sc, a, ctx, env), act.uty.go(f, p, b, mt, st, act.bind(d, act.entry(m, nm), ctx), nm <> seen, env))
    case f 1n+p A.AgEl{s, A.AgPi{i, +x, +a, +d, b}} Nil{} sc <> st:
      +nm = act.fresh.in(x, ctx, seen)
      +m = act.mode(i, a, act.opaque.env(d, a, env))
      act.uty.put(m, nm, act.uty.ty(sc, a, ctx, env), act.uty.go(f, p, b, Nil{}, st, act.bind(d, act.entry(m, nm), ctx), nm <> seen, env))
    case 1n+g 1n+p A.AgEl{s, A.AgDef{+q, +es}} ms scr:
      act.uty.go(g, 1n+p, A.AgEl{s, act.inline(1024n, act.unfold(env, q, es), env)}, ms, scr, ctx, seen, env)
    case _ _ _ _ _:
      Nil{}

def act.fun.body(p: A.AgProj, +cls: A.Ag, +key: String, +ar: Nat, +t: A.Ag, +ents: List<&2, T.Bt>, +env: ActEnv, copat: Bool, +r: ActPs, +ms: List<&2, ActM>) -> T.Bt:
  match p copat:
    case A.AgPrOf{Some{r}, o, ix} _:
      act.proj.body(act.sym(env, r), env, key, ents)
    case _ True{}:
      act.copat.body(act.copat.recq(4n, act.cod.q(ar, t), act.copat.isrec(env, act.cod.q(ar, t)), env), env, cls, ents, key)
    case _ False{}:
      +cls2 = act.rf.cls(cls, act.rf.live(ms, act.ps.ps(r)))
      act.lift.app(List.drop(&2, T.BParam, act.ps.ps(r), act.kept.n(act.cls.arity(cls), ms)), act.body(cls2, ents, env, act.ps.ps(r), act.ps.ret(r), act.uty.go(64n, ar, t, ms, act.scr(cls2, env), Nil{}, Nil{}, env)))

def act.fun.item(+nm: List<&2, U32>, +ms: List<&2, ActM>, +cls: A.Ag, body: T.Bt, r: ActPs, doc: List<&2, List<&2, U32>>, +env: ActEnv) -> List<&2, T.BItem>:
  match r:
    case ActPs{ps, ret, ctx, es, ok}:
      [T.BiDef{nm, act.live.ps(ps, act.or.lists(act.scr(cls, env), act.abs.pos(cls)), ms), ret, body, doc}]

def act.fun.with(+nm: List<&2, U32>, +ms: List<&2, ActM>, +ar: Nat, p: A.AgProj, +cls: A.Ag, +key: String, +t: A.Ag, +env: ActEnv, doc: List<&2, List<&2, U32>>, +r: ActPs) -> List<&2, T.BItem>:
  act.fun.item(nm, ms, cls, act.fun.body(p, cls, key, ar, t, act.ps.ents(r), act.cmb.env(key, env), act.copat.is(cls), r, ms), r, doc, env)

# Sorts by place (with quantities on): Kind(q) is a requirement in Bend (every
# value copyable at q), where Agda's Set ℓ is only a bound, so a definition
# keeps Type (`¬ A = A → ⊥` is a function type at any level). Kind(q) stays
# where kinds are declared: data and record parameters, field types (with
# type-valued definitions opened, so that Category's `_⇒_ : Rel Obj ℓ` shows
# Kind(l)) and the projections that read them.
def act.unkind(t: T.Bt) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+k}, +a}:
      Bool.pick(T.Bt, S.eq(k, S.b("Kind")), T.BtType{}, T.BtApp{T.BtVar{k}, act.unkind(a)})
    case T.BtApp{f, a}:
      T.BtApp{act.unkind(f), act.unkind(a)}
    case T.BtArgs{a, rest}:
      T.BtArgs{act.unkind(a), act.unkind(rest)}
    case T.BtTplArg{a}:
      T.BtTplArg{act.unkind(a)}
    case T.BtLam{m, y, b}:
      T.BtLam{m, y, act.unkind(b)}
    case T.BtPi{m, y, d, a, b}:
      T.BtPi{m, y, d, act.unkind(a), act.unkind(b)}
    case T.BtCon{c, a}:
      T.BtCon{c, act.unkind(a)}
    case T.BtTyApp{c, a}:
      T.BtTyApp{c, act.unkind(a)}
    case T.BtEq{ty, a, b}:
      T.BtEq{act.unkind(ty), act.unkind(a), act.unkind(b)}
    case T.BtSucc{a}:
      T.BtSucc{act.unkind(a)}
    case T.BtAnn{a, ty}:
      T.BtAnn{act.unkind(a), act.unkind(ty)}
    case T.BtDead{a}:
      T.BtDead{act.unkind(a)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{act.unkind(xs), act.unkind(cs)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, act.unkind(b), act.unkind(rest)}
    case T.BtExpr{e}:
      T.BtExpr{act.unkind(e)}
    case T.BtRw{e, p, b}:
      T.BtRw{act.unkind(e), act.unkind(p), act.unkind(b)}
    case T.BtLet{y, v, b}:
      T.BtLet{y, act.unkind(v), act.unkind(b)}
    case t:
      t

def act.unkind.ps(ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      T.BParam{m, x, act.unkind(ty)} <> act.unkind.ps(t)

def act.unkind.its(its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, ret, body, doc} <> t:
      T.BiDef{n, act.unkind.ps(ps), act.unkind(ret), act.unkind(body), doc} <> act.unkind.its(t)
    case it <> t:
      it <> act.unkind.its(t)

# a type's end (past its Pis) as Type when it is a kind
def act.unkind.end(t: T.Bt) -> T.Bt:
  match t:
    case T.BtPi{m, y, d, a, b}:
      T.BtPi{m, y, d, a, act.unkind.end(b)}
    case T.BtApp{T.BtVar{+k}, +a}:
      Bool.pick(T.Bt, S.eq(k, S.b("Kind")), T.BtType{}, T.BtApp{T.BtVar{k}, a})
    case t:
      t

# a type-valued definition (`_×_`, Rel, `¬_`) keeps its parameters' and body's
# kinds, so `A × B` is as copyable as Σ A B, and only its own sort is Type
# (2026-10-21: one with an expression body keeps its sort, and Qfix's
# tqf.ret.kind keeps it when the body is of that kind)
def act.unkind.ret(its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, ret, T.BtExpr{b}, doc} <> t:
      T.BiDef{n, ps, ret, T.BtExpr{b}, doc} <> act.unkind.ret(t)
    case T.BiDef{n, ps, ret, body, doc} <> t:
      T.BiDef{n, ps, act.unkind.end(ret), body, doc} <> act.unkind.ret(t)
    case it <> t:
      it <> act.unkind.ret(t)

# a proper projection keeps its kinds; any other function has Type
def act.unkind.if(p: A.AgProj, its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match p:
    case A.AgPrOf{Some{r}, o, ix}:
      its
    case _:
      act.unkind.its(its)

# a field's or a projection's type with the type-valued definitions it ends
# in opened (Rel Obj ℓ is Obj → Obj → Set ℓ)
# (only with quantities on; tl: the definition is type-valued)
# (2026-10-20: a proper projection keeps its kinds even when it is
# type-valued: `Setoid.Carrier` is a Kind(c), the field's own kind, so the
# quantity of `IsEquivalence Carrier _≈_` is c, not the &1 of a Type)
# (2026-10-21: whether a value definition's kinds become Type.  They did
# so that a caller could pass a function type for `A : Set a`, before Qfix
# solved each call's quantities; with it on, `isYes : Dec<&1, A>` met
# `True_`'s `Dec<a, A>`)
def act.unkind.vals() -> Bool:
  False{}

def act.unkind.val(on: Bool, its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match on:
    case True{}:
      act.unkind.its(its)
    case False{}:
      its

def act.unkind.np(tl: Bool, its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match tl:
    case True{}:
      act.unkind.ret(its)
    case False{}:
      act.unkind.val(act.unkind.vals(), its)

def act.unkind.when(on: Bool, p: A.AgProj, tl: Bool, its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match on p:
    case True{} A.AgPrOf{Some{r}, o, ix}:
      its
    case True{} _:
      act.unkind.np(tl, its)
    case False{} _:
      its

def act.unfold.wrap(+s: A.Ag, u: A.Ag, +t: A.Ag, +env: ActEnv) -> A.Ag:
  match u:
    case A.AgNone{}:
      t
    case u:
      A.AgEl{s, act.inline(1024n, u, env)}

def act.unfold.sorts(fuel: Nat, t: A.Ag, +env: ActEnv) -> A.Ag:
  match fuel t:
    case 1n+f A.AgEl{+s, A.AgDef{+q, +es}}:
      act.unfold.sorts(f, act.unfold.wrap(s, act.unfold(env, q, es), A.AgEl{s, A.AgDef{q, es}}, env), env)
    case 1n+f A.AgEl{+s, A.AgDefX{+q, +es}}:
      act.unfold.sorts(f, act.unfold.wrap(s, act.unfold(env, q, es), A.AgEl{s, A.AgDefX{q, es}}, env), env)
    case 1n+f A.AgEl{s, A.AgPi{i, x, a, d, b}}:
      A.AgEl{s, A.AgPi{i, x, a, d, act.unfold.sorts(f, b, env)}}
    case f t:
      t
def act.field.sorts(on: Bool, t: A.Ag, +env: ActEnv) -> A.Ag:
  match on:
    case True{}:
      act.unfold.sorts(8n, t, env)
    case False{}:
      t

def act.proj.sorts(on: Bool, p: A.AgProj, t: A.Ag, +env: ActEnv) -> A.Ag:
  match on p:
    case True{} A.AgPrOf{Some{r}, o, ix}:
      act.unfold.sorts(8n, t, env)
    case _ _:
      t

# type-valuedness inside an item: a projection's by its own type, another
# function's once its type-valued ends are opened (as act.tylevel)
def act.tylevel.env(p: A.AgProj, +ty: A.Ag, +env: ActEnv) -> Bool:
  match p env:
    case A.AgPrOf{Some{r}, o, ix} e:
      act.ends.sort(ty)
    case _ ActEnv{mod, tab, al, +unf}:
      act.ends.sort.u(8n, ty, unf)

def act.item.fun(s: ActSym, d: A.AgD, +key: String, +ty: A.Ag, +env: ActEnv, doc: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match s d:
    case ActSym{m, +n, k, +ms, +ar, b, fs, c, cp} A.AgDFun{+p, r, w, e, te, mu, +cls, tree}:
      +t = act.proj.sorts(act.quant.on(), p, act.inline.hdr(100000n, ty, env), env)
      act.unkind.when(act.quant.on(), p, act.tylevel.env(p, ty, env), act.fun.with(n, ms, ar, p, cls, key, t, env, doc, act.params.s(64n, ar, t, ms, Nil{}, act.sig.with(w, p, env), env)))
    case _ _:
      Nil{}

# A record: its non-level parameters (erased) and its fields, each field's
# type in the scope of the parameters and the earlier fields, from the
# telescope Agda keeps of both.
type ActRt is Data:
  ActRt{ps: List<&2, T.BParam>, fs: List<&2, T.BField>}

def act.rt.param(m: ActM, +nm: List<&2, U32>, ty: T.Bt, r: ActRt) -> ActRt:
  match m r:
    case AmDrop{} r:
      r
    case m ActRt{ps, fs}:
      ActRt{T.BParam{T.BmErased{}, nm, ty} <> ps, fs}

def act.rt.field(+nm: List<&2, U32>, ty: T.Bt, r: ActRt) -> ActRt:
  match r:
    case ActRt{ps, fs}:
      ActRt{ps, T.BField{nm, ty} <> fs}

def act.rtel(tel: A.Ag, np: Nat, ms: List<&2, ActM>, +ctx: List<&2, T.Bt>, +env: ActEnv) -> ActRt:
  match tel np ms:
    case A.AgTel{+x, i, ty, rest} 1n+p +m <> mt:
      +nm = act.fresh(x, ctx)
      act.rt.param(m, nm, act.t(act.field.sorts(act.quant.on(), act.inline(100000n, ty, env), env), ctx, env), act.rtel(rest, p, mt, act.entry(m, nm) <> ctx, env))
    case A.AgTel{+x, i, ty, rest} 1n+p Nil{}:
      +nm = act.fresh(x, ctx)
      act.rt.param(AmErased{}, nm, act.t(act.field.sorts(act.quant.on(), act.inline(100000n, ty, env), env), ctx, env), act.rtel(rest, p, Nil{}, T.BtVar{nm} <> ctx, env))
    case A.AgTel{+x, i, ty, rest} 0n ms:
      +nm = act.fresh(x, ctx)
      act.rt.field(nm, act.t(act.field.sorts(act.quant.on(), act.inline(100000n, ty, env), env), ctx, env), act.rtel(rest, 0n, ms, T.BtVar{nm} <> ctx, env))
    case _ _ _:
      ActRt{Nil{}, Nil{}}

# Kinds of the declared types (2026-10-20) ------------------------------------
#
# A type is as reusable as its fields' types, as Base's List is.  A field of
# a type parameter `-A: Kind(q)` contributes q (and so does a family
# `-B: A -> Kind(q)` applied); Nat, Bool, Unit, an equation or the type
# itself contribute &2; anything else contributes &1 (a function, a type, or
# another type).  The kind is the smallest: Data for &2, Type for &1, and
# Kind(q) in between.  So Σ A B is Kind(a <&> b), and Product's morphism
# pairs are Data when its homs are.

# the quantity a type's values have, from its type: Kind(q) is q, Data &2
def act.ty.endq(t: T.Bt) -> T.Bt:
  match t:
    case T.BtPi{m, y, d, a, b}:
      act.ty.endq(b)
    case T.BtApp{T.BtVar{+k}, T.BtArgs{+q, T.BtANil{}}}:
      Bool.pick(T.Bt, S.eq(k, S.b("Kind")), q, act.q1())
    case T.BtVar{+d}:
      Bool.pick(T.Bt, S.eq(d, S.b("Data")), act.q2(), act.q1())
    case _:
      act.q1()

# the quantity of the parameter named x's values (&1 if it is no parameter)
def act.p.q(ps: List<&2, T.BParam>, +x: List<&2, U32>) -> T.Bt:
  match ps:
    case Nil{}:
      act.q1()
    case T.BParam{m, +y, ty} <> t:
      Bool.pick(T.Bt, S.eq(x, y), act.ty.endq(ty), act.p.q(t, x))

def act.base.data(+x: List<&2, U32>) -> Bool:
  Bool.or(Bool.or(S.eq(x, S.b("Nat")), S.eq(x, S.b("Bool"))), S.eq(x, S.b("Unit")))

# a field's contribution
def act.fq(+self: List<&2, U32>, ty: T.Bt, +ps: List<&2, T.BParam>) -> T.Bt:
  match ty:
    case T.BtVar{+x}:
      Bool.pick(T.Bt, act.base.data(x), act.q2(), act.p.q(ps, x))
    case T.BtApp{T.BtVar{+x}, a}:
      act.p.q(ps, x)
    case T.BtTyApp{+x, a}:
      Bool.pick(T.Bt, S.eq(x, self), act.q2(), act.q1())
    case T.BtEq{t, a, b}:
      act.q2()
    case _:
      act.q1()

def act.kind.fs(+self: List<&2, U32>, fs: List<&2, T.BField>, +ps: List<&2, T.BParam>) -> T.Bt:
  match fs:
    case Nil{}:
      act.q2()
    case T.BField{x, ty} <> t:
      act.qmin(act.fq(self, ty, ps), act.kind.fs(self, t, ps))

def act.kind.cs(+self: List<&2, U32>, cs: List<&2, T.BCtor>, +ps: List<&2, T.BParam>) -> T.Bt:
  match cs:
    case Nil{}:
      act.q2()
    case T.BCtor{c, fs} <> t:
      act.qmin(act.kind.fs(self, fs, ps), act.kind.cs(self, t, ps))

def act.kind.term(+q: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, act.is.q2(q), T.BtVar{S.b("Data")}, Bool.pick(T.Bt, act.is.q1(q), T.BtType{}, T.BtApp{T.BtVar{S.b("Kind")}, T.BtArgs{q, T.BtANil{}}}))

def act.item.rec.of(+nm: List<&2, U32>, +c: List<&2, U32>, r: ActRt, doc: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match r:
    case ActRt{+ps, +fs}:
      [T.BiType{nm, ps, Bool.pick(T.Bt, act.quant.on(), act.kind.term(act.kind.fs(nm, fs, ps)), T.BtType{}), [T.BCtor{c, fs}], doc}]

def act.item.rec(s: ActSym, d: A.AgD, +env: ActEnv, doc: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match s d:
    case ActSym{m, +n, k, ms, ar, b, fs, +c, cp} A.AgDRec{pars, con, named, ind, fls, tel, eta, pm, rcl}:
      act.item.rec.of(n, c, act.rtel(tel, pars, ms, Nil{}, env), doc)
    case _ _:
      Nil{}

def act.decl.got(r: Map<&2, A.AgDecl> & A.AgDecl) -> A.AgDecl:
  (m, d) = r
  d

def act.decl0() -> A.AgDecl:
  A.AgDecl{A.AgQ{Nil{}, Nil{}, Nil{}}, Nil{}, Nil{}, Nil{}, 0n, 0n, 0n, A.AkWord{}, A.aas.i.vis(), Nil{}, A.AkWord{}, A.AgNone{}, A.AgDOther{A.AxNil{}}}

def act.ctor(d: A.AgDecl, +pars: Nat, +env: ActEnv, +ixs: List<&2, T.BParam>) -> T.BCtor:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, dd}:
      act.ctor.of(act.sym(env, q), pars, act.inline(100000n, ty, env), env, ixs)

def act.ctors(ks: List<&2, String>, +pars: Nat, +env: ActEnv, +decls: Map<&2, A.AgDecl>, +ixs: List<&2, T.BParam>) -> List<&2, T.BCtor>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      act.ctor(act.decl.got(Map.get(A.AgDecl, act.decl0(), decls, k)), pars, env, ixs) <> act.ctors(t, pars, env, decls, ixs)

# a field type a Data value may hold: Nat, Bool, Unit, an equation, or the
# type itself (by name, with no parameters)
def act.dataish(+self: List<&2, U32>, t: T.Bt) -> Bool:
  match t:
    case T.BtVar{+x}:
      Bool.or(Bool.or(S.eq(x, S.b("Nat")), S.eq(x, S.b("Bool"))), S.eq(x, S.b("Unit")))
    case T.BtTyApp{x, T.BtANil{}}:
      S.eq(x, self)
    case T.BtEq{ty, a, b}:
      True{}
    case _:
      False{}

def act.dataish.fs(+self: List<&2, U32>, fs: List<&2, T.BField>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case T.BField{x, ty} <> t:
      Bool.and(act.dataish(self, ty), act.dataish.fs(self, t))

def act.dataish.cs(+self: List<&2, U32>, cs: List<&2, T.BCtor>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case T.BCtor{c, fs} <> t:
      Bool.and(act.dataish.fs(self, fs), act.dataish.cs(self, t))

def act.item.data.of(+nm: List<&2, U32>, r: ActPs, +cs: List<&2, T.BCtor>, doc: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match r:
    case ActPs{+ps, ret, ctx, es, ok}:
      [T.BiType{nm, ps, act.kind.term(act.kind.cs(nm, cs, ps)), cs, doc}]

def act.item.data(s: ActSym, d: A.AgD, ty: A.Ag, +env: ActEnv, +decls: Map<&2, A.AgDecl>, doc: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match s d:
    case ActSym{m, +n, k, +ms, ar, b, fs, c, cp} A.AgDData{+pars, +ixs, cons, sort, dcl}:
      +t = act.inline(100000n, ty, env)
      +r = act.params(64n, Nat.add(pars, ixs), t, ms, Nil{}, env)
      act.item.data.of(n, r, act.ctors(act.keys(cons), pars, env, decls, act.ps.last(ixs, act.ps.ps(r))), doc)
    case _ _:
      Nil{}

# A primitive with clauses is the function its clauses define (2026-10-25):
# Agda.Builtin.Nat's `_+_`, `_*_`, `_-_`, `_==_`, `_<_`, div-helper and
# mod-helper keep their definitions under BUILTIN NATPLUS and the rest, and
# with no item for them every user dropped (corpus1r: 247 items, "uses plus
# in Agda.Builtin.Nat, which dropped it").  One without clauses (a string
# or float primitive) has no item, as before.  agda-export writes a
# primitive's clauses and tree in stored form (`noparams`); a primitive is
# no projection, so its stored form is its explicit form.
def act.unstore(t: A.Ag) -> A.Ag:
  match t:
    case A.AgStored{x}:
      x
    case t:
      t

def act.prim.cls(cls: A.Ag) -> A.Ag:
  match cls:
    case A.AgCl{tel, ps, body, ty, ca, rest}:
      A.AgCl{act.unstore(tel), ps, act.unstore(body), act.unstore(ty), ca, act.prim.cls(rest)}
    case cls:
      cls

def act.prim.fun(d: A.AgD) -> A.AgD:
  match d:
    case A.AgDPrim{n, cls, tree}:
      A.AgDFun{A.AgPrNone{}, 0n, None{}, False{}, A.AkNone{}, A.AgQEnd{}, act.prim.cls(cls), act.unstore(tree)}
    case d:
      d

def act.item.prim(s: ActSym, d: A.AgD, +key: String, +ty: A.Ag, +env: ActEnv, doc: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match d:
    case A.AgDPrim{n, A.AgClEnd{}, tree}:
      Nil{}
    case d:
      act.item.fun(s, act.prim.fun(d), key, ty, env, doc)

# The items of one definition: a function's def, a record's or data
# type's type; nothing for a constructor (its type has it), a copy (it is
# inlined where used), a Level name or a builtin (Base has it), or one of
# the transp and hcomp helpers --cubical-compatible generates (no-compilation).
def act.items.of(s: ActSym, k: A.AgKw, cp: Bool, nc: Bool, d: A.AgD, +key: String, ty: A.Ag, +env: ActEnv, +decls: Map<&2, A.AgDecl>, doc: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match s k cp nc:
    case s _ True{} _:
      Nil{}
    case s _ False{} True{}:
      Nil{}
    case ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop} A.AkFunction{} False{} False{}:
      act.item.fun(ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop}, d, key, ty, env, doc)
    case ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop} A.AkPrimitive{} False{} False{}:
      act.item.prim(ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop}, d, key, ty, env, doc)
    case ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop} A.AkRecord{} False{} False{}:
      act.item.rec(ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop}, d, env, doc)
    case ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop} A.AkData{} False{} False{}:
      act.item.data(ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop}, d, ty, env, decls, doc)
    case ActSym{m, n, k2, ms, ar, AbNone{}, fs, c, cop} A.AkPostulate{} False{} False{}:
      [T.BiComment{List.append(&2, List<&2, U32>, doc, [S.b("a postulate: not translated (Bend has none)")])}]
    case _ _ _ _:
      Nil{}

# whether a symbol is inlined where used (a copy, or made one)
def act.sym.copied(s: ActSym) -> Bool:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, cp}:
      act.copy.is(cp)

def act.items(d: A.AgDecl, +env: ActEnv, +decls: Map<&2, A.AgDecl>) -> List<&2, T.BItem>:
  match d:
    case A.AgDecl{+q, qn, md, +f, +l, l0, l1, k, m, +fl, lang, ty, dd}:
      act.items.of(act.sym(env, q), k, Bool.or(act.flag(A.AkCopy{}, fl), act.sym.copied(act.sym(env, q))), act.flag(A.AkNoCompilation{}, fl), dd, act.key(q), ty, env, decls, act.doc(act.qs(q), f, l))

# A type-valued function whose case tree is one leaf (no split): it
# unfolds, as a copy does, when a header needs the Pis behind it.
def act.unf.d(cp: Bool, srt: Bool, d: A.AgD) -> Maybe<&2, ActCopy>:
  match cp srt d:
    case False{} True{} A.AgDFun{A.AgPrNone{}, r, w, e, t, mu, cls, A.AgDone{xs, body}}:
      Some{ActCopy{act.vars.len(xs), body}}
    case _ _ _:
      None{}

# a definition's opening, when it is a type-valued one (unf: the earlier ones)
# a type- or Bool-valued definition's clauses (act.tcl.key)
def act.ix.is.bool(b: ActB) -> Bool:
  match b:
    case AbBool{}:
      True{}
    case _:
      False{}

def act.ends.bool.t(t: A.Ag) -> Bool:
  match t:
    case A.AgEl{s, A.AgDef{q, es}}:
      act.ix.is.bool(act.builtin(act.qs(q)))
    case _:
      False{}

# a record's first field's type, in the scope of its parameters (act.rft)
def act.rft.of(d: A.AgDecl) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDRec{+pars, c, named, ind, fs, tel, eta, pm, cl}}:
      Some{ActCopy{pars, act.tel.nth(tel, pars)}}
    case _:
      None{}

def act.tcl.d(on: Bool, dd: A.AgD) -> Maybe<&2, ActCopy>:
  match on dd:
    case True{} A.AgDFun{p, r, w, e, t, mu, cls, tree}:
      Some{ActCopy{1n, cls}}
    case True{} A.AgDPrim{n, cls, tree}:
      Some{ActCopy{1n, act.prim.cls(cls)}}
    case _ _:
      None{}

def act.tcl.of(d: A.AgDecl, +unf: Map<&2, ActCopy>) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, +ty, dd}:
      act.tcl.d(Bool.or(act.ends.sort.u(8n, ty, unf), act.ends.bool.t(act.target(ty))), dd)

def act.unf.of(d: A.AgDecl, +unf: Map<&2, ActCopy>) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, +ty, dd}:
      act.unf.d(act.flag(A.AkCopy{}, fl), act.ends.sort.u(8n, ty, unf), dd)

# Combinators (see act.cmb.key): which definitions are ones.

# whether a leaf is headed by a variable applied (no projection) or by a
# combinator's call, under its lambdas
def act.cmb.head(t: A.Ag, +unf: Map<&2, ActCopy>) -> Bool:
  match t:
    case A.AgLam{i, x, d, b}:
      act.cmb.head(b, unf)
    case A.AgVar{i, x, es}:
      act.es.plain(es)
    case A.AgDef{+q, es}:
      act.unf.has.got(Map.has(&2, ActCopy, unf, act.cmb.key(q)))
    case _:
      False{}

# whether a leaf is made of variables, constructors and combinators' calls
# only (under lambdas; a type, sort or level in it is dead): a lemma's
# proof calls other definitions (projections, `start`), and its body is
# not normalised.  yoneda20's first try, with the head alone, unfolded
# Algebra.Consequences.Setoid's reasoning chains (headed by `begin_`) and
# lost two lemmas there (2026-10-22).
def act.cmb.pure(t: A.Ag, +unf: Map<&2, ActCopy>) -> Bool:
  match t:
    case A.AgLam{i, x, d, b}:
      act.cmb.pure(b, unf)
    case A.AgVar{i, x, es}:
      act.cmb.pure(es, unf)
    case A.AgDef{+q, es}:
      Bool.and(act.unf.has.got(Map.has(&2, ActCopy, unf, act.cmb.key(q))), act.cmb.pure(es, unf))
    case A.AgCon{q, o, es}:
      act.cmb.pure(es, unf)
    case A.AgEApp{i, a, rest}:
      Bool.and(act.cmb.pure(a, unf), act.cmb.pure(rest, unf))
    case A.AgENil{}:
      True{}
    case A.AgPi{i, x, a, d, b}:
      True{}
    case A.AgSort{s}:
      True{}
    case A.AgEl{s, x}:
      True{}
    case A.AgLevel{l}:
      True{}
    case A.AgLit{l}:
      True{}
    case A.AgDontCare{x}:
      True{}
    case _:
      False{}

def act.cmb.leaf(hd: Bool, +n: Nat, body: A.Ag) -> Maybe<&2, ActCopy>:
  match hd:
    case True{}:
      Some{ActCopy{n, body}}
    case False{}:
      None{}

# cp: a copy or no-compilation; srt: type-valued
def act.cmb.d(cp: Bool, srt: Bool, d: A.AgD, +unf: Map<&2, ActCopy>) -> Maybe<&2, ActCopy>:
  match cp srt d:
    case False{} False{} A.AgDFun{A.AgPrNone{}, r, None{}, False{}, t, A.AgQEnd{}, cls, A.AgDone{+xs, +body}}:
      act.cmb.leaf(Bool.and(act.cmb.head(body, unf), act.cmb.pure(body, unf)), act.vars.len(xs), body)
    case _ _ _:
      None{}

# a definition's leaf, when it is a combinator (unf: the earlier ones)
def act.cmb.of(d: A.AgDecl, +unf: Map<&2, ActCopy>) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, +fl, lang, +ty, dd}:
      act.cmb.d(Bool.or(act.flag(A.AkCopy{}, fl), act.flag(A.AkNoCompilation{}, fl)), act.ends.sort.u(8n, ty, unf), dd, unf)

# A definition's eta unfolding (see act.etu.key): its case tree walked with
# the terms its leaf's variables stand for, over its n parameters; a split
# of a parameter whose type is a record with eta puts the record's
# projections of it in its place.  Anything else (a data split, a nested
# split, a catch-all, no split at all) has none.

# a record type's fields and arguments (the record found through
# type-valued definitions: A × B is Σ A (λ _ → B))
type ActRec is Data:
  ActRec{fs: List<&2, String>, es: A.Ag, ok: Bool}

# (the record by its symbol: the module's own declarations are all the
# decl map has, and Σ is Agda.Builtin.Sigma's; a split's eta branch already
# says the record has eta).  A record a module application copied is not
# taken: its fields are copies Bend has no names for (Core's `open import
# Categories.Morphism.IsoEquiv 𝒞` copies `_≃_`, 2026-10-21); the copy's
# clause leads to the original instead (act.etu.leaf)
def act.etu.rec.fs(s: ActSym, es: A.Ag) -> ActRec:
  match s:
    case ActSym{m, n, A.AkRecord{}, ms, ar, b, fs, c, None{}}:
      ActRec{fs, es, True{}}
    case _:
      ActRec{Nil{}, A.AgENil{}, False{}}

# what a name unfolds to: a copy's clause, else its leaf in the unfoldings
def act.etu.leaf(s: ActSym, +unf: Map<&2, ActCopy>, +q: A.AgQ) -> ActCopy:
  match s:
    case ActSym{m, n, k, ms, ar, b, fs, c, Some{cp}}:
      cp
    case _:
      act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(q)))

def act.etu.rec.pick(a: ActRec, b: ActRec) -> ActRec:
  match a:
    case ActRec{fs, es, True{}}:
      ActRec{fs, es, True{}}
    case _:
      b

def act.etu.rec(fuel: Nat, t: A.Ag, +tab: Map<&2, ActSym>, +unf: Map<&2, ActCopy>) -> ActRec:
  match fuel t:
    case f A.AgEl{s, x}:
      act.etu.rec(f, x, tab, unf)
    case 1n+f A.AgDef{+q, +es}:
      act.etu.rec.pick(act.etu.rec.fs(act.sym.got(Map.get(ActSym, act.sym0(), tab, act.key(q))), es), act.etu.rec(f, act.unfold.of(act.etu.leaf(act.sym.got(Map.get(ActSym, act.sym0(), tab, act.key(q))), unf, q), es), tab, unf))
    case _ _:
      ActRec{Nil{}, A.AgENil{}, False{}}

# a name from its key (w:k), the only part a translation looks up
def act.q.parts(ps: List<&2, List<&2, U32>>) -> A.AgQ:
  match ps:
    case w <> k <> Nil{}:
      A.AgQ{Nil{}, w, k}
    case _:
      A.AgQ{Nil{}, Nil{}, Nil{}}

def act.q.of.key(k: String) -> A.AgQ:
  act.q.parts(S.split(S.b(k), 58))

# each field's projection of p (the record's arguments, then p)
def act.etu.projs(fs: List<&2, String>, +es: A.Ag, +p: A.Ag) -> List<&2, A.Ag>:
  match fs:
    case q <> rest:
      A.AgDef{act.q.of.key(q), asb.elims.cat(es, A.AgEApp{A.aas.i.vis(), p, A.AgENil{}})} <> act.etu.projs(rest, es, p)
    case _:
      Nil{}

def act.etu.len.ok(+xs: List<&2, A.Ag>, +nf: Nat) -> List<&2, A.Ag>:
  Bool.pick(List<&2, A.Ag>, Nat.is_eq(List.length(&2, A.Ag, xs), nf), xs, [A.AgNone{}])

def act.etu.fields.of(r: ActRec, +p: A.Ag, +nf: Nat) -> List<&2, A.Ag>:
  match r:
    case ActRec{fs, +es, True{}}:
      act.etu.len.ok(act.etu.projs(fs, es, p), nf)
    case _:
      [A.AgNone{}]

def act.etu.dom(m: Maybe<&2, A.Ag>) -> A.Ag:
  match m:
    case Some{d}:
      d
    case None{}:
      A.AgNone{}

# the fields a split puts in place of the term it splits (a parameter)
def act.etu.fields(m: Maybe<&2, A.Ag>, +nf: Nat, +doms: List<&2, A.Ag>, +n: Nat, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, A.Ag>:
  match m:
    case Some{A.AgVar{+vi, x, A.AgENil{}}}:
      act.etu.fields.of(act.etu.rec(8n, act.etu.dom(asb.nth(Nat.sub(Nat.sub(n, 1n), vi), doms)), tab, unf), A.AgVar{vi, x, A.AgENil{}}, nf)
    case _:
      [A.AgNone{}]

def act.etu.at.k(+k: Nat, +nf: Nat, +terms: List<&2, A.Ag>, +doms: List<&2, A.Ag>, +n: Nat, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, A.Ag>:
  List.append(&2, A.Ag, List.take(&2, A.Ag, terms, k), List.append(&2, A.Ag, act.etu.fields(asb.nth(k, terms), nf, doms, n, unf, tab), List.drop(&2, A.Ag, terms, 1n+k)))

def act.etu.ok(ts: List<&2, A.Ag>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case A.AgNone{} <> t:
      False{}
    case h <> t:
      act.etu.ok(t)

def act.etu.done.ok(ok: Bool, +n: Nat, body: A.Ag, +terms: List<&2, A.Ag>) -> Maybe<&2, ActCopy>:
  match ok:
    case True{}:
      Some{ActCopy{n, asb.subst(body, 0n, List.reverse(&2, A.Ag, terms), List.length(&2, A.Ag, terms))}}
    case False{}:
      None{}

def act.etu.done(split: Bool, +n: Nat, body: A.Ag, +terms: List<&2, A.Ag>) -> Maybe<&2, ActCopy>:
  match split:
    case True{}:
      act.etu.done.ok(act.etu.ok(terms), n, body, terms)
    case False{}:
      None{}

def act.etu.tree(fuel: Nat, tree: A.Ag, +terms: List<&2, A.Ag>, +doms: List<&2, A.Ag>, +n: Nat, split: Bool, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> Maybe<&2, ActCopy>:
  match fuel tree:
    case 1n+f A.AgCase{i, +k, A.AgBranches{False{}, A.AgBEnd{}, A.AgBr{cq, +nf, sub, A.AgBEnd{}}, A.AgBEnd{}, A.AgNone{}}}:
      act.etu.tree(f, sub, act.etu.at.k(k, nf, terms, doms, n, unf, tab), doms, n, True{}, unf, tab)
    case f A.AgDone{xs, body}:
      act.etu.done(split, n, body, terms)
    case _ _:
      None{}

# the parameters' terms: var n-1 (the first) ... var 0
def act.etu.init(k: Nat) -> List<&2, A.Ag>:
  match k:
    case 0n:
      Nil{}
    case 1n+(+p):
      A.AgVar{p, S.b("x"), A.AgENil{}} <> act.etu.init(p)

# the variables, among n parameters, of the dependent binders at positions ps
def act.etu.vs(ps: List<&2, Nat>, +n: Nat) -> List<&2, A.Ag>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      A.AgVar{Nat.sub(Nat.sub(n, 1n), p), S.b("x"), A.AgENil{}} <> act.etu.vs(t, n)

def act.etu.dep(d: Bool, +j: Nat, deps: List<&2, Nat>) -> List<&2, Nat>:
  match d:
    case True{}:
      j <> deps
    case False{}:
      deps

# each Pi's domain in the scope of all n parameters (a non-dependent Pi
# binds no variable, so each domain is renamed, not shifted)
def act.etu.doms(t: A.Ag, +j: Nat, +n: Nat, +deps: List<&2, Nat>) -> List<&2, A.Ag>:
  match t:
    case A.AgEl{s, x}:
      act.etu.doms(x, j, n, deps)
    case A.AgPi{i, x, a, +d, b}:
      asb.subst(a, 0n, act.etu.vs(deps, n), List.length(&2, Nat, deps)) <> act.etu.doms(b, 1n+j, n, act.etu.dep(d, j, deps))
    case _:
      Nil{}

def act.etu.go(skip: Bool, +n: Nat, +ty: A.Ag, tree: A.Ag, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> Maybe<&2, ActCopy>:
  match skip:
    case True{}:
      None{}
    case False{}:
      act.etu.tree(64n, tree, act.etu.init(n), act.etu.doms(ty, 0n, n, Nil{}), n, False{}, unf, tab)

# a function's eta unfolding (not a projection, a copy or a type-valued one)
def act.etu.of(d: A.AgDecl, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> Maybe<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, +fl, lang, +ty, A.AgDFun{A.AgPrNone{}, r, w, e, t, mu, cls, tree}}:
      act.etu.go(Bool.or(act.flag(A.AkCopy{}, fl), act.ends.sort(ty)), act.cls.arity(cls), ty, tree, unf, tab)
    case _:
      None{}

# Projection form (2026-10-22) -------------------------------------------------
#
# Upstream Bend has no record eta: a match on a variable stays stuck.
# Relation.Unary's `(P ⟨×⟩ Q) (x , y) = P x × Q y`, written as a match on
# its pair, left `(P ⟨×⟩ Q) x` stuck where x is a variable (`_⟨·⟩_`'s
# argument: "expected: a datatype", and with it 72 of yoneda19's 121
# files).  Agda reads a record pattern as the record's projections; a
# type-valued function whose case tree splits only records with eta before
# its one leaf is written so: one clause of variables, its leaf with each
# split field the projection of its parameter (`P (proj₁ x) × Q (proj₂ x)`),
# its parameters erased as a type-valued definition's are.  A function with
# a value keeps its match: its projections would use the record twice, and
# its type would need eta to meet the body's (uncurry's `C p` against
# `C (proj₁ p , proj₂ p)`); headers unfold its calls instead
# (act.inline.hdr).

# each Pi's domain in the scope of all n parameters (as act.etu.doms), the
# type-valued definitions the type ends in opened (`Pred (A × B) ℓ` is
# `A × B → Set ℓ`)
def act.prj.doms(fuel: Nat, t: A.Ag, +j: Nat, +n: Nat, +deps: List<&2, Nat>, +unf: Map<&2, ActCopy>) -> List<&2, A.Ag>:
  match fuel t:
    case f A.AgEl{s, x}:
      act.prj.doms(f, x, j, n, deps, unf)
    case f A.AgStored{x}:
      act.prj.doms(f, x, j, n, deps, unf)
    case f A.AgPi{i, x, a, +d, b}:
      asb.subst(a, 0n, act.etu.vs(deps, n), List.length(&2, Nat, deps)) <> act.prj.doms(f, b, 1n+j, n, act.etu.dep(d, j, deps), unf)
    case 1n+f A.AgDef{+q, +es}:
      act.prj.doms(f, act.unfold.of(act.unf.got(Map.get(ActCopy, ActCopy{0n, A.AgNone{}}, unf, act.key(q))), es), j, n, deps, unf)
    case _ _:
      Nil{}

# the leaf with the split fields as projections (None: not only eta splits)
def act.prj.of(+n: Nat, +ty: A.Ag, tree: A.Ag, +env: ActEnv) -> Maybe<&2, ActCopy>:
  match env:
    case ActEnv{mod, tab, al, +unf}:
      act.etu.tree(64n, tree, act.etu.init(n), act.prj.doms(8n, ty, 0n, n, Nil{}, unf), n, False{}, unf, tab)

# the clause's telescope and patterns: a variable for each parameter
def act.prj.tel(ps: A.Ag) -> A.Ag:
  match ps:
    case A.AgPArg{i, x, p, rest}:
      A.AgTel{x, i, A.AgNone{}, act.prj.tel(rest)}
    case _:
      A.AgTEnd{}

def act.prj.ps(ps: A.Ag, +k: Nat, +n: Nat) -> A.Ag:
  match ps:
    case A.AgPArg{i, +x, p, rest}:
      A.AgPArg{i, x, A.AgPVar{x, Nat.sub(Nat.sub(n, 1n), k), A.AkWord{}}, act.prj.ps(rest, 1n+k, n)}
    case _:
      A.AgPEnd{}

def act.prj.cl(c: Maybe<&2, ActCopy>, cls: A.Ag) -> A.Ag:
  match c cls:
    case Some{ActCopy{n, body}} A.AgCl{tel, +ps, b, ty, ca, rest}:
      A.AgCl{act.prj.tel(ps), act.prj.ps(ps, 0n, act.pats.len(ps)), body, A.AgNone{}, False{}, A.AgClEnd{}}
    case _ cls:
      cls

# the clauses a function is written from: a type-valued one's (tyv)
# projection form when it has one, else its own
def act.prj.cls(p: A.AgProj, tyv: Bool, +cls: A.Ag, tree: A.Ag, +ty: A.Ag, +env: ActEnv) -> A.Ag:
  match p tyv:
    case A.AgPrNone{} True{}:
      act.prj.cl(act.prj.of(act.cls.arity(cls), ty, tree, env), cls)
    case _ _:
      cls

# a declaration as its items are written from it: a function's clauses in
# projection form when it has one (the symbol table keeps the original)
def act.prj.decl(d: A.AgDecl, +env: ActEnv) -> A.AgDecl:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, +ty, A.AgDFun{+p, r, w, e, t, mu, +cls, +tree}}:
      A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDFun{p, r, w, e, t, mu, act.prj.cls(p, act.tylevel.env(p, ty, env), cls, tree, ty, env), tree}}
    case d:
      d

# a copattern definition's field clauses into the unfoldings (see
# act.cop.key): a tree that splits its result by copatterns first, each
# field a leaf (a field taking more patterns has none)
def act.cop.brs(+dq: A.AgQ, brs: A.Ag, u: Map<&2, ActCopy>) -> Map<&2, ActCopy>:
  match brs:
    case A.AgBr{fq, k, A.AgDone{xs, body}, rest}:
      act.cop.brs(dq, rest, Map.set(&2, ActCopy, u, act.cop.key(dq, fq), ActCopy{act.vars.len(xs), body}))
    case A.AgBr{fq, k, t, rest}:
      act.cop.brs(dq, rest, u)
    case _:
      u

def act.cop.add(d: A.AgDecl, unf: Map<&2, ActCopy>) -> Map<&2, ActCopy>:
  match d:
    case A.AgDecl{q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDFun{p, r, w, e, t, mu, cls, A.AgCase{i, n, A.AgBranches{True{}, brs, eta, lits, ca}}}}:
      act.cop.brs(q, brs, unf)
    case _:
      unf

# A record field's projection, for the quantity pass's destructuring
# (ToBend/Copy.bend): its record's module and constructor (Bend names), the
# field's index and the field count; ok False for any other definition.
type ActPj is Data:
  ActPj{cmod: List<&2, U32>, ctor: List<&2, U32>, i: Nat, k: Nat, ok: Bool}

def act.pj.rec(s: ActSym, +key: String) -> ActPj:
  match s:
    case ActSym{m, n, A.AkRecord{}, ms, ar, b, +fs, c, cp}:
      ActPj{m, c, act.key.pos(key, fs), List.length(&2, String, fs), True{}}
    case _:
      ActPj{Nil{}, Nil{}, 0n, 0n, False{}}

def act.pj.of(d: A.AgDecl, +tab: Map<&2, ActSym>) -> ActPj:
  match d:
    case A.AgDecl{+q, qn, md, f, l, l0, l1, k, m, fl, lang, ty, A.AgDFun{A.AgPrOf{Some{r}, o, ix}, rs, w, e, t, mu, cls, tree}}:
      act.pj.rec(act.sym.got(Map.get(ActSym, act.sym0(), tab, act.key(r))), act.key(q))
    case _:
      ActPj{Nil{}, Nil{}, 0n, 0n, False{}}

# The quantity pass's modes put back into a symbol --------------------------------

def act.m.code(m: ActM) -> Nat:
  match m:
    case AmDrop{}:
      0n
    case AmErased{}:
      1n
    case AmLive{}:
      2n
    case AmCopy{}:
      3n
    case AmTpl{}:
      4n

type ActRe is Data:
  ActRe{ms: List<&2, ActM>, changed: Bool}

def act.re.put(m: ActM, r: ActRe, ch: Bool) -> ActRe:
  match r:
    case ActRe{ms, c}:
      ActRe{m <> ms, Bool.or(c, ch)}

# past the header, the modes Copy gives the return type's Pis the body's
# lambdas bind (a lowered point of `step-≈-⟩`), on the modes after the arity
def act.remode.rest(ms: List<&2, ActM>, hdr: List<&2, T.BMode>) -> ActRe:
  match ms hdr:
    case AmDrop{} <> t hdr:
      act.re.put(AmDrop{}, act.remode.rest(t, hdr), False{})
    case +m <> t h <> ht:
      +n = act.m.of(h)
      act.re.put(n, act.remode.rest(t, ht), Bool.not(Nat.is_eq(act.m.code(m), act.m.code(n))))
    case ms Nil{}:
      ActRe{ms, False{}}
    case Nil{} hdr:
      ActRe{Nil{}, False{}}

# A symbol's modes with its header's (the first ar parameters, the dropped
# ones skipped) replaced by the pass's; changed says whether any differs.
# A header longer than the modes (its type a definition the header opened
# to reach more Pis) adds the rest, which callers otherwise take as live.
def act.remode(ar: Nat, ms: List<&2, ActM>, hdr: List<&2, T.BMode>) -> ActRe:
  match ar ms hdr:
    case 0n ms hdr:
      act.remode.rest(ms, hdr)
    case 1n+p AmDrop{} <> t hdr:
      act.re.put(AmDrop{}, act.remode(p, t, hdr), False{})
    case 1n+p +m <> t h <> ht:
      +n = act.m.of(h)
      act.re.put(n, act.remode(p, t, ht), Bool.not(Nat.is_eq(act.m.code(m), act.m.code(n))))
    case 1n+p m <> t Nil{}:
      act.re.put(m, act.remode(p, t, Nil{}), False{})
    case 1n+p Nil{} h <> ht:
      +n = act.m.of(h)
      act.re.put(n, act.remode(p, Nil{}, ht), Bool.not(Nat.is_eq(act.m.code(n), 2n)))
    case 1n+p Nil{} Nil{}:
      ActRe{Nil{}, False{}}

def act.sym.remode.of(s: ActSym, r: ActRe) -> ActSym & Bool:
  match s r:
    case ActSym{m, n, k, x, ar, b, fs, c, cp} ActRe{ms, ch}:
      (ActSym{m, n, k, ms, ar, b, fs, c, cp}, ch)


# a symbol with new modes
def act.sym.remode(s: ActSym, hdr: List<&2, T.BMode>) -> ActSym & Bool:
  match s:
    case ActSym{m, n, k, ms, +ar, b, fs, c, cp}:
      act.sym.remode.of(ActSym{m, n, k, Nil{}, ar, b, fs, c, cp}, act.remode(ar, ms, hdr))

# The copattern helpers' unfoldings (Agda2Bend.bend a2b.cop.go): D's field
# under "cop:" D|FIELD is the helper at D's parameters (a field path of one
# projection), and a type-valued helper whose case tree splits only records
# with eta opens to its projection form (act.prj.of).  So a later type's
# `_≈_ (⟨ 𝑆 ⟩ A) x y` reads as the helper's Σ, the pair a refl splits.
type ActUe is Data:
  ActUe{k: String, c: ActCopy}

def act.cop.dvars(n: Nat, t: A.Ag, +k: Nat) -> A.Ag:
  match n t:
    case 1n+p A.AgEl{s, A.AgPi{i, x, a, dep, b}}:
      A.AgEApp{i, A.AgVar{Nat.sub(k, 1n), x, A.AgENil{}}, act.cop.dvars(p, b, Nat.sub(k, 1n))}
    case _ _:
      A.AgENil{}

def act.cop.ue.cop(ks: List<&2, A.AgQ>, +dq: A.AgQ, +hq: A.AgQ, +n: Nat, +dty: A.Ag) -> List<&2, ActUe>:
  match ks:
    case f <> Nil{}:
      [ActUe{act.cop.key(dq, f), ActCopy{n, A.AgDef{hq, act.cop.dvars(n, dty, n)}}}]
    case _:
      Nil{}

def act.cop.ue.prj(m: Maybe<&2, ActCopy>, +hq: A.AgQ) -> List<&2, ActUe>:
  match m:
    case Some{c}:
      [ActUe{act.key(hq), c}]
    case None{}:
      Nil{}

def act.cop.ue.ty(srt: Bool, +n: Nat, +ty: A.Ag, +tree: A.Ag, +hq: A.AgQ, +env: ActEnv) -> List<&2, ActUe>:
  match srt:
    case True{}:
      act.cop.ue.prj(act.prj.of(n, ty, tree, env), hq)
    case False{}:
      Nil{}

# a helper's entries (h: the helper; dq, dty: D's name and type; ks its path)
def act.cop.ue(+h: A.AgDecl, +dq: A.AgQ, +dty: A.Ag, +ks: List<&2, A.AgQ>, +n: Nat, +env: ActEnv) -> List<&2, ActUe>:
  match h:
    case A.AgDecl{+hq, qn, md, f, l, l0, l1, kd, mm, fl, lang, +hty, A.AgDFun{pr, rs, wi, e, t, mu, +cls, +tree}}:
      List.append(&2, ActUe, act.cop.ue.cop(ks, dq, hq, n, dty), act.cop.ue.ty(act.ends.sort(hty), act.cls.arity(cls), hty, tree, hq, env))
    case _:
      Nil{}

def act.cop.ue.hs(hs: List<&2, A.AgDecl>, +dq: A.AgQ, +dty: A.Ag, +ks: List<&2, A.AgQ>, +n: Nat, +env: ActEnv) -> List<&2, ActUe>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> t:
      List.append(&2, ActUe, act.cop.ue(h, dq, dty, ks, n, env), act.cop.ue.hs(t, dq, dty, ks, n, env))

def act.cop.ue.ps(ps: List<&2, List<&2, A.AgQ>>, +d: A.AgDecl, +q: A.AgQ, +ty: A.Ag, +cls: A.Ag, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, ActUe>:
  match ps:
    case Nil{}:
      Nil{}
    case +ks <> rest:
      +p = act.cop.pstr(ks)
      +n = act.cop.ntop.of(cls, p)
      List.append(&2, ActUe, act.cop.ue.hs(act.cop.hs.one(act.cop.needs(cls, p), ks, p, d, q, ty, cls, unf, tab), q, ty, ks, n, ActEnv{Nil{}, tab, Map.new(&2, List<&2, U32>), unf}), act.cop.ue.ps(rest, d, q, ty, cls, unf, tab))

def act.cop.ue.d(+d: A.AgDecl, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, ActUe>:
  match d:
    case A.AgDecl{+q, qn, md, f, l, l0, l1, k, m, fl, lang, +ty, A.AgDFun{A.AgPrNone{}, rs, w, e, t, mu, +cls, tree}}:
      act.cop.ue.ps(act.cop.paths(cls, Nil{}), d, q, ty, cls, unf, tab)
    case _:
      Nil{}

def act.cop.ues(ds: List<&2, A.AgDecl>, +unf: Map<&2, ActCopy>, +tab: Map<&2, ActSym>) -> List<&2, ActUe>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> t:
      List.append(&2, ActUe, act.cop.ue.d(d, unf, tab), act.cop.ues(t, unf, tab))

def act.cop.ue.put(es: List<&2, ActUe>, u: Map<&2, ActCopy>) -> Map<&2, ActCopy>:
  match es:
    case Nil{}:
      u
    case ActUe{+k, c} <> t:
      act.cop.ue.put(t, Map.set(&2, ActCopy, u, k, c))
