# agda2bend handoff

Working notes, so the work can continue from another machine or agent. Newest first. Times are UTC-6. agda2bend was split out of ana (github:hhefesto/ana) on 2026-10-22. ana's HANDOFF.md, before that date, has the rest of the history.

## ▶ CONTINUE HERE (2026-10-22, 18:40 UTC-6): its own repository, on upstream Bend; yoneda22 checks 2246 of 2527

- **The repository:** ~/src/agda2bend, github:hhefesto/agda2bend (public). Its history is ana's, filtered down to agda2bend's paths. ana takes `agda2bend` and `agda-export` from this flake, as its input `agda2bend`, and pins the same nixpkgs and Bend.
- **Bend is upstream's** (bendlang/bend 2.0.38, b8664b0), with no fork. The fork's record eta (2b33b4f1) was reverted in cecf7397, then the fork was dropped altogether. agda2bend writes a type-valued function's record match as projections, and it unfolds a header's record-matching call. The fixture A2bFix covers both.
- **Dev runs live in run/a2b** (untracked, moved from ~/src/ana/run/a2b): the exports (export2: 768 modules), the yonedaN runs, and bin/ (the -O0 dev builds). `tools/a2b/README.md` describes the loop. run/a2b/gcroot-bend has to be rebuilt from this flake (`nix build .#bend -o run/a2b/gcroot-bend`), because the old root is the fork's bend.
- **yoneda22** (no record eta): 2246 checked, 166 dependent, 115 dropped, of 2527. yoneda21 (record eta) had 2250 / 165 / 112. The changes: 2 checked→dependent, 9 checked→dropped, 1 dependent→dropped, 5 dropped→checked.
  - Category.Construction.Functors: 5 checked→dropped, 2 dropped→checked.
  - LiftSetoids: 2 checked→dropped, 1 dropped→checked.
  - Functor.Hom: 1 dependent→dropped, 1 dropped→checked.
  - Data.Unit.Properties: 2 checked→dependent, 1 checked→dropped (⊤ eta).
  - WellFounded: 1 checked→dropped, 1 dropped→checked.
  - Categories.Yoneda: 12 items, 0 check (3 gaps).
- **In progress (uncommitted, unbuilt, by FoggyOrca):**
  - ToBend/Copy.bend has a new pass, `tcp.unit`, for Agda's ⊤ eta. A def whose body is one expression matches its Unit params against `Unit{}`.
  - Agda2Bend.bend has `a2b.shape = Q.tcp.unit(a2b.destr(it, te))`, which replaces `a2b.destr` in `a2b.re.items` and `a2b.finish`.
  - `Q.tcp.destr` is still unwired (a2b.destr has been a stub since 10-20).
- **Next, in order:**
  1. Build and test the ⊤ pass (tools/a2b/test.sh, then `nix flake check`). Then run yoneda23 on upstream Bend and compare it with yoneda22, remembering that the Bend binary changed.
  2. Win back the drops: Data.Unit.Properties (⊤ eta), Category.Construction.Functors, LiftSetoids, Category.Product and Setoids (both need record eta), and Categories.Yoneda's 12.
  3. Corpus readiness: what share of the output a corpus can use. On yoneda19, 26 of 121 files with long lines held 91% of the bytes.
  4. The shell scripts in tools/a2b fail ana's shell lint (all logic belongs in Bend), so port them to Bend.
  5. The public page, agda2bend.hhefesto.dev, and a tweet, once it's ready.

## Previous (2026-10-22, 07:30 UTC-6, from ana's HANDOFF): Bend had record eta (the fork, since reverted); yoneda19 checks 1986 of 2527

- **Record eta in Bend:** hhefesto/bend2 ft-kernels 2b33b4f1, which flake.lock now pins. It works in checking only, by two rules:
  - A match on a neutral record goes on with the record's projections.
  - A constructor equals a neutral value when they agree field by field.
  - A record means one constructor, with no field that reaches the datatype, either by its own name or through a type-level def. Base's `Word.Con` reaches it through `tail: Word(p)`. Missing that case hung everything that imports Base.
  - Bend's tests/check, proof and base (396 files) give the same verdicts as before.
  - `--verdict` doesn't know eta.
  - The pattern that stuck Product (`zip` assoc and left identity on function-typed homs, an `OP` record) checks with eta and fails without it.
- **Levels as quantities are on** (`act.quant.on()`). Qfix (ToBend/Qfix.bend) solves each quantity argument from the kind of the type passed: &1 for a function type, &2 for Data, the hom quantity for `Arr(C)(x, y)`. The gate solves them again after its repairs. The goldens for Level and Function.Base were remade with quantities, and Function.Base's 33 items all still check. agda2bend.bend gives 52 oks locally.
- **yoneda19** (eta Bend plus Qfix): 1986 checked, 397 dependent, 144 dropped, of 2527. yoneda18 had 1976 / 389 / 150 of 2515.
  - LiftSetoids: 5 of 7 (was 2).
  - Category.Product: 8 of 16 (was 7), with 7 dropped.
  - Setoids: 0 of 1.
  - Functor.Hom: 3 of 7.
  - Categories.Yoneda: 0 of 12, all 12 dependents.
- **Top causes** (`agda2bend report run/a2b/yoneda19 run/a2b/yoneda18`):
  - `expected Data observed Kind(a)`: 175 blocked, 4 roots.
  - A value used twice: 64 blocked, 26 roots.
  - `expected Data observed Type`: 52 blocked, 17 roots.
  - An erased binder used live: 51 blocked, 15 roots.
  - `Category<C.o, &2, &2>` vs `Category`: 23 blocked, 2 roots (Dinatural).
  - Product's own: `_※ⁿ_`, `πʳ`, `Swap`.

## CONTINUE HERE (2026-10-20, 08:00 UTC-6): agda2bend on the Yoneda cone, 1923 of 2527 items check; Product and Setoids hit Bend's missing record eta

- **The loop:** `run/a2b/bin/agda2bend-O0 emit run/a2b/export2 run/a2b/yonedaN Categories.Yoneda` translates Categories.Yoneda's 121-module import cone (stdlib and agda-categories) with that day's translator. Each run is about 40 min and about 80 MB. Then `agda2bend report run/a2b/yonedaN run/a2b/yonedaM` ranks the causes against the previous run. Dev tools, uncommitted, in /tmp/claude-1000/a2b:
  - build.sh: the dev binary.
  - test.sh: the tests, 36 laws.
  - probe.sh: `probe.sh OUT MODPATH AGDANAME`, a gated module plus raw items, checked.
  - export-each.sh: the per-module exporter.
- **Runs** (checked of 2527 items; Categories items of 523):

  | Run | Checked | Categories | Change |
  |---|---|---|---|
  | yoneda2 | 1430 | 149 | Data kinds, indexed families |
  | yoneda3 | 1752 | 287 | re-exported copy modules, absurd clauses, unfolded Pis |
  | yoneda5 | 1859 | 337 | a field named like a def is no use (7169da6); a template in a dead argument no longer makes one; projections' type-valuedness by their own type |
  | yoneda6 | 1869 | 349 | objects, morphisms and setoid points erased in dependent visible Pis (an opaque type: a record field that is a type) |
  | yoneda7 | 1886 | 351 | arguments of a variable marked "mode unknown" (live for templates); a return-type Pi raised when its lambda is used live; functions type-valued once opened, projections by their own type |
  | yoneda8 | 1678 | 175 | destructuring record parameters: reverted, see below |
  | yoneda9 | 1886 | 351 | yoneda7 + the eta unfolding through the symbol table (it fires: Product's `_⇒_` is a pair of hom types; Product then stops at zip, eta) + opaque seen through AgDefX: neutral |
  | yoneda10 | 1898 | 351 | a live parameter with no live use falls to erased (a variable's arguments count as uses); the Data repair raises a point-free def's return-type Pi; 13 gains, Function.Base golden 32 of 33 check |
  | yoneda11 | 1901 | 355 | copattern reductions: a field projected out of a copattern def is its clause (`isPartialEquivalence(partialSetoid(S))` -> `isPartialEquivalence(isEquivalence S)`, glue loses its hom-setoid template); 6 gains, 2 regressions (`≉-respʳ`: S now used twice at a variable's arguments, which Copy does not count) |
  | yoneda12 | 1901 | 355 | the return type's Pis (bound by head lambdas) get their raised modes into the symbol past the arity; lowering them was tried and reverted (a Pi is part of the type: `const` passed as `B -> A`); same as yoneda11 (the committed tree 8cdccfa) |
  | yoneda13 | 1858 | 290 | lambda lifting (a plain function takes all its Pis as parameters, its body applied to the extras): lifted erased parameters were passed live, so Copy raised `Functor.₁`'s objects and `_∘F_` fell |
  | yoneda14 | (stopped) | | levels as quantities: unsound (a type at a variable level may be a function type, which Bend makes Type), switched off |
  | yoneda15 | 1923 | 355 | lifting with erased lifted parameters passed dead (+22, 23 gains); quantity code present behind `act.quant.on()` = False |

- **Bend limits found** (memory project-bend2-silent-traps):
  - A type-valued def's body is live at its top.
  - A template argument in a dead place may be any variable.
  - A later dotted type fails through an import.
  - **No record eta.** Product's `_∘_ = zip _∘_ _∘_` stays stuck on morphism-pair variables in its laws. A projection-based zip would copy a pair of morphisms, and morphisms are Type: Setoids' are `Func` records. Setoids' composition hits the same wall.
  - **Templates are inlining:** `Carrier(partialSetoid(~S))` reduces. Destructuring the record (yoneda8) made it affine but stuck on variables, and the reasoning layer fell (Categories 351 to 175). It is unwired in a2b.destr; its code and laws stay.
  - So Yoneda itself (12 items) waits on Product (through Bifunctor) and Setoids.
- **Why the reasoning lemmas still take their objects and morphisms as templates** (debug build, 2026-10-20 01:30): a chain's points (`(f ∘ a) ∘ b`) go live to `step-≈-⟩`, whose point is a Pi of its return type, so each morphism counts as used twice. Lowering that Pi changes the def's type. The next step is to lift a point-free def's head lambdas into header parameters (the arity grows through remode), then lower them as parameters are.
- **Product, specialised to Data homs (the user's choice, 2026-10-20):** tested in Bend (scratchpad prod/r.bend, s.bend, t.bend). A `Cat<q>` with `Arr: Obj -> Obj -> Kind(q)` and Product at `&2` checks with Agda's own `assoc = (C.assoc , D.assoc)` and projection-based composition. The translator side is in the tree but switched OFF (`act.quant.on()` in Cata.bend). It covers:
  - Level binders as `Quant` parameters, `Set ℓ` as `Kind(qℓ)`.
  - A declaration's kind from its fields (`Σ` is `Kind(a <&> b)`).
  - The gate's `&2` specialisation repair (Copy tcp.q.spec, gate kind 4).
  - Inlining partial pair-building eta-only calls (Product's `_∘_ = zip …`).

  Deriving quantities from levels failed: `Setoids c ℓ` has `Func` homs (Type) at the variable level `c ⊔ ℓ`, and a probe of the Product cone checked 146 of 2226. A quantity argument must instead be the kind of the type it governs (`Arr(C)(…)`: C's hom quantity; a function type: &1; Data: &2), which needs kind inference over the Bend terms. That is the next step for Product.
- **Next:**
  1. Commit yoneda9 if it holds against yoneda7.
  2. The top causes in yoneda7.report:
     - "expected Data observed Type", 51 roots, 325 blocked: setoid points used twice in reasoning chains, and eta-lambda type parameters the Data repair cannot raise.
     - Values used twice (16 roots).
     - Dependent J (Bend limit).
  3. Decide what to do about record eta. Options: ask upstream Bend, give the fork eta for single-constructor types, or encode Product's homs differently.
- **Erasure oracle (2026-10-20, 972bef1 and 9411f76):** `agda-export --export-erasure-only` writes OUT/<Module>.erasure.sexp, one `(erasure Q (args N) (erased I*) (unused I*) …)` per definition (FORMAT.md, "The erasure sidecar"). All 767 modules of run/a2b/export2 have one; the driver is /tmp/claude-1000/a2b/erasure-each.sh, ad hoc.
  - In agda-categories, Agda's compiler erases little beyond levels, types and record parameters. glue keeps its objects and morphisms, and step-≈-⟩ keeps its point. So a sidecar is a lower bound on what is safe to erase, not a stand-in for agda2bend's heuristics.
  - Not read by agda2bend yet, which is optional per the user.
- **Export:** run/a2b/export2 has 768 modules. Not exported:
  - 6 agda-categories modules timed out at 1200 s: Bicategory.Construction.Spans and Spans.Properties, Category.Construction.SymmetricMonoidalFunctors, Functor.Monoidal.PointwiseTensor, Functor.Profunctor, Profunctor.Cograph.
  - 4 ran out of the 12 GB heap: EnrichedCats, End.Fubini, End.Parameterized, EnrichedUnderlying.

## Previous (2026-10-19, evening UTC-6): agda2bend translates Agda into checked Bend 2; Categories.Category.Core translates completely

The user (2026-10-19): "I want something that takes in agda code and spits out bend code … a parser of lean or agda in bend and then a cata that turns that parsed code into more regular bend code. After that it should be easier to fix anything that didn't translate so well and iterate over the translator." Plan: ~/.claude/plans/humming-brewing-shannon.md (approved; Agda first, only ALL PROOFS CHECK output, every Agda CT repository in scope; Lean later on the same back end). The user on an Agda/Lean oracle pass: "take it into consideration … Don't forcefully use it" (optional; not used yet).

- **The pipeline** (all Bend except the exporter):
  - `tools/agda-export` (Haskell, Agda 2.8.0 backend, FORMAT.md version 2): elaborated definitions as S-expressions. Since 5096af4 a module application's copy functions are written compactly (case tree only), which a v1 export of agda-categories had run out of a 10 GB heap on.
  - `bend/ToBend/Sexp.bend` (reader, streaming) → `bend/Agda2Bend/Ast.bend` (the parser of Agda: one type `Ag`, keywords by hash) → `bend/Agda2Bend/Cata.bend` (the fold: symbol table, copy inlining with beta-reduction, terms, headers, clauses into one match in parameter order, refl splits into `%e` rewrites, records, data, projections, copatterns) → `bend/ToBend/Copy.bend` (the quantity pass: erased/live/+/templates, in rounds) → `bend/ToBend/Order.bend` → `bend/ToBend/Print.bend` → `bend/ToBend/Gate.bend` (locked bend, first error; repairs a named binder, else drops it and its dependents; cross-module dependents dropped before any check).
  - CLI `bend/Agda2Bend.bend`: `translate FILE.agda OUT` (agda-export into OUT/export, then emit), `emit EXPORT OUT [MODULE...]` (a cone, or the whole export), `report OUT` (the ledger ranked by root cause), `decode`. OUT/src is checked Bend, OUT/raw the same modules before the gate, OUT/ledger.tsv every item (module, Bend name, Agda name, checked/dropped/dependent, reason).
  - Flake: `nix run .#agda2bend -- translate FILE.agda OUT` (ee9f83e; not yet built by nix, the -O3 compile takes 10+ min). Dev binary: run/a2b/bin/agda2bend-O0 (/tmp/claude-1000/a2b/build.sh: bend -o C, clang -O0, ~2 min).
  - Tests: bend/tests/agda2bend.bend, 22 laws, compiled (the interpreter's stack does not hold Level): the reader, the decoder, the printer's goldens, and the whole translation of a committed import cone (Agda.Primitive, Level, Function.Base) against goldens.
- **Results** (run/a2b/outN, each on Categories.Category.Core's 65-module cone):
  - run 5: 503 items checked; run 8: 950, Category.Core 22/22 (the Category record and its projections, Category.op, ∘-resp-≈ˡ, hom-setoid, with the category a `~` template, as the hand spike wrote it); run 9: 1,080; run 10 (equation rewrites that check, beta-reduction): 1,103 checked, 87 dropped, 609 dependents.
  - Relation.Binary.PropositionalEquality.Core alone: 16 of 17 (sym, trans, cong, subst through `%e` rewrites).
  - `agda2bend report run/a2b/out9`: the top causes are polymorphic values used twice (`_ˢ_`: Bend copies only Data), Reflects/Dec (indexed families, not translated yet), absurd patterns (`⊥-elim`), and a few erasure mismatches at eta-expanded calls.
- **The export of all of agda-categories:** run/a2b/export2 (403 modules after one process ran out of a 14 GB heap); the rest are being exported in chunks of 40 modules (run/a2b/everything/Chunk[A-H].agda, /tmp/claude-1000/a2b/export-chunks.sh, log run/a2b/export-chunks.log). agda-export is GC-rooted at run/a2b/gcroot-agda-export (an unrooted store path was collected once).
- **Next:** indexed families (constructor fields carrying `{idx == i}`, rewrites in matches); absurd clauses (`match x:` with no cases); a library run over the whole export (`emit run/a2b/export2 OUT`); then the per-repository census (milestone 7) and lean2bend.
- **Bend facts learned** (memory project-bend2-silent-traps): names are per file (import alias + full name); a match on several values, and nested matches, must follow parameter order; `noabs` binds no variable (FORMAT.md); `Bool.pick` evaluates both branches (several near-misses with recursion in both); an equation cannot be matched, only rewritten (`%e : P` needs the goal to be P with e's right side at the holes).

## Rules

- **Bend only.** Everything after agda-export is Bend. Write no Python. A shell script is a thin shim.
- **Git:** commits carry no Co-Authored-By. Ask before pushing.
- **Machine hygiene:** `nix build --max-jobs 1`. Heavy Bend compiles queue on `$A2B_LOCK`. Long runs go under `systemd-run --user --scope -p MemoryMax=… -p MemorySwapMax=…`, because an unbounded build once filled RAM and swap.
- **Logs** are stamped in Mexico City time (UTC-6) by `ck.wall` (bend/Clock.bend over bend/effs/wall.c and wall.js).
