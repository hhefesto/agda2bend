# agda2bend handoff

Working notes, so the work can continue from another machine or agent. Newest first. Times are UTC-6. agda2bend was split out of ana (github:hhefesto/ana) on 2026-10-22. ana's HANDOFF.md, before that date, has the rest of the history.

## corpus1t: agda-categories past module 355 (2026-10-29, 00:45 UTC-6; running)

- **Why every category run stopped at 355.** corpus1, corpus1r and corpus1s all logged the same 355 of export2's 767 modules, the last being Categories.Adjoint.Monadic. None of them wrote the 356th module's raw file, so the translation itself stalled, not the check. The next module ready in import order is Categories.Adjoint.Monadic.Properties, a **678 MB export**. corpus1s spent 18 h on it until the OOM killer stopped it at a 16 GB peak (10-26 20:14). Twelve of the remaining exports are bigger than 150 MB, and Categories.Pseudofunctor.Composition is 843 MB.
- **The big exports give almost nothing.** Over corpus1s's ledger (4,281 checked items), the modules under 5 MB gave 3,141 checked items and those of 5-20 MB gave 1,096. The modules of 20-100 MB gave 40, and the ones over 100 MB gave 0. Their items are dependents of earlier drops. The time goes into translation: Monoidal.Properties (227 MB) took 73 min for 38 items, all of them dependents.
- **corpus1t** (unit `a2b-corpus1t`, MemoryMax 10G) runs master's translator (bin/agda2bend-O0-c1s, 3174c1e; the master code is unchanged since) with corpus1s's environment (`A2B_MAXLINE=100000 A2B_CORPUS_LINE=2000`). Its input is **run/a2b/export2s**: symlinks to export2's 703 exports of 20 MB or less, with their erasure sidecars. A module it skipped is simply missing: an item naming one of its defs drops with "a name the symbol table does not have" (tested on Data.Empty.Polymorphic without Data.Empty). I expect about 7 h at corpus1s's pace (1,425 MB in 7.4 h) and longer at today's load.
- **ana takes it** through its unit `ana-a2bm7` (ana run/v5/clean/a2bm7.sh). That unit waits for corpus1t to end, then runs `corpus` on export2 + corpus1t and keeps only the ids ana's a2b-s lacks. corpus1s's own copies already reached ana: run 5's a2b-s takes 232 modules from export2 + corpus1s, and all 232 are in it.
- **Not done:** resuming (skipping the check of modules an earlier run's ledger has) and skipping items whose dependencies dropped before translation. Either would save the 7 h that corpus1t spends redoing corpus1s's first 355 modules, minus their big exports.

## ▶ CONTINUE HERE (2026-10-25, 20:15 UTC-6): ⊤ eta, dead arguments and Nat's primitives, merged into master

- **Merged and pushed (10-25 20:15).** The user said to merge `unit-eta` into master and push once yoneda24 showed no losses. It showed none (below), so master is unit-eta, fast-forwarded and pushed.
- **The user (10-25): "continue the agda2bend effort".** The work was on the local branch `unit-eta` (master b05bb3c plus these commits and HANDOFF notes):
  - ad671d1: FoggyOrca's ⊤ pass (wip/unit-eta bd8303b), built and tested. Data.Unit.Properties checks 6 of 12 (was 2): `_≟_`, `⊤-irrelevant`, `≡-total`, `≡-decSetoid`. `≡-isPreorder` still drops (Agda's implicit points are `tt`).
  - 68db2ed: dead arguments. An argument the callee takes erased or dropped (past its modes: a hidden, instance, irrelevant or @0 one) is inlined as a header's place is, so a call there that has an eta unfolding takes it (Cata.bend act.inline.go carries the callee's modes, `ms`). Category.Product checks 13 of 16 (was 8): πˡ, πʳ, assocˡ, assocʳ, Swap. Refl's point `proj₁ (zip _∘_ _∘_ g f)` was stuck on the pairs g f.
  - 3174c1e: a primitive with clauses is the function its clauses define. Agda.Builtin.Nat's `_+_`, `_-_`, `_*_`, `_==_`, `_<_` had no item, and every user dropped (corpus1r: 247 items blocked by "uses plus in Agda.Builtin.Nat"). agda-export writes a primitive's clauses in stored form (`noparams`), which for a primitive is the explicit form. Data.Nat.Base's cone (run/a2b/nat-prim2): +31 checked (5 in Agda.Builtin.Nat, 26 dependents in Data.Nat.Base), no losses. div-helper and mod-helper still drop: Bend's termination reads arguments left to right, and their first argument grows.
  - Tests: 57 ok with all three.
- **Corpus mode drops whole cones for one wide item.** `agda2bend report run/a2b/corpus1r`: Categories.Category.Product's `Product` has a 75,431-character line, so `A2B_MAXLINE=20000` drops it and 281 items that use it. Categories.Functor's `identity′` (35,696) blocks 134. corpus1s (unit a2b-corpus1s, started 10-25 18:53) runs the category export again with this branch's translator (bin/agda2bend-O0-c1s: 3174c1e with the 8 GB pool stack) and `A2B_MAXLINE=100000`. The corpus copy still keeps only lines up to 2000 (`A2B_CORPUS_LINE`). corpus1r keeps going as the fallback. Over its first 253 modules corpus1r equals corpus1 item for item, so the Bend change of 10-22 didn't change those results.
- **Runs** (run/a2b, Categories.Yoneda's cone unless said; compare with `sh /tmp/bx/a2b/ue/ledcmp.sh OLD/ledger.tsv NEW/ledger.tsv`, an awk join on module and Agda name):
  - yoneda22u: master's translator (bin/agda2bend-O0-c1r) on upstream Bend 2.0.38, the baseline. Up to module 111 it equals yoneda22 item for item.
  - yoneda23: + the ⊤ pass (bin/agda2bend-O0-y23). Up to module 111: +4 checked, no losses.
  - prod-dead: + dead arguments (bin/agda2bend-O0-dead), Category.Product's cone only (94 modules): +5 checked, no losses against yoneda23.
  - yoneda24: + dead arguments, the whole cone (bin/agda2bend-O0-dead, finished 20:11). Against yoneda22u: +10 checked (8 dropped→checked, 2 dependent→checked: the 4 Data.Unit.Properties items, Product's πˡ, πʳ, assocˡ, assocʳ, Swap, and Bifunctor.flip), no checked item lost. 2 dependent→dropped: NaturalTransformation.Properties' `F′` and `G′`, no longer blocked, now drop on their own (expected `Category<anon.F_p~C_o, &2, &2>`). Categories.Yoneda: still 0 of 12.
  - nat-prim3: + primitives (bin/agda2bend-O0-prim2), Data.Nat.Properties' cone (126 modules) in corpus mode (finished). Against corpus1r on the modules both have: +60 checked (dependent→checked), no checked item lost, 72 dependent→dropped (unblocked, now dropping on their own). Totals 2707 checked, 682 dependent, 317 dropped.
- **The old corpus runs (corpus1–5, 10-22) were checked by a different Bend:** gcroot-bend then pointed at /nix/store/js8k6x6…-bend, the fork's Bend 2.0.37 run by bun. Its checker (bend2/bend.ts) is the same file as upstream 2.0.38's; base.bend, comp.ts, main.ts and safe.ts differ. gcroot-bend has been upstream's since 10-25 15:48. corpus1r (unit a2b-corpus1r, the category run again, 1G stack) runs on upstream.
- **Speed:** corpus1r spent 73 min on Categories.Category.Monoidal.Properties (16:49 to 18:03) and checked none of its 38 items: all are dependents of earlier drops. Its translation (one core, no bend child) is the cost. Skipping items whose dependencies already dropped, before translating them, would save hours per corpus run. The dependencies would have to come from the Agda side.
- **Setoids, the user's decision (live objects in law fields): not tried, it looks like a net loss.** Setoids needs its objects live in three fields, not one:
  - `assoc` uses `D` (`IsEquivalence.refl(…, Setoid.isEquivalence(D))`).
  - `equiv` uses `A` (`Setoid.isEquivalence(setoid(~B, A))`).
  - `∘-resp-≈` uses `C`.
  - `Category.equiv` appears 3576 times in yoneda22/src (24 files). Live objects there would make every hom-setoid step use its objects live, and an object (Kind(o)) can't be copied. The other law fields together appear 184 times.
  - So Yoneda's 12 items stay blocked by Setoids unless its objects get another encoding.
- **LiftSetoids** (`_..extendedlambda1`, Bend name anon.anon.extendedlambda1_2): its header keeps `extendedlambda0_2(…, x)`, a match on Lift, stuck on the variable x. Headers do unfold calls that have an eta unfolding, so extendedlambda0_2 seems to get none. Lift has one field, so its projection form would use x once. Not debugged yet.
- **Next:**
  1. Done: yoneda23 and yoneda24 against yoneda22u showed no losses; unit-eta merged and pushed (10-25 20:15).
  2. LiftSetoids: why extendedlambda0_2 has no eta unfolding.
  3. Category.Construction.Functors: several drops have `uncurry` stuck (see yoneda24 for what dead arguments fixed).
  4. The top causes in `agda2bend report run/a2b/yoneda22` (/tmp/bx/a2b/ue/y22.report): an erased binder used live (56 blocked, 18 roots, mostly eta-expanded binders in Function.Bundles), Data vs Type (27), Dinatural's `Category<C.o, &2, &2>` (23), dependent J (19).

## Previous (2026-10-22, 21:05 UTC-6): corpus runs for ana, category theory first

- **The user (10-22, evening): "work on agda2bend. we should extend the ana corpus with as much bend as advisable. Start with category theory themed code and continue with any code you think would do good for training ana."**
- **Corpus mode** (committed with this entry): two emit settings and a command.
  - `A2B_MAXLINE=N`: an item printed with a line wider than N never reaches a check (`G.tgt.wide`); what uses it is dropped too. The widest items were elaborated reasoning chains (yoneda22: 85% of 9 MB in 187 lines over 2,000 characters, the widest 1.8 MB) and the slowest to check (one module took 30 min). Corpus runs use 20000.
  - `A2B_CORPUS_LINE=N`: after the gate, each module's corpus copy goes to OUT/corpus/<path>.bend: the kept items no wider than N, less those using a wider one of the module (`G.tgt.corpus`), so the copy checks against the same imports. Corpus runs use 2000, ana's raw limit (ana docs/CORPUS-V2.md, C6).
  - `agda2bend corpus JSONL DIR OUT... [DIR OUT...]`: every module's corpus copy as one JSONL line `{"id", "text"}`; each export DIR is followed by the runs (OUTs) made from it, and an id already written is skipped (the first OUT with a module wins; Agda's builtins come once). The id mirrors the Agda source (`a2b:agda-categories/src/Categories/Adjoint.bend`, `a2b:agda-stdlib/src/Data/Bool/Base.bend`, `a2b:agda/src/data/lib/prim/Agda/Builtin/Sigma.bend`; another package keeps its name less hash and version), so ana's `bend-corpus-v2 raw` holds a translation out with its Agda source's unit. Tried on a 12-module cone: ana's raw kept 11 and held out Data.Bool.Base, the leak noted on 10-22.
- **Names** (ToBend/Names.bend): `.` is a separator like `_` and `-`, so a generalized variable's level `A.a` is `A_a` (it was `A_u002e_a`, 13,488 times in yoneda22's short lines). New words: subscripts ₄–₉, ʸ, ᵣ, ⊢ (vdash), ⊣ (dashv), ⟪ ⟫ (llangle, rrangle). The Function.Base goldens were remade (only those names changed; 57 ok).
- **Exports** (run/a2b, untracked; drivers /tmp/bx/a2b/export3.sh, export3b.sh, exportlib.sh, one-offs):
  - export3: export2 (hard links) plus the standard library's other modules, all but Tactic, Reflection, IO, System, Foreign, Debug, Size, Codata.Musical, Codata.Sized, Test (770 asked, all exported; dependencies pull some of the excluded ones in). Chunks of 40 imports need `{-# OPTIONS --guardedness --sized-types #-}` (both infective).
  - export-libsA: export3 plus agdarsec, functional-linear-algebra and generics (68 modules). export-hs: agda2hs-base (`--erasure --no-projection-like`; Haskell.Extra.Delay and Haskell.Prim.Thunk need sized types and are missing). export-prelude: agda-prelude (alone: it shares module names with the standard library). AGDA_DIR for these: run/a2b/libs/agda-dir (the nixpkgs agdaPackages, GC-rooted in run/a2b/libs). iowa-stdlib doesn't build in this nixpkgs; 1lab, cubical and cubical-mini are cubical, which agda2bend doesn't translate.
- **Corpus runs** (user units a2b-corpus1..5, `A2B_MAXLINE=20000 A2B_CORPUS_LINE=2000`, binaries run/a2b/bin/agda2bend-O0-c1/-c2, logs run/a2b/corpusN.log):
  - corpus1: all of export2 (agda-categories' 487 modules and their standard-library cone, 768 modules).
  - corpus2: export3's 1102 non-Categories modules (the standard library).
  - corpus3: export-libsA's 68 new modules. corpus4: export-hs. corpus5: export-prelude.
  - Then (/tmp/bx/a2b/finish.sh, unit a2b-finish, waits for the five): `agda2bend corpus ~/src/ana/run/v5/a2b/bend.jsonl run/a2b/export-libsA run/a2b/corpus1 run/a2b/corpus2 run/a2b/corpus3 run/a2b/export-hs run/a2b/corpus4 run/a2b/export-prelude run/a2b/corpus5`, then ana's `bend-corpus-v2 raw` on it into ~/src/ana/run/v5/a2b/raw (what ana would keep, and the holdout).
- **Not done yet:** Setoids with live objects in law fields (the user's decision, below), the ⊤ pass on wip/unit-eta, Product's stuck zip. Each would add checked items to the next corpus run.

## Previous (2026-10-22, 18:40 UTC-6): its own repository, on upstream Bend; yoneda22 checks 2246 of 2527

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
- **The flake is on nixpkgs** (0bb7ec5). A move to ekapkgs (6c44cef, as Telomare does) was reverted on 10-22: too green yet (its standard-library build failed, and Agda and most of the Haskell harness weren't in its cache). Tried again 10-24/25 on the local branch `ekapkgs` (9eede20: Agda's primitive library checked at install, which fixes the standard-library build): everything builds and checks, but ekala's cache has lost even gcc and glibc, so every machine would build the toolchain from source; that needs a cache of our own, and the user said no (10-25): stay on nixpkgs.
- **In progress, on branch wip/unit-eta (bd8303b, FoggyOrca's, unbuilt as a binary):**
  - ToBend/Copy.bend has a new pass, `tcp.unit`, for Agda's ⊤ eta. A def whose body is one expression matches its Unit params against `Unit{}`.
  - Agda2Bend.bend has `a2b.shape = Q.tcp.unit(a2b.destr(it, te))`, which replaces `a2b.destr` in `a2b.re.items` and `a2b.finish`.
  - The flake check `tests` passed with it applied (57 ok, 18:53), but no run used it.
  - `Q.tcp.destr` is still unwired (a2b.destr has been a stub since 10-20).
- **FoggyOrca's last findings (10-22 18:4x):**
  - Data.Unit.Properties lost `≡-isPreorder` and 2 dependents. Agda's eta filled implicit points with `tt`, so `trans(&2, Unit, Unit{}, Unit{}, Unit{}, eta1, eta2)` has `eta1 : {i == j}`.
  - `tcp.unit` aims at `⊤-irrelevant`, `_≟_` and `≡-total`, which would bring back 3 items plus 3 dependents (not verified).
  - LiftSetoids: `extendedlambda1` drops on `Setoid.eq` over `Level.Lift.lower(…)`, probably Lift's missing eta.
  - WellFounded's "swap" is an artifact: `GeneralizeTel` appears twice in both ledgers, which duplicates its key in the join.
  - **Setoids fails on "expected -D observed D".** Category's law fields erase objects and morphisms (a yoneda6 choice), but Setoids' `assoc` needs `Setoid.isEquivalence(D)` live. Yoneda's 12 items depend on it through Presheaves and NT.Hom. **User's decision (10-22): keep objects live in law fields if that gives better Bend output.** So try it, run it against the last yoneda run, and keep it only if more items check overall (yoneda6's erasure won 10 items, which it may lose).
  - Product: πˡ, πʳ, assocˡ and assocʳ drop because `Product_Base.zip(…)` is stuck inside refl's erased point. A planned fix: `act.inline.go` unfolds calls in projection form at arguments the callee takes erased or dropped, as headers already do.
  - Scratch from that work is in /tmp/bx/fo: the joins (l21/l22/j/m21/m22.tsv) and the probes (u/t1–t6.bend). Don't run /tmp/bx/fo/inl.pl: its regex never terminates.
- **Next, in order:**
  1. Build and test the ⊤ pass (tools/a2b/test.sh, then `nix flake check`). Then run yoneda23 on upstream Bend and compare it with yoneda22, remembering that the Bend binary changed.
  2. Win back the drops: Data.Unit.Properties (⊤ eta), Category.Construction.Functors, LiftSetoids (Lift's eta), Category.Product (the stuck `zip`; the planned fix is above), Setoids (live objects in law fields, kept only if the net count rises), and Categories.Yoneda's 12.
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
