# agda2bend

Agda in, checked [Bend 2](https://github.com/bendlang/bend) out.

agda2bend translates Agda modules, together with the modules they import, into
Bend 2. It keeps only what upstream Bend's checker accepts. Everything else is
dropped and written down in a ledger with the reason, so you can rank the causes
and work on the translator from them. Nothing is patched into the checker: the
Bend it targets is the stock release.

It's work in progress. On agda-categories' `Categories.Yoneda` import cone
(121 modules from the standard library and agda-categories, 2527 items), 2246
items check. The other 281 are dropped, or depend on something that was
(run `yoneda22`, 2026-10-22). Below are the main reasons, and what doesn't
translate yet.

## Use

```sh
# translate a file and the modules it imports; OUT/src holds the Bend that checks
nix run github:hhefesto/agda2bend -- translate Foo.agda out

# translate an existing export (agda-export's --export-dir), a module's cone or all of it
nix run github:hhefesto/agda2bend -- emit EXPORT_DIR out Categories.Yoneda

# the ledger summed up, causes ranked by the items they block
nix run github:hhefesto/agda2bend -- report out
```

`translate` runs from the root of FILE's Agda library. By default agda-export
resolves the standard library and agda-categories. To use other libraries, set
`AGDA_DIR`.

### Training data for ana

The checked output is training data for
[ana](https://github.com/hhefesto/ana), a small model that writes Bend. Two
settings make an emit produce it:

```sh
# A2B_MAXLINE: an item with a line wider than this never reaches a check
#   (the widest terms are elaborated reasoning chains, up to 1.8 MB on one line,
#   and the slowest to check), and what uses it is dropped too
# A2B_CORPUS_LINE: each module's corpus copy, OUT/corpus/<path>.bend, keeps the
#   checked items no wider than this, less those that use a wider one
A2B_MAXLINE=20000 A2B_CORPUS_LINE=2000 agda2bend emit EXPORT_DIR out

# every module's corpus copy as one JSONL ({"id", "text"} a line): each export
# dir is followed by the runs made from it, and the first run with a module wins;
# ids mirror the Agda sources' paths, a2b:agda-categories/src/Categories/Adjoint.bend,
# so ana's repository holdout holds a translation out with its Agda source
agda2bend corpus corpus.jsonl EXPORT_DIR out [out2 ...] [EXPORT_DIR2 out3 ...]
```

2,000 characters is ana's limit on a line of raw code. Without the caps, 85% of
the Yoneda cone's 9 MB of output was in 187 lines past it, so those files
couldn't go into ana's corpus at all.

From another flake:

```nix
inputs.agda2bend.url = "github:hhefesto/agda2bend";
# packages: agda2bend, agda-export, bend (the pinned checker)
```

## How it works

1. **Elaboration is Agda's.** `tools/agda-export` is an Agda 2.8.0 backend,
   written in Haskell, and the only part that isn't Bend. It writes every
   definition of every module in the import closure as one S-expression of
   Agda's internal syntax: types, clauses, compiled case trees, records, data
   types and constructors. It decides nothing. `tools/agda-export/FORMAT.md` is
   the contract.
2. **Everything after that is Bend.** The pipeline:
   - the S-expression reader (`bend/ToBend/Sexp.bend`), which streams;
   - the parser of Agda (`bend/Agda2Bend/Ast.bend`);
   - a fold from the parsed Agda into a Bend syntax tree
     (`bend/Agda2Bend/Cata.bend`);
   - the Bend-side passes (`bend/ToBend/`): names, order, the quantity pass
     `Copy.bend`, levels as quantities `Qfix.bend`, and the check gate
     `Gate.bend`;
   - the printer (`bend/ToBend/Print.bend`);
   - the driver (`bend/Agda2Bend.bend`).
3. **The gate.** Each module is checked by the pinned `bend`. Whatever fails is
   dropped, and so is everything that depends on it. The ledger
   (`OUT/ledger.tsv`) records each item's fate and reason.

Levels are erased to quantities. Record parameters become `~` templates.
Indexed families carry their index as an erased type parameter. Absurd clauses
match down to an empty type. A record match in a type-valued definition is
written with projections, because Bend has no record eta.

## Where it stands

Top reasons items are dropped on the Yoneda cone:

- `expected Data observed Kind(a)`: records over a carrier of an arbitrary
  kind.
- a polymorphic value used twice (Bend copies only `Data`);
- an erased binder used live;
- eta for records and for `⊤`, where a proof relies on it;
- what gets erased: Category's law fields erase their objects and morphisms,
  but the proofs in `Setoids` need them live, and Yoneda depends on those.

`HANDOFF.md` has the working notes and the current plan.

## Develop

```sh
nix build .#agda2bend          # the translator (Bend to C, clang -O3; slow)
nix flake check                # bend/tests/agda2bend.bend: reader, parser, printer, gate, goldens
tools/a2b/build.sh             # a quick -O0 dev binary at run/a2b/bin/agda2bend-O0
tools/a2b/test.sh              # the tests with the dev build
```

`tools/a2b/README.md` describes the dev loop. `bend/Sys.bend`, `Nul.bend`,
`Tokenizer.bend`, `Sha256.bend`, `Num.bend` and `Clock.bend` are small libraries
shared with [ana](https://github.com/hhefesto/ana), which agda2bend was split out
of (its history comes with it).

## License

MIT. Agda, the Agda standard library, agda-categories and Bend are their
authors' work, under their own licenses.
