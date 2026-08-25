# The CBOR boundary tests

Two extraction tests built from one corpus and one model:

```
cbor-corpus/valid.txt        26 vectors expected to be accepted
cbor-corpus/malformed.txt    22 vectors expected to be rejected
cbor-corpus/model.py        the independent oracle both modules are generated against
cbor-corpus/mutants.py      the adequacy measurement, run against either module
CborBoundary.{core.in,gen.py,parsers.txt,fst}
pulse/CborBoundarySlice.{core.in,gen.py,parsers.txt,fst}
```

The corpus, the oracle and the measurement exist **once**.  Two checkers
generated from two copies of the same vectors would be free to drift into
testing different things while both stayed green, which is the failure mode
this whole directory exists to argue against.

| test | language | columns | runs under | cost |
|---|---|---|---|---|
| `CborBoundary.fst` | pure F\* | direct-C | stage1/2/3, every push | 7.9 s |
| `pulse/CborBoundarySlice.fst` | Pulse, over a slice | direct-C **and** Rust | stage3 only | 34 s |

Both are reduced deterministic-CBOR well-formedness checkers. Neither is the
real EverParse parser; they exist to keep exercising four classes of
behaviour that a curated corpus was measured to reach and that random input
generation was measured not to:

1. UTF-8 codepoint and continuation-byte boundaries,
2. minimal-length integer encodings at each width boundary,
3. declared element counts versus remaining input budget,
4. truncation, i.e. proper prefixes of well-formed items.

The two differ in how the input is represented, and that difference is the
point of having both. `CborBoundary.fst` consumes a `ref`-linked cons cell,
which is the only byte-sequence a pure-F\* module has; it is the version that
can run under stage1 and stage2, which do not have the Pulse language
extension. `CborBoundarySlice.fst` consumes a `Pulse.Lib.Slice.slice byte`
over a stack-allocated array, which is what EverParse's own parsers take, and
is the only one of the two that can drive the Rust column.

Both `main`s report through an exit code: direct-to-C has no krmllib, so
there is no `FStar.IO.print_string` to link against.

## Regenerating and reproducing

```
python3 CborBoundary.gen.py CborBoundary.fst
python3 cbor-corpus/mutants.py ops    _output/CborBoundary.dc   # after `make`
python3 cbor-corpus/mutants.py consts _output/CborBoundary.dc

cd pulse
python3 CborBoundarySlice.gen.py CborBoundarySlice.fst
python3 ../cbor-corpus/mutants.py ops    _output/CborBoundarySlice.dc
python3 ../cbor-corpus/mutants.py consts _output/CborBoundarySlice.dc
```

Each generator defaults to the shared corpus, so neither can be pointed at
the wrong vectors by accident.  `mutants.py` derives the symbol prefix from
the name of the `.dc` and reads the functions it is allowed to mutate from
the module's `.parsers.txt`; mutating anything else -- the embedded vector
constructors above all -- corrupts the test data rather than the parser and
inflates the kill count, which is a mistake that was actually made and
caught here.

`cbor-corpus/model.py` is an independent Python model of the reduced
grammar. It is what decides whether each vector is expected to be accepted,
so the expected values in the generated module do not come from the parser
under test.

Current adequacy against the extracted C, with `-fsanitize=address,undefined
-fno-sanitize-recover=all` and a clean reference run:

| module | operator family | constant family |
|---|---|---|
| `CborBoundary` | 46 / 46 | 46 / 46 |
| `CborBoundarySlice` | 48 / 49 | 46 / 59 |

`CborBoundarySlice`'s survivors are accounted for rather than tuned away.
One in each family is `pos < l` → `pos <= l` in `rem`, where both branches
return `0` at `pos == l`. The other twelve perturb the recursion budget
`fuel`, which exists only to discharge the `decreases` clause and is slack
for every vector in the corpus; they are unobservable by construction, not a
coverage gap.

## Two negative results

These are the reason the tests are shaped the way they are, and they are
worth keeping in mind before simplifying either of them.

### "It compiles" is not an acceptance criterion for a backend

The bug that motivated this corpus was a miscompilation, not a build
failure. karamel modelled `Pulse.Lib.Slice.slice t` as an owning `Box<[T]>`;
the `.clone()` calls rustc suggests to make that borrow-check *do* make it
compile, and they also make every write land in a temporary that is then
discarded. A test that builds the generated code and stops passes cleanly
while the parser silently returns zeroes.

So both of these tests write their vectors through the buffer and then check
their own answers, and the `.dcran`/`.rsran` rules run the binary. This is
also why `CborBoundarySlice` is worth its 34 s despite duplicating the
other's logic: it is the only one of the two whose Rust column exercises
`&mut [u8]`.

### Line coverage is a poor proxy for defect detection

Reducing a corpus by line coverage looks principled and is not. Starting
from 12,110 random inputs over the full EverParse CBOR parser, a greedy set
cover shrank the corpus to **28 inputs with identical line coverage** — and
those 28 killed only **118 of 135** mutants, missing 17. Validated out of
sample against a mutation operator family the reduction had never seen, the
same 28 killed **57 of 152**.

A mutation-guided reduction of the same corpus to a comparable size behaved
completely differently: 40 vectors reproduced the full 458-vector curated
corpus exactly, 139/139 on the fitting family and 152/152 out of sample.
Same budget, 2.7× the detection, purely from minimising against the right
signal.

Two procedural lessons came out of that study and are worth repeating:

- **Validate a reduction on a held-out mutation operator family**, not just a
  different seed. The same-family candidate pool gets exhausted, so a
  reduction fitted to it will look perfect and generalise badly.
- **Never patch a held-out miss with the miss's own witness.** Add the
  principled class the witness belongs to, or the held-out set stops
  measuring anything.

### A worked example of the second lesson

The corpus grew from 40 to 48 vectors when `CborBoundarySlice` was written,
and how that happened illustrates both lessons.

Porting the parser from the cons cell onto a slice left two operator-family
survivors. Rather than assume they were equivalent mutants, the bounds check
in `peek` was instrumented:

```c
if (i == (uint64_t)Pulse_Lib_Slice_len__t(s)) { atend(); }
```
```
peek-at-end calls: 0
```

`peek` was never reached at `i == len` by any of the 40 vectors, so the
mutant that widens its check to `<=` was unreachable rather than equivalent:
the corpus had no vector truncated *inside a header's argument bytes*,
despite truncation being one of the four classes above. The cons-cell version
could not have exposed this, because running off the end of a linked list
returns `None` structurally and there is no bounds check to mutate.

The held-out constant family then found a second gap: `hi1 = 0xBF`, the
UTF-8 second-byte upper bound for the non-`E0`/`ED` and non-`F0`/`F4` leads,
was never probed at `0xC0`.

Both were fixed by adding the class rather than the witness — one
truncated-argument vector per argument width, and the just-inside and
just-outside pair for each of the two `hi1` defaults — and every added vector
was confirmed against `cbor-corpus/model.py` first.
