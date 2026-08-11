# Extraction findings

Every entry below is reproduced by a test module in this directory and pinned
down by an `XFAIL_<backend>` entry in the `Makefile`. When a bug is fixed, the
corresponding cell starts passing, the `xfail` rule reports `UNEXPECTED PASS`,
and the build stops — so a fix cannot silently go unrecorded.

Severities, following the classification we set out to test for. Note that
severity 1 is about the *extracted program* crashing, not about krml or
fstar.exe crashing -- a toolchain failure is severity 4, since the outcome is
the same as generating code the backend compiler rejects: no usable output.

| | |
|---|---|
| **1** | the extracted program crashes at runtime |
| **2** | F\* statically proves a value, the runtime produces a different one |
| **3** | right answer, wrong performance (e.g. a lost short circuit) |
| **4** | extraction does not produce usable output: the backend compiler rejects it, or the toolchain itself fails |

Backends: **ml** = OCaml, **c** = C via Karamel, **rs** = Rust via Karamel.

---

## Summary

| # | Issue | Sev | ml | c | rs | Test |
|---|-------|-----|----|---|----|------|
| 1 | `IntN.ne` / `UIntN.ne` has no Krml opcode | 4 | ✗ | ✗ | ✗ | `ExtIntNe` |
| 2 | `shift_arithmetic_right` unsupported by the Rust backend | 4 | ✓ | ✓ | ✗ | `ExtIntShiftArith` |
| 3 | `UInt8.lognot` is not truncated in OCaml | **2** | ✗ | ✓ | ✓ | `ExtUInt8Lognot` |
| 4 | narrowing casts dropped inside comparisons | **2** | ✓ | ✗ | ✓ | `ExtIntCast` |
| 5 | `Prims.int` `/` and `%` truncate instead of Euclidean in C | **2** | ✓ | ✗ | – | `ExtPrimsIntDiv` |
| 6 | `Prims_op_Star` is never defined in krmllib | 4 | ✓ | ✗ | – | `ExtPrimsIntMul` |
| 7 | `Prims_int` is `int32_t`; literals silently truncate | **2** | ✓ | ✗ | – | `ExtPrimsIntBignum` |
| 8 | recursive inductives emit uncompilable C, undiagnosed | 4 | ✓ | ✗ | ✗ | `ExtDatatypesRec`, `ExtDatatypesMutual` |
| 9 | krml does not terminate on two recursive datatypes (C *and* Rust) | 4 | ✓ | ✗ | ✗ | `ExtDatatypesRec` |
| 10 | Rust backend references a `lowstar` module it never emits | 4 | ✓ | ✓ | ✗ | `ExtDatatypesRecord`, `ExtDatatypesVariant` |
| 11 | projector applied to a constructor application crashes krml | 4 | ✓ | ✗ | ✗ | `ExtProjectorOfCtor` |
| 12 | Rust backend cannot translate `EFun` and silently truncates the crate | 4 | ✓ | – | ✗ | `ExtBoolHigherOrder` |

`–` means "not applicable": the backend rejects the feature by design (closures
are not Low\*; the Rust backend refuses mathematical integers outright).

---

## 1. `FStar.IntN.ne` / `FStar.UIntN.ne` have no Krml opcode

*Severity 4 (C, Rust) and 4 (OCaml, for `UInt8` only). Test: `ExtIntNe`.*

`mk_op` in `src/extraction/FStarC.Extraction.Krml.fst:494-517` maps the
machine-integer operator names onto Krml opcodes. It has a case for `eq`, but
none for `ne` — even though the Krml AST has had a `Neq` opcode all along
(same file, line 148). The call therefore falls through to a plain function
call:

* **C**: emits `FStar_Int32_ne(a, b)`. The symbol is `extern`-declared in
  `FStar_Int32.h` but defined in no `.c` file in krmllib, so the build fails
  with an implicit declaration under `-Werror` and would fail to link anyway.
* **Rust**: `ERROR translating ...: Failure("unexpected: [type] no casts in
  Low* -> Rust")`, after which krml **exits 0** and writes a crate with the
  function silently missing (see also #12).
* **OCaml**: works for every width except `UInt8`, whose realization is
  hand-written and simply lacks `ne` (see #3).

The fix is one line in `mk_op`:

```diff
   | "eq" -> Some Eq
+  | "ne" -> Some Neq
```

## 2. `shift_arithmetic_right` is unsupported by the Rust backend

*Severity 4. Test: `ExtIntShiftArith`.*

Like `ne`, this is not a Krml opcode. The C backend is rescued by hand-written
`static inline` definitions in `karamel/include/krml/fstar_int.h`, which are
whitelisted in `builtin_names` in `karamel/lib/Helpers.ml` (~line 516). The
Rust backend has no equivalent fallback and dies with

```
Failure("unexpected: [type] no casts in Low* -> Rust")
Fatal error: exception Not_found
```

— the `Not_found` being a second, unhandled failure while reporting the first.

## 3. `FStar.UInt8.lognot` is not truncated in OCaml

*Severity 2 — silent wrong value. Test: `ExtUInt8Lognot`.*

`ulib/ml/app/FStar_UInt8.ml` is the only machine-integer realization written by
hand; `UInt16/32/64` and `Int8/16/32/64` are generated from
`ulib/ml/app/ints/FStar_Ints.ml.body` by `mk_int_file.sh` on top of `Stdint`.
The hand-written file represents a `uint8` as an OCaml `int` and masks the
result of every operation that can leave range — except `lognot`:

```ocaml
let lognot (a:uint8) : uint8 = lnot a      (* missing `land 255` *)
```

So `FStar.UInt8.lognot 0uy` evaluates to `-1` while F\* proves it is `255uy`.
Nothing crashes; the value is simply not the verified one, and it is not even
representable as a `uint8`, so every subsequent comparison, cast and
`to_string` is wrong too. Since F\* proves
`UInt8.v (UInt8.lognot 0uy) = 255`, the bad value can be laundered into an
out-of-bounds index.

While diffing that file against the generated `FStar_UInt16.ml`, the following
are also missing from `FStar_UInt8.ml`: `ne`, `of_int`, `of_native_int`,
`to_native_int`, `shift_arithmetic_right`, `len`, `zeroes`.

## 4. Narrowing casts are dropped inside comparisons (C)

*Severity 2 — silent wrong value. Test: `ExtIntCast`.*

`mk_arith` in `karamel/lib/AstToCStar.ml` has an optimization that removes the
`(uint32_t)` upcasts it inserts around `UInt8`/`UInt16` operands before a
comparison. As written, it strips **any** cast:

```ocaml
| Eq | Neq | Lt | Lte | Gt | Gte when a1 && a2 ->
    let strip e = match e with CStar.Cast (inner, _) -> inner | _ -> e in
    CStar.Call (Op op, [ strip e1; strip e2 ])
```

A user-written *narrowing* cast is atomic too, so it is stripped along with the
upcasts. Minimal repro:

```fstar
let u64big : U64.t = 0x123456789abcdef0uL
let f () : bool = U32.eq (C.uint64_to_uint32 u64big) 0x9abcdef0ul   (* F*: true *)
let g () : U32.t = C.uint64_to_uint32 u64big                        (* F*: 0x9abcdef0 *)
```

generates

```c
bool f(void) { return u64big == 0x9abcdef0U; }   /* cast gone: false */
uint32_t g(void) { return (uint32_t)u64big; }    /* cast kept: correct */
```

The comparison is performed at 64 bits and yields `false` where F\* proves
`true`. Introduced by karamel commit `8c19d414` ("Fix UInt8/UInt16 masking:
switch scrutinee, ETernary, ECast").

The `widened` flag that `mk_arith` already returns is true *exactly* for the
casts the catch-all case inserts, so it can be used to strip only those:

```ocaml
| Eq | Neq | Lt | Lte | Gt | Gte when a1 && a2 ->
    let strip w e =
      if w then match e with CStar.Cast (inner, _) -> inner | _ -> e else e
    in
    CStar.Call (Op op, [ strip w1 e1; strip w2 e2 ])
```

This was verified locally: with the patch, `f` becomes
`(uint32_t)u64big == 0x9abcdef0U` and the whole matrix in this directory
passes. The patch has not been committed here because `karamel/` is a
submodule.

## 5. `Prims.int` division and remainder truncate in C

*Severity 2 — silent wrong value. Test: `ExtPrimsIntDiv`.*

F\*'s `/` and `%` on `Prims.int` are **Euclidean**: the remainder is always
non-negative.

| | F\* | C / OCaml native |
|---|---|---|
| `(-17) / 5` | `-4` | `-3` |
| `(-17) % 5` | `3` | `-2` |

`karamel/krmllib/dist/generic/prims.c` hands the operation straight to C:

```c
int32_t Prims_op_Division(int32_t x, int32_t y) { RETURN_OR((int64_t)x / (int64_t)y); }
int32_t Prims_op_Modulus (int32_t x, int32_t y) { RETURN_OR((int64_t)x % (int64_t)y); }
```

so every negative dividend is silently wrong. F\* will prove `x % 5 >= 0`,
which makes this another way to produce an out-of-bounds index from verified
code. OCaml is correct because extraction routes these through Zarith's
`ediv`/`erem`.

## 6. `Prims_op_Star` is never defined

*Severity 4. Test: `ExtPrimsIntMul`.*

F\* extraction emits `Prims.op_Star` for `*` on `Prims.int`, and the C backend
turns that into a call to `Prims_op_Star`. krmllib only ever defines
`Prims_op_Multiply`, so the generated C fails to compile:

```
error: implicit declaration of function 'Prims_op_Star'
```

## 7. `Prims_int` is 32 bits, and literals bypass the overflow check

*Severity 2. Test: `ExtPrimsIntBignum`.*

`karamel/include/krml/internal/compat.h`:

```c
typedef int32_t Prims_pos, Prims_nat, Prims_nonzero, Prims_int, krml_checked_int_t;
```

Operations go through `RETURN_OR`, which detects overflow and calls
`KRML_HOST_EXIT(252)` — noisy, and defensible for something documented as a
porting aid. *Literals*, however, bypass that check entirely: they are printed
verbatim into the generated C and truncated by the compiler, so

```c
krml_checked_int_t big2 = 987654321098765432109876543210;
```

silently becomes `-775520534`. gcc only tells you because of `-Werror=overflow`;
without it the program runs and computes with the wrong number.

## 8. Recursive inductives emit uncompilable C, with no diagnostic

*Severity 4. Tests: `ExtDatatypesRec`, `ExtDatatypesMutual`.*

Low\* has no heap-allocated inductives, so a constructor field whose type is
the type being defined cannot be laid out. Karamel does not diagnose this: it
emits a struct containing itself by value and lets the C compiler complain.

```
T1.h:24:20: error: field 'tl' has incomplete type
T2.h:30:10: error: field 'case_Neg' has incomplete type
```

The user gets an error about generated code rather than about their source.

## 9. krml does not terminate on two recursive datatypes

*Severity 4 — the toolchain hangs. Test: `ExtDatatypesRec`.*

This affects **both** Karamel backends, so the loop is in a shared phase
(monomorphization / the boxing fixpoint) rather than in `AstToMiniRust`.
Nine lines are enough (>5 minutes at 100% CPU and ~1.5 GB RSS, no output):

```fstar
module H3
module U32 = FStar.UInt32
type mylist (a:Type) = | Nil : mylist a | Cons : hd:a -> tl:mylist a -> mylist a
type tree = | Leaf : U32.t -> tree | Node : tree -> tree -> tree
let rec length (#a:Type) (l:mylist a) : U32.t =
  match l with | Nil -> 0ul | Cons _ tl -> U32.add_mod 1ul (length tl)
let rec tree_sum (t:tree) : U32.t =
  match t with | Leaf v -> v | Node l r -> U32.add_mod (tree_sum l) (tree_sum r)
let main () : U32.t = U32.add_mod (length (Cons 1ul Nil)) (tree_sum (Leaf 1ul))
```

Either type alone is translated in well under a second, and a single recursive
type also hangs when it is used by two different recursive functions *and*
built with a nested constructor literal -- so the trigger is not the number of
types as such.

Because the C backend hangs before it can lay the types out, `ExtDatatypesRec`
never even reaches the "incomplete type" error of #8; that one is observed on
`ExtDatatypesMutual` and on single-type repros. This is also why every krml
invocation in this directory runs under `timeout $(KRML_TIMEOUT)`: without it,
`make` never finishes.

Separately, mutually recursive types are not boxed at all, and rustc rejects
the result:

```
error[E0072]: recursive type `expr` has infinite size
```

## 10. The Rust backend references a `lowstar` module it never emits

*Severity 4. Tests: `ExtDatatypesRecord`, `ExtDatatypesVariant`.*

Discriminators and projectors have an unused `projectee` binder, for which the
Rust backend emits

```rust
crate::lowstar::ignore::ignore::<wrapper>(projectee);
```

but the generated crate contains no `lowstar` module:

```
error[E0433]: cannot find `lowstar` in `crate`
```

Any module with a record or a multi-constructor datatype hits this, so it
affects essentially every non-trivial Rust extraction of an inductive.

## 11. A projector applied to a constructor application crashes krml

*Severity 4 — unhandled exception in krml. Test: `ExtProjectorOfCtor`.*

```fstar
let seven : U32.t = 7ul
let main () : U32.t = Circle?.radius (Circle seven)
```

* **C**:
  ```
  Fatal error: exception Failure("Expected a type annotation for:
    (CStar.Struct (None, [((Some "tag"), ...);
      (None, (CStar.Struct (None, [((Some "case_Circle"), ...)])))]))")
  ```
  The anonymous struct literal for `Circle seven` reaches the C printer with
  no type to give the compound literal. krml nonetheless **exits 0**, so a
  build system that only checks the exit status carries on with no output.
* **Rust**: emits `match shape::Circle { radius: seven } { ... }`, which rustc
  rejects with `error: struct literals are not allowed here` — the struct
  literal needs parentheses in a scrutinee position.

Both `let c = Circle seven in Circle?.radius c` and
`match Circle seven with | Circle r -> r | _ -> 0ul` work, which is why every
other module in this directory `let`-binds constructor applications first.

## 12. The Rust backend cannot translate `EFun`, and truncates silently

*Severity 4. Test: `ExtBoolHigherOrder`.*

A lambda passed as an argument gives

```
ERROR translating ExtBoolHigherOrder.main: Failure("unexpected: EFun")
1 total errors
```

after which krml **exits 0** and writes a crate with the offending function
missing. This silent-truncation behaviour is shared with #1 and #11 and is
arguably the most dangerous part: a caller who trusts the exit status gets a
library that is missing definitions. It is why the `rust` rule in the
`Makefile` greps for `krml_main` before invoking rustc.

---

## Things that were checked and are *correct*

Recording these matters as much as the bugs — they are the cells of the matrix
that are now pinned down and will not silently regress.

* **Short-circuiting of `&&` and `||`** survives on all three backends, and so
  does the laziness of `if/then/else`. `ExtBoolShortCircuit` detects a lost
  short circuit as a *crash* (division by zero under a guard) rather than as a
  performance difference, which is the only way a test can see it. Note that
  the short circuit is a property of the syntactic full application: passing
  `&&` as a value yields the strict `Prims.op_AmpAmp`, which is correct but
  worth knowing.
* **Signed and unsigned machine arithmetic** at all four widths: `div`/`rem`
  sign semantics, `add_mod`/`sub_mod`/`mul_mod` wraparound, logical operations,
  shifts, and comparisons (`ExtIntSigned`, `ExtUIntUnsigned`).
* **`FStar.Int.Cast`**: sign extension, zero extension, truncation, and
  same-width sign reinterpretation, plus round trips (`ExtIntCast`) — modulo
  finding #4.
* **Enum-like inductives** (`ExtDatatypesEnum`): tag values, out-of-order
  matches, discriminators, structural equality.
* **Records and single-constructor inductives** (`ExtDatatypesRecord`) on OCaml
  and C, including nested structs and functional update, which must copy.
* **Tagged unions** (`ExtDatatypesVariant`) on OCaml and C, including `option`.
* **`Prims.int`** small-value arithmetic and comparison on OCaml and C
  (`ExtPrimsInt`).

## Notes for whoever extends this

Two behaviours of the toolchain shaped the design of these tests and will bite
anyone adding to them:

* **F\* extraction constant-folds literal `Prims.int` arithmetic and string
  concatenation.** `2 + 2` extracts as `4`, so a test written with inline
  literals is vacuous. Bind operands as top-level `let` constants: those stay
  opaque to extraction but remain delta-reducible for the SMT solver, so the
  expected values can still be proved.
* **Those top-level constants must be literals.** A *computed* global generates
  a `krmlinit_globals` initializer, which C accepts but which is a fatal
  warning 9 for the Rust backend.

See `README.md` for the harness contract.
