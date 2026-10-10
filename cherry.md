# Counting cherries in the custard

Cherry is an extension of custard to support reference counted types. It takes inspiration from Ullrich and de Moura's paper "Counting immutable beans" and from Lean's runtime.
The long-term goal of Cherry is to support extraction of the F* compiler to C, without having to use OCaml.

## Scope and representation

Existing Pulse code will compile and run like now, with no extra overhead. This means that all types are monomorphized and option etc. retain their existing layout without indirection.
Programs that compile with the C backend today should continue to compile without requiring a runtime. Cherry requires a runtime (big integers, closures, etc.).
Native compilation is restricted to a subset of F* that can be compiled to efficient code. In particular, polymorphic recursion is not supported (if the compiler uses it, we will eliminate it).
Some types require reference counting, like pointers to heap cells. This has no effect on their representation, it just means that every type has inc/dec/mark operations and we have to call them when appropriate.
Function arguments and return values keep their current representation. That means using option or either in the return type does not require allocation.
A type is called plain if it does not require refcounting. Bool is plain, so is UInt32.t etc.
Pulse refs/arrays can be allocated uninitialized. This does not work with reference counting, so uninitialized allocation is only allowed for plain types.

## Reference counting

Every heap cell starts with a reference count, using Lean's encoding:
- rc > 0: the cell is single-threaded (only reachable from one thread); inc/dec are regular reads and writes.
- rc < 0: the cell is multi-threaded; inc/dec are atomic operations.
- rc = 0: the cell is immortal (statics, literals); inc/dec do nothing.

So inc/dec is one well-predicted branch on the sign, and the common single-threaded case avoids atomic operations entirely.
All cells start out single-threaded. Marking turns a cell multi-threaded, and recursively marks everything reachable from it. Marking is one-way and stops at cells that are already multi-threaded (or immortal), so its cost is proportional to the newly published part of the object graph. Every type has a mark function, generated the same way as the dec function.
Since only the owning thread can publish a single-threaded cell, a thread that observes a single-threaded rc knows that no other thread can access the cell concurrently.

Freeing and marking never recurse on the C stack, so values of any depth (long lists, deep terms) can be dropped and published:
- A cell is processed by a generated visit function: `cherry_free_T` decs the fields and frees the cell, while `cherry_markf_T` marks the fields. The visit loops on the last field of the cell's own type, so a list spine is walked in place.
- `cherry_dec_T` and `cherry_mark_T` hand the cell and its visit function to `cherry_defer` (cherry.c). It runs the visit at once, unless a walk is already in progress on this thread. In that case it pushes the cell onto that thread's work list, which the outer walk drains. The same applies to closures (drop/mark of the environment) and references (the value).
- The work list is per thread and kept between walks.

Values must be marked when they become reachable from another thread (publication points):
- Storing a value into a Pulse container (Pulse references, Pulse arrays). These containers have no refcount, and Pulse permissions allow multiple threads to read from them concurrently (and then inc the read value). Invariant: everything stored in a Pulse container is multi-threaded. As a consequence, mark functions never need to look inside a Pulse container.
- Storing a value into a mutable cell (reference, mutable array) that is multi-threaded.
- Arguments to thread spawn / par.

There are no weak references. Reference cycles (e.g. through refs) leak; this is acceptable. Cherry must not create cycles on its own though: local `let rec` closures do not capture themselves, they are lambda-lifted (or receive the closure as an argument) like in Lean.
The hash code memo reference in terms is being removed, so terms do not need weak references either.

## Calling convention

Ownership and borrowing of function parameters follows the "Counting immutable beans" paper and Lean.
Every non-plain parameter is either owned (the callee consumes one reference) or borrowed (the caller guarantees the value stays alive for the duration of the call). Plain parameters are neither.
Return values are always owned. This includes the `either exn a` returns used for exceptions.
Unboxed values (structs, option, either, etc.) are passed by value as today. Owned/borrowed applies to the whole value; their inc/dec functions act on each field.
Calls to unknown functions (closures, apply_n) use all-owned parameters. Every function that is used as a value gets a generated `_boxed` wrapper with all-owned parameters, which calls the function with the inferred convention and decrements the borrowed arguments afterwards.
For externals and runtime primitives the convention is declared, not inferred: parameters are borrowed by default, and `[@@cherry_owned]` on a binder makes them owned. For example, string_append takes its first argument owned so that the in-place update can apply. Regular functions can also use `[@@cherry_owned]` and `[@@cherry_borrowed]` on binders to override inference.

## Borrow inference

Borrow inference runs per monomorphized instance, over the strongly connected components of the call graph, until a fixpoint is reached (Counting immutable beans, section 5):
1. Initially, all parameters are borrowed.
2. A parameter is marked owned if:
   - it may be reset/reused (in-place updates of strings, immutable arrays, constructor cells);
   - it is passed to an owned parameter;
   - it is passed to an owned parameter in a tail call. This preserves the tail call, which would otherwise be followed by a dec.
3. Storing a parameter into a constructor, closure, or partial application marks it owned, as in Lean: the stored value is usually consumed, so an owned parameter saves an inc.

Mutual recursion cannot span F* modules, so inference proceeds in module dependency order. The inferred conventions are exported in the module's custard interface (Loader/imports) so that callers in other modules agree with them.

Borrowed locals: a projection of a field of an immutable cell is borrowed for as long as the cell is live, so it needs no inc. Reads from mutable cells (ML references, Pulse references, arrays) are always owned, since a callee could overwrite the cell and free the old value.

Prototype status (`FStarC.Custard.Cherry.infer_borrows`):
- The fixpoint runs over the whole (monomorphized) program at once rather than per SCC. The result is `Cherry.param_owned`, one flag per binder; plain and unit binders are listed as owned.
- The rules are rules 2 and 3 (except reset/reuse, which does not exist yet). Records and tuples count as constructors, and passing a value to a closure call marks it owned. In the tail-call rule, any fresh argument (anything other than a variable or a global) counts as owned.
- Fields bound by a match on a borrowed variable (a borrowed parameter or such a field) are borrowed. They get no inc, and the scrutinee is not dec'd. Record projections (`p.f`) still inc.
- Definitions whose convention other code relies on are pinned to all-owned: imported definitions, and in `--custard_unit` mode, the non-private ones. Interfaces do not carry conventions yet.
- The closure entry of a definition (static closures and partial applications) adapts the conventions. Borrowed captured fields are not inc'd. Borrowed arguments are dec'd after the call, since the entry receives them owned. No separate `_boxed` wrapper is needed.
- Not yet done: `[@@cherry_owned]`/`[@@cherry_borrowed]`, borrowed record projections, and conventions in custard interfaces.

## Inserting reference counting operations

Reference counting operations are inserted in a separate pass on the ANF'd, monomorphized IR, after layout and simplification and before printing C. Doing this in the emitter would make liveness analysis and reuse awkward.
1. Insert reset/reuse for heap cell reuse (requires liveness).
2. Insert inc/dec following the "Counting immutable beans" algorithm: inc when an owned variable is consumed but still live afterwards, dec after its last use if it was not consumed, and in match/if branches dec the variables that are dead at the start of the branch.
3. Clean up: cancel inc/dec pairs, push decs into branches, and specialize dec for constructors known from an enclosing match.

## The any type

The any type is represented as a fat pointer: a pair of a uintptr_t and an RTTI pointer. The RTTI contains the inc, dec, and mark functions (and maybe some inspection functions for debugging). Types that are small enough to fit into a uintptr_t are stored directly, for larger types we allocate a heap cell with a reference count and store the pointer in the uintptr_t.
FStar.Dyn.dyn generates the any type. Casting any to any is the identity (undyn is unchecked, so nothing is lost).

## References

There are two kinds of references. Both are represented as a pointer.
Pulse references (Pulse.Lib.Reference) are plain: they point to a heap cell containing only the contained value. Ownership, freeing, and thread safety fully rely on Pulse's permission system. Stored values are marked (see above). Reading a value increments its refcount, and after a write the old value must have its refcount decremented.
ML references (FStar.Ref etc.) point to a heap cell containing the reference count, a spinlock, and the contained value. If the cell is single-threaded, reads and writes do not touch the spinlock: a read is one read of the rc, one read of the value, plus the inc. If the cell is multi-threaded, reads and writes must acquire the spinlock. One, the value may be too large for atomic operations. Two, we need to increment the refcounts in the value while the spinlock is held; otherwise a writer might decrement and free the value before the reader gets to increment it. Values written into a multi-threaded reference are marked.

The prototype implements ML references as follows:
- Under Cherry, `FStar.All.ref t` and `FStarC.Effect.ref t` extract to the runtime type `Cherry.ref t` rather than to `TRef t`, which stays the plain pointer of Pulse references and boxes. The operations are the usual buffer operations, which the Cherry pass rewrites into `RefNew v` (takes `v`), `RefGet r` (borrows `r`, returns an owned copy of the value) and `RefSet r v` (borrows `r`, takes `v`, releases the old value).
- In C every ML reference is a `cherry_ref` (`cherry.h`), so the header needs nothing generated. For each value type the printer generates the cell (`struct cherry_refN_s { cherry_ref_hdr h; T v; }`) and `cherry_refN_new/get/set/dec/mark`. A cell whose count is not positive (shared, or persistent because a global reaches it) is accessed under its spinlock, and a value written into one is marked shared first.
- A reference is a pointer, so a type that reaches itself through one is not boxed, and the C type order ignores what a reference holds.
- Pulse references and arrays holding counted values are rejected for now.

## Functions

When extracting with Cherry, all function values are reference counted closures: a heap cell with the reference count, a function pointer, the arity, and the closed over values. The regular C backend still emits function types as function pointers, since tools like EverParse rely on that.
Top-level functions used as values become static immortal closures, so they require no allocation. Known saturated calls to top-level functions remain direct calls.
F* functions are curried; calls to unknown closures go through generic apply_n helpers that compare the number of arguments to the arity and handle partial and over-application (like Lean's lean_apply_n).
For now, every function type is a reference counted closure; there are no closures whose ownership is tracked by Pulse permissions. Closures are therefore not Pulse containers, but values captured by a closure are marked when the closure itself is marked.

The prototype implements this as follows:
- The Cherry pass lambda-lifts every lambda to a private top-level function taking the captured variables first, and the lambda becomes the partial application of that function to them. Externals used as values or partially applied get a wrapper definition the same way, and over-applications of known functions are split into a saturated call followed by a closure call. Afterwards a function value is a function's name (a static closure), a partial application of a known function, or a variable.
- `cherry.h` defines the closure cell (`cherry_closure`: header, entry point, drop and mark functions, arity, then the environment). The entry point takes the closure borrowed and the arguments owned.
- For each partially applied function and number of arguments, the printer generates an environment struct, an entry point (which increments the captured values and calls the function), drop/mark functions and a constructor. For each closure type and number of arguments it generates `cherry_apply_T_k`, which switches on the arity: an exact call, a call followed by applying the result to the remaining arguments, or a new closure capturing the arguments given so far. Helpers are generated on demand from a worklist.
- Arity counts only the non-unit parameters. Custard drops unit parameters from definitions (Mono's rule 1) while the function types at use sites keep them, so this is the only count on which a definition and its type agree; it is also the one the C backend uses for function pointers.
- A closure call borrows the closure and takes the arguments owned; a partial application takes its arguments owned.
- A global of function type holds a closure (persistent, see Globals), so a call through it is a closure call.

## Inductive types

Inductive types can be tagged as custard_boxed. Then they are allocated on the heap so that they fit in a pointer. Constructors without fields (None, Nil, etc.) are stored directly as scalars without a heap allocation (e.g. `(n << 1) | 1`, like Lean). The other constructors are stored in heap cells, which have different sizes depending on the fields.
The constructor number is always stored in the heap cell header. Storing it in the pointer tag as well is an optional fast path (there are only 3 low tag bits, and the high bits are not available on 32-bit or with 5-level paging), e.g. for types with few constructors.
Recursive types are automatically custard_boxed.

## Integers, strings, exceptions

Integers are stored with tagged pointers. Small integers are stored directly (`(n << 1) | 1`, 63 bits on 64-bit targets). Large integers are stored in a heap cell with a reference count, a sign, and 32-bit limbs. Values are canonical: a number that fits in a small integer is never a cell, so equality is a pointer comparison unless both are cells. Arithmetic has inline fast paths for two small operands; `/` and `%` are Euclidean, as in F\*. Literals with absolute value below 2^30 are small on every target; larger ones are allocated where they are evaluated (`cherry_int_of_decimal`) and counted like any other value.
Strings follow Lean: a heap cell with the reference count, byte size, capacity, and zero-terminated UTF-8 data. Appends and other updates use the functional-but-in-place optimization: if the string is uniquely owned and has enough capacity, it is modified in place, otherwise a copy with geometrically grown capacity is allocated. This makes repeated appends cheap without source changes, at the cost of some slack memory. String literals are emitted as immortal static cells. `String.length`, `index` and `sub` count code points, so they walk the UTF-8 data.
Zero-terminated C strings with static lifetime (e.g. C.String for the existing C backend) remain a separate F* type.
Exceptions are out of scope for the initial version. They will be implemented using error returns, probably by returning `either exn a`.
Values of the exn type are stored as pointers to heap cells containing the reference count, RTTI, and field values. Exn is an open type, so we need RTTI to determine which exception it is and to decrement/mark the fields.

## Arrays

There are three array kinds:
- Pulse arrays (Pulse.Lib.Array): same memory layout as now, plain, ownership tracked by Pulse permissions. Stored values are marked.
- Mutable reference counted arrays (FStarC.Array): can grow, stored as rc + capacity + length + data array. Accessed like ML references (spinlock only if multi-threaded).
- Immutable arrays (FStar.ImmutableArray): stored like strings, as rc + capacity + length + data array. Updates and appends use the functional-but-in-place optimization: if the array is uniquely owned (and, for appends, has enough capacity), it is modified in place, otherwise a copy (with geometrically grown capacity for appends) is allocated.

## Globals

Globals (like `let foo = [1;2]`) are stored as immortal (rc = 0) static cells without requiring an initializer. Since inc/dec never write to immortal cells, immutable globals can be put in .rodata.
Storing objects in read-only mmapped files (like Lean's .olean files) is out of scope for now.

The prototype does not build static cells yet. Instead, a global of reference-counted type is computed by the unit's initialization function like any other global, and is then made persistent: `cherry_mark_T(g, CHERRY_PERSIST)` sets the count of every cell reachable from it to 0, stopping at cells that are already immortal. Mark functions therefore take a mode, `CHERRY_SHARE` (make multi-threaded) or `CHERRY_PERSIST`. Reading a global (`EQual` of a global) is then free: the Cherry pass treats it like a function name, as a value that needs no inc and no dec. Building literal globals as static cells at compile time is a later optimization that removes the initialization cost.

## Heap cell reuse

Heap cells are reused opportunistically. Due to the nonuniform memory layout, we only reuse cells for the same constructor (with the same monomorphized type). Unlike Lean, we do not add a branch on rc=1 to the IR; instead a variant of the decrement operation returns a pointer to the recyclable heap cell (if uniquely owned, i.e. rc = 1 or rc = -1) without freeing it, or null otherwise. The fields of the recyclable cell are decremented eagerly. The cell is then reused by following allocations where appropriate, and must be freed on paths where it is not reused. Immortal cells are never reused.

## Backend

Cherry is a separate backend, `--custard_backend Cherry`, which shares most of its code with `--custard_backend C`. It is separate because it needs runtime support, extra includes, and generated auxiliary functions (inc/dec/mark functions, RTTI, `_boxed` wrappers, apply_n helpers). Since reference counting operations are inserted in a separate IR pass, the shared emitter needs only minor changes; the generated boilerplate is new code that does not affect the existing C pipeline. The runtime itself (cell header, inc/dec/mark primitives, integers, strings, closures) is not generated: it is the hand-written `ulib/c/cherry.h` (types and inline fast paths) and `ulib/c/cherry.c` (slow paths: big integer arithmetic, string operations), distributed with F\*. Generated units `#include "cherry.h"`; users add `$(fstar.exe --locate_lib)/ulib/c` to the include path and compile and link `cherry.c` with the program.
The Cherry pass maps the F\* primitives on `Prims.int` and `Prims.string` (arithmetic, comparisons, `strcat`, `string_of_int`, `FStar.String.{strlen,index,sub,compare}`, `FStar.IO.print_string`) to runtime functions, with per-argument ownership: they borrow their arguments, except `strcat`, which takes its first argument owned so that it can append in place.
