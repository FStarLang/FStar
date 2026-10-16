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
All cells start out single-threaded. Marking turns a cell multi-threaded, and recursively marks everything reachable from it. Marking is one-way and stops at cells that are already multi-threaded (or immortal). Every access to a count is atomic (relaxed loads and stores on the fast paths, which compile to plain moves), so that the program has no data races in the C11 sense, so its cost is proportional to the newly published part of the object graph. Every type has a mark function, generated the same way as the dec function.
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
Return values are always owned. A function that returns with an exception pending (see "Exceptions") returns no value: its result is never read or released.
Unboxed values (structs, option, either, etc.) are passed by value as today. Owned/borrowed applies to the whole value; their inc/dec functions act on each field.
Calls to unknown functions (closures, apply_n) use all-owned parameters. Every function that is used as a value gets a generated `_boxed` wrapper with all-owned parameters, which calls the function with the inferred convention and decrements the borrowed arguments afterwards.
For externals and runtime primitives the convention is declared, not inferred: parameters are borrowed by default, and `[@@cherry_owned]` on a binder makes them owned. For example, string_append takes its first argument owned so that the in-place update can apply. Regular functions can also use `[@@@cherry_owned]` and `[@@@cherry_borrowed]` (from `FStar.Attributes`) on binders to override inference, e.g. `let push ([@@@cherry_owned] l: list int) = ...`.

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
- Fields bound by a match on a borrowed variable (a borrowed parameter or such a field) are borrowed. They get no inc, and the scrutinee is not dec'd. Likewise a let-bound record projection (`let x = p.f`, or a chain `p.f.g`) of a borrowed variable is borrowed; projections in argument position are let-bound first, so `length p.f` costs nothing. A projection is inc'd only where it is stored or returned.
- Imported definitions are pinned to the convention recorded in their unit's interface: the `.cui` gives each definition a `CherryConv` flag, one owned/borrowed bit per binder, after inference. An imported definition without the flag (a unit compiled for plain C) is taken as all-owned. A unit's exported definitions are inferred like any other.
- `[@@@cherry_owned]`/`[@@@cherry_borrowed]` on a binder fix that parameter's convention (Extract records them positionally as a `CherryMode` flag), and the fixpoint never changes it. Both are always sound, since the rc pass incs a borrowed parameter where it is stored and decs an owned one where it dies. Both on one binder is warning 371, and both are ignored. They still feed inference elsewhere: an owned parameter passed on in a tail call makes the callee's parameter owned.
- The closure entry of a definition (static closures and partial applications) adapts the conventions. Borrowed captured fields are not inc'd. Borrowed arguments are dec'd after the call, since the entry receives them owned. No separate `_boxed` wrapper is needed.
- Externals borrow every argument by default. The runtime's own externals take their conventions from a table in `Cherry.runtime_externals`; any other external can say `[@@@cherry_owned]` on a binder of its type (`assume val f : ([@@@cherry_owned] s: string) -> ML t`), and then the C function receives a reference it must release. Test: `tests/custard/CherryExtOwn.fst`, whose owned stub calls `cherry_dec`.

## Inserting reference counting operations

Reference counting operations are inserted in a separate pass on the ANF'd, monomorphized IR, after layout and simplification and before printing C. Doing this in the emitter would make liveness analysis and reuse awkward.
1. Insert reset/reuse for heap cell reuse (requires liveness).
2. Insert inc/dec following the "Counting immutable beans" algorithm: inc when an owned variable is consumed but still live afterwards, dec after its last use if it was not consumed, and in match/if branches dec the variables that are dead at the start of the branch.
3. Clean up: cancel inc/dec pairs, push decs into branches, and specialize dec for constructors known from an enclosing match.

## The any type

The any type is represented as a fat pointer: a pair of a uintptr_t and an RTTI pointer. The RTTI contains the inc, dec, and mark functions (and maybe some inspection functions for debugging). Types that are small enough to fit into a uintptr_t are stored directly, for larger types we allocate a heap cell with a reference count and store the pointer in the uintptr_t.
FStar.Dyn.dyn generates the any type. Casting any to any is the identity (undyn is unchecked, so nothing is lost).

Prototype status: under Cherry, `dyn` extracts to the IR's `TAny` (the type of values whose representation was lost elsewhere), which prints as `cherry_any` (`{uintptr_t v; const cherry_rtti *rtti}`), and `mkdyn`/`undyn` become ops that are monomorphized per payload type. Each payload type gets `cherry_anyN_mk`/`_get` helpers and a static `cherry_rtti`. The RTTI holds the payload's name and its inc, dec and mark functions. For a plain payload they only count or mark the box when the payload is stored in one (see below), and do nothing when it is inline. `mkdyn` takes its operand owned and `undyn` borrows. A payload with `sizeof(T) <= sizeof(uintptr_t)` is stored inline; a larger one is stored in a counted cell. The prototype keeps undyn checked: `_get` compares the RTTI pointer and aborts with both type names on a mismatch. RTTIs are per-unit statics, so a `dyn` made in another unit carries that unit's RTTI; `_get` then falls back to comparing the C type names (see "Separate compilation"). `FStar.Dyn.fst` models `dyn` as an arrow abbreviation, so extraction keeps the folded codomain of a definition's type, and a global or result of type `dyn` stays `dyn`. Test: `tests/custard/CherryDyn.fst`.

Extraction also produces `TAny` where OCaml would use `Obj.t`: dependent types (`if b then int else bool`), type-level computations (a printf whose type is computed from its format), and method types that are polymorphic in their own right. OCaml can ignore the mismatch between `any` and the real type, but C cannot. The Cherry pass therefore lowers every coercion between `any` and a concrete type to `Dyn mk`/`get` (`lower_any`), and makes the IR's types agree first:
- A type variable that monomorphization left standing (e.g. the `'a` of `ret : #a:Type -> a -> m a`) becomes `any`.
- A pattern variable bound from an `any` field is typed `any` in its branch, so that the coercion out of it is not taken for a no-op.
- An application is typed by its head. Where the head returns `any` and extraction typed the call concretely, the result is coerced. Where extraction typed the call `any` and the head knows better, the call keeps the head's type and its consumer coerces it.
- The arms of an `if` or `match` typed `any` are coerced to `any`, and a function body to its declared result type.
- A closure stored in `any` is stored at its uniform type, with every parameter and the result `any`. A coercion between arrow types builds an adapting lambda that coerces each argument and the result. If the source arrow takes fewer parameters than the target, the adapter applies the source to the first ones and adapts the closure it returns to the rest.

`tests/custard/AnyLambda`, `AnyCond`, `HigherKind`, `RetArity` and `Combinators` cover these.

## References

There are two kinds of references. Both are represented as a pointer.
Pulse references (Pulse.Lib.Reference) are plain: they point to a heap cell containing only the contained value. Ownership, freeing, and thread safety fully rely on Pulse's permission system. Stored values are marked (see above). Reading a value increments its refcount, and after a write the old value must have its refcount decremented.
ML references (FStar.Ref etc.) point to a heap cell containing the reference count, a spinlock, and the contained value. If the cell is single-threaded, reads and writes do not touch the spinlock: a read is one read of the rc, one read of the value, plus the inc. If the cell is multi-threaded, reads and writes must acquire the spinlock. One, the value may be too large for atomic operations. Two, we need to increment the refcounts in the value while the spinlock is held; otherwise a writer might decrement and free the value before the reader gets to increment it. Values written into a multi-threaded reference are marked.

The prototype implements ML references as follows:
- In the IR the two kinds are separate: `TRef (RGc, t)` is a garbage-collected (ML) reference and `TRef (RManual, t)` a manually managed (Pulse) one. `FStar.All.ref t` and `FStarC.Effect.ref t` extract to `TRef (RGc, t)` under every backend. The OCaml and F# backends print both kinds as their native `ref`. Direct C, KrmlC and KrmlRust reject `RGc`, since they have no collector, and the error points to Pulse references or `--codegen Cherry`. Under Cherry the operations are the usual buffer operations, which the Cherry pass rewrites into `RefNew v` (takes `v`), `RefGet r` (borrows `r`, returns an owned copy of the value) and `RefSet r v` (borrows `r`, takes `v`, releases the old value).
- In C every ML reference is a `cherry_ref` (`cherry.h`), so the header needs nothing generated. For each value type the printer generates the cell (`struct cherry_refN_s { cherry_ref_hdr h; T v; }`) and `cherry_refN_new/get/set/dec/mark`. A cell whose count is not positive (shared, or persistent because a global reaches it) is accessed under its spinlock, and a value written into one is marked shared first.
- A reference is a pointer, so a type that reaches itself through one is not boxed, and the C type order ignores what a reference holds.

The prototype implements Pulse references and arrays holding counted values (`TRef t` and `TBuf t` with `t` counted) as follows:
- The Cherry pass rewrites their buffer operations into `PBuf` nodes, and the printer generates `cherry_pbufN_{alloc,init,read,write,free,drop,blit}` for each element type. `read` borrows the container and returns an owned copy. `write` takes the value, marks it shared, and releases the old one. `blit` (`Pulse.Lib.ArrayPtr.memcpy`) increments the source range before it releases the destination range, so overlapping ranges are safe. A value is marked shared whenever it is stored, so reads only need an atomic inc and never take a lock.
- A heap allocation (`Box.alloc`, `Vec.alloc`, an `Array.alloc` that escapes) puts the length in a header in front of the elements (`cherry_pbuf_new` in `cherry.h`). That way `free` can release the elements wherever the container ends up being freed. The pointer Pulse sees is to the first element, so the layout is otherwise unchanged.
- A stack allocation (`let mut`, `[| v; n |]`, an `alloc`/`free` pair promoted to the stack) is declared without an initializer and filled by `init`, which takes the value. `drop` releases the cells when the scope ends. Pulse code does not raise, so nothing leaves the scope early.
- Uninitialized allocation (`Reference.alloc_uninit`, `Array.mask_alloc`) of counted values is rejected, and so is a constant array of them.
- `tests/custard/pulse/CherryPulse.fst` covers stack and heap references, boxes, arrays and vectors freed in another function, zero-length arrays, `memcpy` and `ArrayPtr.memcpy`. `CherryPulseUninit.fst` covers the rejection. The Pulse suite also runs every direct-C test through Cherry under ASan.

## Functions

When extracting with Cherry, all function values are reference counted closures: a heap cell with the reference count, a function pointer, the arity, and the closed over values. The regular C backend still emits function types as function pointers, since tools like EverParse rely on that.
Top-level functions used as values become static immortal closures, so they require no allocation. Known saturated calls to top-level functions remain direct calls.
F* functions are curried; calls to unknown closures go through generic apply_n helpers that compare the number of arguments to the arity and handle partial and over-application (like Lean's lean_apply_n).
For now, every function type is a reference counted closure; there are no closures whose ownership is tracked by Pulse permissions. Closures are therefore not Pulse containers, but values captured by a closure are marked when the closure itself is marked.

The prototype implements this as follows:
- The Cherry pass lambda-lifts every lambda to a private top-level function taking the captured variables first, and the lambda becomes the partial application of that function to them. Externals used as values or partially applied get a wrapper definition the same way, and over-applications of known functions are split into a saturated call followed by a closure call. Afterwards a function value is a function's name (a static closure), a partial application of a known function, or a variable.
- `cherry.h` defines the closure cell (`cherry_closure`: header, entry point, drop and mark functions, arity, then the environment). The entry point takes the closure borrowed and the arguments owned.
- For each partially applied function and number of arguments, the printer generates an environment struct, an entry point (which increments the captured values and calls the function), drop/mark functions and a constructor. For each closure type and number of arguments it generates `cherry_apply_T_k`, which switches on the arity: an exact call, a call followed by applying the result to the remaining arguments, or a new closure capturing the arguments given so far. Helpers are generated on demand from a worklist.
- Arity counts only the non-unit parameters. Custard drops unit parameters from definitions (Mono's rule 1) while the function types at use sites keep them, so this is the only count on which a definition and its type agree; it is also the one the C backend uses for function pointers. A call site counts a unit parameter as supplied when the next argument is not a unit, and skips a unit argument that has no parameter.
- A closure whose remaining parameters are all units (a thunk, or a partial application that leaves only units) gets the arity `CHERRY_ARITY_UNITS`, not 0. Applying it to no further arguments returns it unchanged if the type says that more arrows follow, and runs it otherwise. With arity 0, a partial application `f x` of `f x ()` would run `f` early.
- As on OCaml, closures are polymorphic, so erased binders stay in a lambda as unit parameters (`heap_closures` in Extract). Otherwise the same closure would have different arities at different types.
- A self tail call in a definition becomes a jump to its start (`goto custard_tail`), so tail-recursive loops run in constant stack.
- A closure call borrows the closure and takes the arguments owned; a partial application takes its arguments owned.
- A global of function type holds a closure (persistent, see Globals), so a call through it is a closure call. This includes the exception test after it: whether the global's initializer raises says nothing about whether the closure does.

## Inductive types

Inductive types can be tagged as custard_boxed. Then they are allocated on the heap so that they fit in a pointer. Constructors without fields (None, Nil, etc.) are stored directly as scalars without a heap allocation (e.g. `(n << 1) | 1`, like Lean). The other constructors are stored in heap cells, which have different sizes depending on the fields.
The constructor number is always stored in the heap cell header. Storing it in the pointer tag as well is an optional fast path (there are only 3 low tag bits, and the high bits are not available on 32-bit or with 5-level paging), e.g. for types with few constructors.
Recursive types are automatically custard_boxed.
Custard turns every single-constructor type into a record. A recursive record (e.g. `type tree = Node : int -> forest -> tree`) is boxed as a variant with the single constructor `Mk_tree`, so it shares the code path of other boxed types. Projections out of it read the cell's field.

Structural equality (`=` at a type with decidable equality) borrows both operands and is generated per type, as in the C backend. For a boxed type, `T__eq` first checks for the same pointer (which also covers equal scalars), then compares tags and the fields of the cell. The last field of the cell's own type is compared by looping rather than by a recursive call, so two long lists compare in constant stack; other recursive fields, such as the left subtree of a tree, still recurse. Integers and strings compare by value through the runtime.

## Integers, strings, exceptions

Integers are stored with tagged pointers. Small integers are stored directly (`(n << 1) | 1`, 63 bits on 64-bit targets). Large integers are stored in a heap cell with a reference count, a sign, and 32-bit limbs. Values are canonical: a number that fits in a small integer is never a cell, so equality is a pointer comparison unless both are cells. Arithmetic has inline fast paths for two small operands; `/` and `%` are Euclidean, as in F\*. Literals with absolute value below 2^30 are small on every target; larger ones are allocated where they are evaluated (`cherry_int_of_decimal`) and counted like any other value. A constant pattern of that size is tested with `cherry_int_eq_decimal`, which builds the literal, compares and releases it. With `--custard_int128` (on by default), conversions between `Prims.int` and the 128-bit integers go through 128-bit runtime conversions (`cherry_int_of_u128` etc.), and the others through the 64-bit ones. Test: `tests/custard/CherryEdge.fst`.
Strings follow Lean: a heap cell with the reference count, byte size, capacity, and zero-terminated UTF-8 data. Appends and other updates use the functional-but-in-place optimization: if the string is uniquely owned and has enough capacity, it is modified in place, otherwise a copy with geometrically grown capacity is allocated. This makes repeated appends cheap without source changes, at the cost of some slack memory. String literals are emitted as immortal static cells. `String.length`, `index` and `sub` count code points, so they walk the UTF-8 data.
Zero-terminated C strings with static lifetime (e.g. C.String for the existing C backend) remain a separate F* type.
Values of the exn type are stored as pointers to heap cells containing the reference count, RTTI, and field values. Exn is an open type, so we need RTTI to determine which exception it is and to decrement/mark the fields.

### Exceptions

Exceptions use error returns. Instead of returning `either exn a`, which would change every signature and box every result, a raise stores the exception in a thread-local slot (`cherry_exn_slot`) and returns. The function's result is a dummy that is never read or released.
- A call that may raise is followed by a test of the slot, marked unlikely. If an exception is pending, the caller releases the owned references it holds and returns in turn. These include the references held by enclosing `let` continuations, not only the call's own operands.
- A call in tail position is not tested: the dummy result is passed on, and the caller tests.
- `try e with brs` becomes a call of `e`'s body, lifted into its own function with its free variables as parameters. If the slot is set after the call, the exception is taken out of it and matched against `brs`, plus a final branch that raises it again.

A fixpoint over the program finds the definitions that may raise. A definition may raise if it is not total and it raises, has a `try` (which can re-raise), or calls something that may raise. Calls that may raise are those to impure imported definitions and to impure closures. Total definitions and calls to externals are never tested.
A heap cell reuse token whose reuse comes after a possible raise is freed on that exit path.

Each exception constructor gets a cell `{ header, info, f0, f1, ... }`. The info is a static `cherry_exn_info` with the name, a free function and a mark function, so the runtime can release and mark exceptions of any constructor. A handler pattern compares the `info` pointer. Nullary exceptions are cells too, so every exception has an info. The closure `apply` helpers test the slot between the partial calls of an over-application. An exception that reaches `main`, or escapes a global's initializer, prints `Uncaught exception: Name` and exits with status 2. If the exception's first field is a string, the message is printed too, as in `Uncaught exception: FStar.All.Failure("msg")`.
`failwith s` (from `FStar.All` or `FStarC.Effect`) raises `Failure s`, so it can be caught like any other exception. If the program has no declaration of `Failure`, one is added.

Prototype status: implemented as above. Each unit has its own static info for every exception it raises or matches, so `cherry_exn_is` compares the info pointer first and the F\* name second (see "Separate compilation"). A `raise` is typed at the type F\* instantiated it at, so a lambda whose body is just a `raise` keeps its result type. `tests/custard/CherryExn.fst` covers:
- raises through deep non-tail recursion that holds lists;
- re-raising through nested handlers, and raising from a handler;
- raises through closures and over-application;
- reuse tokens on raising paths;
- references mutated before a raise;
- a global's initializer;
- `failwith` caught as `Failure`.

## Arrays

There are three array kinds:
- Pulse arrays (Pulse.Lib.Array): same memory layout as now, plain, ownership tracked by Pulse permissions. Stored values are marked. A heap array of counted values carries its length in a header in front of the elements (see "References").
- Mutable reference counted arrays (FStarC.Array): can grow, stored as rc + capacity + length + data array. Accessed like ML references (spinlock only if multi-threaded).
- Immutable arrays (FStar.ImmutableArray): stored like strings, as rc + capacity + length + data array. Updates and appends use the functional-but-in-place optimization: if the array is uniquely owned (and, for appends, has enough capacity), it is modified in place, otherwise a copy (with geometrically grown capacity for appends) is allocated.

Prototype status: immutable arrays are implemented. `FStar.ImmutableArray` gains `upd` and `push` (with spec lemmas; the OCaml realization copies). Under Cherry, `FStar.ImmutableArray.t a` is the IR type `FStar.ImmutableArray.Base.t a`, which prints as `cherry_iarray` (in `cherry.h`: header, size, capacity, then the elements), and its operations become `IArr` nodes. For each element type the backend generates `cherry_iarrN_{of_list,to_list,index,upd,push,dec,mark}`. `length`, `index` and `to_list` borrow the array. `upd` and `push` take it owned and update it in place when `rc == 1`; a full array is `realloc`ed to capacity `2n+1`. Any other array, shared or persistent (such as a global), is copied: the copy increments every element, and then the original is released. Freeing and marking go through `cherry_defer`, like other cells. Structural equality on arrays is rejected for now. `tests/custard/CherryIArray.fst` covers 10^6 in-place pushes and updates, copying of shared and global arrays, counted elements, and nested arrays.

## Globals

Globals (like `let foo = [1;2]`) are stored as immortal (rc = 0) static cells without requiring an initializer. Since inc/dec never write to immortal cells, immutable globals can be put in .rodata.
Storing objects in read-only mmapped files (like Lean's .olean files) is out of scope for now.

The prototype does not build static cells yet. Instead, a global of reference-counted type is computed by the unit's initialization function like any other global, and is then made persistent: `cherry_mark_T(g, CHERRY_PERSIST)` sets the count of every cell reachable from it to 0, stopping at cells that are already immortal or shared. A shared cell stays shared, because other threads may already be counting it; the reference the global holds is never dropped, so it lives as long as an immortal one. Mark functions therefore take a mode, `CHERRY_SHARE` (make multi-threaded) or `CHERRY_PERSIST`. Reading a global (`EQual` of a global) is then free: the Cherry pass treats it like a function name, as a value that needs no inc and no dec. Building literal globals as static cells at compile time is a later optimization that removes the initialization cost.

## Heap cell reuse

Heap cells are reused as in Lean (Counting immutable beans, section 4). When a branch of a match on an owned cell `x` no longer needs `x`, and builds a cell of the same type on some path, the Cherry pass:
- binds a token `w = reset x` at the start of the branch;
- builds the first such cell on each path with `reuse w`;
- frees the token on the paths that build none.

A loop body is not searched, since it may build any number of cells.

- `reset x`: if `x` is unique (rc = 1), the fields the branch uses are moved out of it (no inc), the others are released, and `x`'s memory becomes the token. Otherwise the used fields are inc'd, `x` is dec'd, and the token is null. A shared cell (rc < 0) is never reused, because its fields are shared too and the rebuilt cell's would not be. Immortal cells (rc = 0) are never reused either.
- `reuse w` builds any constructor of the same monomorphized type. If the token is non-null and the new cell fits in the old one (a `sizeof` comparison that the C compiler folds), the cell is updated in place: tag and fields. Otherwise the token is freed and a new cell is allocated.
- Borrow inference makes a parameter owned when such a branch could reuse it (rule 2).
- The fields of `x` must be bound by variables, or by patterns that bind none (e.g. `Node Leaf s Leaf`), so that the reset can tell which fields are kept.

On a microbenchmark (repeatedly mapping over a list of 10^6 elements), reuse is about 2.3x faster than allocating.

Not done yet: reuse of boxed records, reusing a cell for a constructor of another type of the same size, and reuse without a match (Lean's reuse of a dead variable that was not matched on).

## Separate compilation

Cherry supports `--custard_unit`/`--custard_link` like the C backend. A unit's header exposes the cell structs and constructor tags of its types. Every helper Cherry generates (inc/dec/mark/free, constructors, reuse, equality, exception and any helpers) is `static`, so a consumer generates its own copy for each imported type it uses rather than importing one. All copies agree because they are generated from the same layout. Calling conventions across the boundary are the inferred ones, recorded in the unit's `.cui` (see "Borrow inference"), and a consumer assumes every imported impure function may raise.

Two kinds of runtime identity are per unit, and the runtime matches them by name:
- **Exception info:** every unit that raises or matches an exception has its own `cherry_exn_info`. `cherry_exn_is` compares the pointers and then the F\* names, which are unique in a program. No single unit owns `FStar.All.Failure`, so an owning unit would not work.
- **`dyn` RTTI:** `cherry_anyN_get` compares the RTTI pointer, then the C type names (a monomorphized type has one C name program-wide) before aborting.

The slow path costs a `strcmp`, only when values cross units, and only when matching exceptions or reading a `dyn`. Test: `tests/custard/CherrySepLib.fst` and `CherrySepApp.fst`, which pass lists, globals, closures in both directions, exceptions raised through the other unit, refs, immutable arrays, equality on imported types and `dyn` values across the boundary.

## Programs and tests

`--custard_main M.main` makes the program's `main` call `M.main` after the units are initialized. A module whose top-level effects (`let _ = ...`) run code gets a `main` that runs them.
F\* modules that the OCaml backend links as hand-written realizations, but whose F\* source is good enough, are compiled from source under Cherry (`Builtins.cherry_source_modules`: `FStar.List`, `FStar.List.Tot.Base`, `FStar.Option`). The rest are implemented in `cherry.c`: the `Prims.int` and `Prims.string` primitives, `string_of_bool`, `FStar.IO.print_newline`, `FStar.Parse`, the machine integers' `v`/`to_string`, and the conversions between `Prims.int` and the machine integers. A guarded branch `p when g -> b` becomes a wildcard branch `_ -> if (match x with p -> g | _ -> false) then (match x with p -> b) else rest`, where `rest` is the match on the remaining branches, so `rest` appears once and the code grows linearly with the number of guards.

Tests:
- `tests/custard` runs its Cherry tests (`CHERRY_TESTS`) and the direct-C tests through Cherry under ASan and UBSan. It also runs each OCaml-run test (`CUSTARD_TESTS`) through Cherry and compares the output with the same `.out.expected` (`.chdiff`). Nine of those are skipped (`CHERRY_OCAML_SKIP`): they use OCaml functors, realizations written only for OCaml, `reify`, an effect whose box type is a function, or a constructor matched out of `any` at an instance that only its uses determine.
- `tests/custard/pulse` runs the Pulse tests through Cherry.
- `make run-cherry` in `tests/extraction`, `tests/bug-reports/closed`, `examples/printf` and `examples/algorithms` runs every test those directories run on OCaml through Cherry and diffs against the same expected output (`mk/test.mk`; `NO_CHERRY` lists exclusions).
- `tests/extraction/backends` has a Cherry column.
- `pulse/test/pool/pulse_task` builds the parallel quicksort on Pulse's task pool (`Pulse.Lib.Task`) with Cherry as well as OCaml (`make run-cherry`, part of `make test`), and runs it under ASan and UBSan with 32 worker threads. Its C realizations are in `c/`. `Pulse_Lib_Core_fork_core` marks the closure shared (`cherry_mark_fn(f, CHERRY_SHARE)`), takes a reference to it for the new thread, and runs it on a detached pthread, which calls it with `cherry_call_thunk` (cherry.h) and then drops it. The spin lock is the C realization of `Pulse.Lib.SpinLock` from the DICE example. Every task closure and result goes through a Pulse box, so it is marked when it is stored and counted atomically from then on.

## Benchmarks

`tests/custard/bench` builds the same F* programs with Cherry (`gcc -O2`, system malloc), the OCaml backend (OCaml 5.3, no flambda) and the F# backend (.NET 10, Release), and times them: `make bench` (`RUNS`, `BACKENDS`, `BENCHES` select). It is not part of `make test`. Each program checks its own result. Every run gets a 1 GB stack, OCaml 5's default limit, because some of the recursion is not tail calls. All arithmetic is on `Prims.int`, as in the compiler: Cherry uses tagged small ints, OCaml uses Zarith, and F# uses BigInteger.

The programs:
- RBMap: Koka/Lean red-black tree, 10^6 inserts.
- BinaryTrees: Benchmarks Game, depth 20.
- CFold: Koka constant folding, 16 expressions of depth 16.
- NQueens: Koka, n = 13, all solutions as shared lists.
- Strings: number formatting, and joining by `acc ^ x`.
- Closures: map, filter and fold over closures.

Results on a 72-core x86-64 machine: median of 5 runs, with the ratio to OCaml (lower is faster), and peak RSS in MB. `make bench` also runs Cherry's executables with mimalloc (3.2) and jemalloc (5.3) through `LD_PRELOAD` when they are installed.

| Benchmark | Cherry (s) | Cherry (mimalloc) (s) | Cherry (jemalloc) (s) | OCaml (s) | F# (s) | Cherry RSS | Cherry (mimalloc) RSS | Cherry (jemalloc) RSS | OCaml RSS | F# RSS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| RBMap | 0.567 (1.69x) | 0.475 (1.41x) | 0.472 (1.41x) | 0.336 | 3.249 (9.68x) | 62 | 48 | 51 | 53 | 108 |
| BinaryTrees | 14.279 (2.48x) | 6.364 (1.10x) | 8.991 (1.56x) | 5.762 | 45.059 (7.82x) | 129 | 161 | 151 | 143 | 290 |
| CFold | 0.241 (1.11x) | 0.149 (0.69x) | 0.206 (0.95x) | 0.218 | 1.314 (6.04x) | 14 | 14 | 16 | 20 | 87 |
| NQueens | 2.165 (0.30x) | 1.949 (0.27x) | 1.968 (0.28x) | 7.109 | 12.430 (1.75x) | 127 | 130 | 134 | 183 | 370 |
| Strings | 0.105 (0.11x) | 0.079 (0.08x) | 0.101 (0.11x) | 0.942 | 0.889 (0.94x) | 2 | 7 | 7 | 11 | 42 |
| Closures | 0.592 (1.13x) | 0.470 (0.90x) | 0.520 (1.00x) | 0.522 | 0.699 (1.34x) | 1 | 7 | 7 | 7 | 40 |

Cherry wins where values are reused in place (Strings, where `acc ^ x` appends to a unique string) or where many cells are shared and long-lived (NQueens, where OCaml's major GC keeps rescanning them). Where cells are allocated and freed at a high rate (BinaryTrees, RBMap), the cost is mostly the allocator. With glibc's `malloc`, about 60% of BinaryTrees' time is in libc and it takes 2.5x OCaml's time; with mimalloc it takes 1.1x. mimalloc is the best of the three everywhere, so the runtime should link it or a size-class free-list allocator of its own, like Lean's small-object allocator. RBMap stays 1.4x slower than OCaml with every allocator. Its inserts rebuild a path whose old cells are freed one by one, and they do not reuse them in place yet, because the balance functions match nested cells. The UTF-8 `String.strlen`/`String.sub` of the OCaml library are linear, so the Strings benchmark avoids them.

## Backend

Cherry is a separate backend, `--codegen Cherry`, which shares most of its code with `--codegen C`. It is separate because it needs runtime support, extra includes, and generated auxiliary functions (inc/dec/mark functions, RTTI, `_boxed` wrappers, apply_n helpers). Since reference counting operations are inserted in a separate IR pass, the shared emitter needs only minor changes; the generated boilerplate is new code that does not affect the existing C pipeline. The runtime itself (cell header, inc/dec/mark primitives, integers, strings, closures) is not generated: it is the hand-written `ulib/c/cherry.h` (types and inline fast paths) and `ulib/c/cherry.c` (slow paths: big integer arithmetic, string operations), distributed with F\*. Generated units `#include "cherry.h"`; users add `$(fstar.exe --locate_lib)/ulib/c` to the include path and compile and link `cherry.c` with the program.
The Cherry pass maps the F\* primitives on `Prims.int` and `Prims.string` (arithmetic, comparisons, `strcat`, `string_of_int`, `FStar.String.{strlen,index,sub,compare}`, `FStar.IO.print_string`) to runtime functions, with per-argument ownership: they borrow their arguments, except `strcat`, which takes its first argument owned so that it can append in place.

## Known gaps

The prototype runs every test in `tests/custard` and `tests/custard/pulse` through Cherry, but it is not yet a complete backend. The goal for an initial release, running the OCaml extraction tests that exist today, is met except for the skipped tests listed in "Programs and tests". Compiling the F\* compiler itself is a later goal, because it needs C implementations of the modules that are now implemented in OCaml, and porting those is out of scope for now.

- **Library implementations.** The C runtime implements only what the tests use (see "Programs and tests"). Every other module with an OCaml implementation (a hand-written `.ml` or a `-ocaml.fst` file; under Cherry, `Builtins.cherry_realized_modules`) has no C counterpart: `FStar.Char`, the rest of `FStar.String`, and all of the compiler's `FStarC.*` support modules (`Util`, `PSMap`/`PIMap`, `Hash`, `Json`, `Getopt`, `Filepath`, `Format`, `Pprint`, ...).
- **Mutable reference-counted arrays.** `FStarC.Array` (see "Arrays") is designed but not implemented.
- **Threads.** The only spawn primitive is Pulse's `fork_core`, realized in C for the task-pool test (see "Programs and tests"); there is no `par`. ThreadSanitizer has not been run, because it cannot run in the development container (it fails to disable ASLR).
- **Unsupported constructs.** The Cherry pass rejects disjunctive patterns, tuple patterns, anonymous tuples of counted values, lambdas in polymorphic definitions, primitive operations that return counted values, and polymorphic externals used as values. Some of these may never reach the backend; this has to be checked against real code.
- **Matching out of `any`.** Constructor patterns on an `any` scrutinee need the monomorphic instance the value was built at, which only the pattern variables' uses determine (`tests/custard/AnyPat`). An impure effect whose box type is a function (`tests/custard/Effects`) is typed as a non-function in the IR.
- **Globals** are computed at startup and then made persistent, rather than emitted as static cells (see "Globals").
- **Allocation.** Cherry uses `malloc`/`free` directly. The benchmarks show that the allocator dominates allocation-heavy programs (BinaryTrees is 2.5x slower than OCaml with glibc malloc and 1.1x with mimalloc), so a small-object allocator with per-thread free lists (as in Lean) is probably needed.
- **Reuse** does not yet cover boxed records, reusing a cell for a constructor of another type of the same size, or reusing a dead variable that was not matched on (see "Heap cell reuse").
- **Scale.** The largest programs compiled so far are the tests and benchmarks. Nothing the size of a compiler component has been compiled yet.
