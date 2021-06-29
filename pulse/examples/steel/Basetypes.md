The Steel heap maps addresses to cells, and each cell holds both a value `v` and its type `a`:
```fst
noeq
type cell : Type u#(a + 1) =
  | Ref : a:Type u#a ->
          p:pcm a ->
          frac:Frac.perm{ frac `Frac.lesser_equal_perm` Frac.full_perm } ->
          v:a { frac == Frac.full_perm ==> p.refine v } ->
          cell
```
If we would like to model references to substructures `w:b` of `v`
without having to add new constructors to `cell` specifically for structs and arrays,
it seems inevitable that the model will have to keep track of both the
type `b` of the substructure and the type `a` of its base object.
AggregateRef.fst defines a type of such references `ref a b`.
Because ref has to keep track of the type of its base object, code
that works with references has to carry around extra parameters.
The model runs into trouble when the number of references isn't known
statically; for example, if one wants to specify the contents of an array
of references, each with possibly different base objects.
Unfortunately it's not possible to solve this by hiding `a` behind
an existential, because that would increase `ref`'s universe level.

One idea could be to hide `a` inside a closure, exposing only a record of basic operations:
```fstar
let operations =
  let r: ref a b = .. in {
    read = (fun () -> .. r ..);
    write = (fun () -> .. r ..);
  }
```
This would work if we just wanted simply typed versions of `read` and `write`,
but there is no way to give dependently-typed specifications to these
functions without talking about the base object `a`.

Here are some ideas on how to resolve this:

### Hide `a` in a closure, then carry along proofs extrinsically

Construct a record `{read = .., write = ..}` hiding the base type `a`
and the raw `ref a b` inside closures, and give `read` and `write` simple types.
Return, with it, a proof of `exists a. read spec /\ write spec`.
This would allow the record to live in universe `0` (the record is
simply typed and the proof is squashed), so refs could safely be stored in the Steel heap.

However, giving the operations simple types means that they have to return some bogus
value (or be partial) on inputs which don't satisfy their preconditions;
this seems tricky, or maybe even impossible if the preconditions aren't decidable.

### Represent refs just as addresses

The heap stores the types and PCMs along with values.
Is it possible, then, to avoid storing those same types and PCMs inside the ref?
If so, we could store refs in the heap, and only mention base types/PCMs
in predicates like `pts_to`. Unfortunately, this doesn't seem possible
either, because the base type is needed to give a type to the lens.

### Store the lens in the heap

Can we treat a reference like an addressable stack-local and store
its lens in the heap? For example, if we start with
```
p `pts_to` {x, y}
```
and take a pointer to the first field of `{x, y}`, we get
```
(p `pts_to` {x, y}) `star`
(r `pts_to` {base_type & lens for field x of base_type})
r: Steel.Memory.ref _
```
This loses a lot of equalities. For example, if we take
a second pointer to the first field of `{x, y}` we get
```
(p `pts_to` {x, y}) `star`
(r `pts_to` {base_type & lens for field x of base_type})
(s `pts_to` {base_type & lens for field x of base_type})
r, s: Steel.Memory.ref _
```
If we would like to use the fact that `r` and `s` alias later on,
we need to use separation logic to prove that any code between then
and when the pointers were taken didn't modify either of the lenses.

### Store lenses along with base objects

Instead of just storing values v in the heap, store (v, [l1, .., ln])
where [l1, .., ln] are a (heterogenous) list of lenses into
v. Represent references as (addr, k) where k is an index into this
list. (This may not necessarily mean modifying Steel.Heap---it could
be possible to design a PCM to carry along these lists of lenses.)

This would fix the universe issue, but it's very complicated..
Also, in order to nicely support reasoning about aliasing, we would
want that the list of lenses not contain any duplicates; to maintain
that invariant, we'd need decidable equality on lenses, which isn't guaranteed.

### Give up on hiding the base object

Though the model in AggregateRef.fst is designed for writing C-like code,
the representation of a reference as a lens + Steel memory ref
suggests that there could be more high-level applications of references as well.
For example, it might be possible to construct a "reference" to a linked list
which allows viewing it as an ordinary F* list of its elements, or to
construct a "reference" to a u32 from the upper 16 bits of two other u32 references.
These things aren't possible with the current model because an AggregateRef.ref
contains only one Steel.Memory.ref, and therefore can only point to
one piece of memory; in order to support these fancy applications,
we'd need to allow an AggregateRef.ref to point to parts of multiple
different pieces at once.

We could address this and somewhat get around the base object issue by
representing references as a lens + a family of `Steel.Memory.ref`s
instead of just a single `Steel.Memory.ref`.
Then:
- It would be possible to write a function like
    `ref u32 u16 -> ref u32 u16 -> ref (u32 & u32) u32`
    to combine two refs for the upper 16 bits of two `u32`s into
    a 32-bit ref
- It would be possible to write a function like
    `cons: ref 'a 'c -> ref 'b (list 'c) -> ref ('a & 'b) (list 'c)`
    to build up a "reference" to a linked list
- An array of pointers `t *a[n]` could be represented by a
    `ref base_type_at (i:nat{i<n} -> ref (base_type_at i) t)`
    For example, if I have two references `p: ref ('a1 * .. * 'am) 'c`
    and `q: ref ('b1 * .. * 'bn) 'c` then an array containing `p` and `q`
    could be represented by
      ```fstar
      let base_type is_p =
        if is_p then 'a1*..*'am else 'b1*..*'bn
      in r: ref base_type (is_q:bool -> ref (base_type is_q) 'c)
      ```