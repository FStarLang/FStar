module FStar.Ghost.Pull

(** 
   [pull] is an axiom.

   It type states that for any ghost function ``f``, we can exhibit a
   total function ``g`` that is pointwise equal to ``f``. However, it
   may not be possible, in general, to compute ``g`` in a way that
   enables it to be compiled by F*. So, ``pull f`` itself has ghost
   effect, indicating that applications of ``pull`` cannot be used in
   compilable code.

   Alternatively, one can think of `pull` as saying that the GTot
   effect is idempotent and non-dependent, meaning that if evaluating
   `f` on an argument `v:a`, exhibits an effect `GTot` and returns a
   result; then the effect does not depend on `v` and it can be
   subsumed to exhibiting the effect first and then computing `f v`
   purely.
   
   In other words, it "pulls" the effect out of `f`.

   pull is useful to mimic a kind of Tot/GTot effect polymorphism. 
   
   E.g.,  if you have `f: a -> GTot b` and a `l:list a`
          you can do List.map (pull f) l : GTot (list b)
 *)
val pull (#a:Type) (#b:a -> Type) (f: (x:a -> GTot (b x)))
  : GTot (x:a -> b x)

val pull_equiv (#a:Type) (#b:a -> Type) (f: (x:a -> GTot (b x))) (x:a)
  : Lemma (ensures pull f x == f x)
          [SMTPat (pull f x)]

