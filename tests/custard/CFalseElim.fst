module CFalseElim

(* `FStar.Pervasives.false_elim` is `Prims.magic` and `Prims.admit` in a third
   spelling: it typechecks only because the caller has `False` in scope, and
   its own definition is

       let rec false_elim #_ _ = false_elim ()

   -- a non-terminating loop standing in for a value that cannot exist.
   `magic` and `admit` have had a builtin rule mapping them to `EAbort` since
   M2; `false_elim` did not, so Custard extracted the loop.  That was worse
   than useless in two different ways.  On OCaml the residue is an infinite
   loop where a `failwith` belongs, so a program that reaches
   provably-unreachable code hangs rather than saying so.  On C it was a hard
   368 -- the result type is a type variable -- and with type monomorphization
   on it became a 368 about the *return* type of a function that never
   returns.

   `EAbort` at `TAny` fixes both: `TAny` stands where a value of any type is
   wanted, so the C backend stops caring what the result type was.

   [g] is reachable but not taken, so the test compiles, runs, and returns 0;
   what it pins is that `abort()` is emitted at all, and that no residue of
   `false_elim` itself survives. *)

let g (sq: squash False) : FStar.UInt32.t = FStar.Pervasives.false_elim ()

let pick (b: bool) : FStar.UInt32.t = if b then 0ul else g (magic ())

let main () : FStar.UInt32.t = pick true
