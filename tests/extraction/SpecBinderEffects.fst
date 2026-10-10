module SpecBinderEffects

(* What dropping a binder must not do to an effect.

   If dropping the binder a [requires] desugars into leaves a definition with
   no binder at all, its abstraction disappears and an effectful definition
   becomes an effectful *value*.  Its effect then runs once, when the module
   is initialized, rather than once per call -- or, if the resulting value is
   mistaken for a pure one, it is dropped as dead code and never runs at all.
   That is the second half of issue #4650, and no pure test can see it.

   So the output below is *ordered*.  [init] is printed by the first
   declaration in the module, and [START] by the first line of [main]:

     - an effect that escaped into module initialization appears between them,
     - an effect that was dropped does not appear at all,
     - an effect that runs once per call appears once per call, in order.

   [NEVER] is printed by a definition of exactly that shape which nothing
   calls, so it must not appear anywhere. *)

open FStar.All

assume val q : prop
assume val pf : squash q

let say (s:string) : ML unit = FStar.IO.print_string s

let _ : unit = say "init\n"

(* Generalization takes [#a] into a type parameter and the spec binder is
   dropped, so nothing is left: [tick] has to be kept a function by thunking
   it, and the thunk's arrow has to stay *impure* or the calls below are dead
   pure code. *)
let tick (#a:Type) : ML unit (requires q) = say "tick "

(* The same shape, never called.  Erasing its binder would move its effect to
   module initialization, where it would run even though nothing calls it. *)
let never (#a:Type) : ML unit (requires q) = say "NEVER "

(* Recursive, and still nothing is left.  The recursive call has to be thunked
   too.  [stop] is a top-level constant rather than a literal so that
   extraction cannot fold the branch away: the call really is compiled, it is
   just not taken. *)
let stop : bool = true
let rec spin (#a:Type) : ML unit (requires q) =
  say "spin ";
  if stop then () else spin #int

(* Mutual recursion, nothing left on either side, and here the cross call
   really is taken. *)
let rec ping (#a:Type0) : ML unit (requires q) = say "ping "; pong #int
and pong (#a:Type0) : ML unit (requires q) =
  say "pong "; if stop then () else ping #bool

(* Only the spec binder is dropped; a real argument remains. *)
let echo (s:string) : ML unit (requires q) = say s

(* Point-free higher order: [twice] receives [echo1] itself, so the two have
   to agree about how many arguments it takes. *)
let twice (f : unit -> ML unit) : ML unit = f (); f ()
let echo1 (u:unit) : ML unit (requires q) = say "echo1 "
let via_twice () : ML unit = twice echo1

(* A local definition with nothing left either; local [let]s are extracted by
   a different path than top-level ones. *)
let nested () : ML unit =
  let inner (#a:Type) : ML unit (requires q) = say "inner " in
  inner #int; inner #bool

(* The pure counterpart must *not* be thunked: [answer] is a value either way,
   so it stays one and its uses pass no argument. *)
let answer (#a:Type) : Pure int (requires q) (ensures fun _ -> True) = 42

(* Declared by a [val] and defined separately, which is the path interface
   extraction takes. *)
val valdef : unit -> ML unit (requires q)
let valdef () = say "valdef "

let main () : ML unit =
  say "START ";
  tick #int;
  tick #bool;
  spin #int;
  ping #int;
  echo "echo ";
  via_twice ();
  nested ();
  say (string_of_int (answer #int) ^ " ");
  valdef ();
  say "END\n"

let _ : unit = main ()
