module HigherKind

(* Section 5.0/5.4: a binder of *higher* kind -- the [m] of [class monad
   (m:Type -> Type)] -- is a type binder just as much as one of kind [Type],
   and has to be erased like one.  Taken for a runtime binder it is passed as
   a value, and its uses come out as unbound variables.

   The same goes for a type argument in a spine whose head no declaration
   describes: here the dictionary is [dyn], so the method call is compiled as
   a projection out of a runtime record and the head of the application is a
   [match].  Its type argument must go too.

   NOGREP is the point of the test on the F* side; the OCaml compiler is what
   really checks it, since a leaked binder is an unbound variable. *)
open FStar.All
open FStar.IO
open FStar.Custard

class monad (m:Type->Type) = {
  ret : #a:Type -> a -> m a;
}

class lvm (m:Type->Type) = {
  lvm_monad : monad m;
  f_int     : int -> m int;
}

instance _lvm_monad (#m:_) (_ : lvm m) : Tot (monad m) = lvm_monad

type id (a:Type) = a

instance id_monad : monad id = { ret = (fun #a (x:a) -> x) }

let mk (n:int) : lvm id = { lvm_monad = id_monad; f_int = (fun x -> x + n) }

let use (#m:Type->Type) {| lvm m |} (x:int) : m int = ret x

let pick (b:bool) : ML (lvm id) = if b then mk 1 else mk 2

let from_ref (b:bool) (x:int) : ML int =
  let d = pick b in
  use #id #(dyn d) x

let main () : ML unit =
  print_string (string_of_int (from_ref true 41));
  print_string "\n"
