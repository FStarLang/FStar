module WarnAny

(* Section 5.6: --custard_warn_any reports every position where Custard lost
   track of what a value looks like at runtime.

   Higher-kinded polymorphism is the one construct that reliably produces such
   a position.  [f int], where [f] is a *bound* type variable of kind
   [Type0 -> Type0], is not an application of a type constructor Custard can
   look up, and the target type language has nothing to say about it: it lands
   on [TAny].  Monomorphization does not save us either, because [f] is not a
   [Mono] argument and could not be one -- a Mono argument stands for a value.

   So this module is a *rejection* test: extraction of it must report warning
   366, which the suite escalates to an error.

   [hk] *chooses* between its two [f int] arguments rather than returning one
   of them, so that section 27.4's forwarder rule does not collapse the call
   and delete the very declaration whose type is being complained about. *)

open FStar.All

let hk (#f: Type0 -> Type0) (n: bool) (x: f int) (y: f int) : f int =
  if n then x else y

let main () : ML unit =
  let l : list int = hk #(fun a -> list a) true [1; 2; 3] [] in
  FStar.IO.print_string (string_of_int (List.length l))
