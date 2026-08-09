module Magic

(* Section 5.4: where the coercions go.

   A class over a type *constructor* is the one construct that genuinely has no
   counterpart in either the IR's type language or OCaml's: [m a], with [m] a
   bound [Type -> Type], is not an application of anything Custard can look up,
   so the dictionary's fields land on [TAny] and print as [Obj.t].  A coercion
   there is unavoidable, and this module is where the compiler is held to
   putting exactly the unavoidable ones in.

   The interesting placements are: the constructor built at the abstract result
   type, the scrutinee matched at it, and the argument handed to a field whose
   own parameter type survived.  What must *not* appear is a coercion anywhere
   in [main], which is entirely concrete. *)

open FStar.All

class monad (m : Type -> Type) = {
  ret  : #a:Type -> a -> m a;
  bind : #a:Type -> #b:Type -> m a -> (a -> m b) -> m b;
}

instance opt_monad : monad option = {
  ret  = (fun #a x -> Some x);
  bind = (fun #a #b x f -> match x with None -> None | Some v -> f v);
}

let twice (#m:Type -> Type) {| monad m |} (x : m int) : m int =
  bind x (fun v -> ret (v + v))

let main () : ML unit =
  match twice #option (Some 21) with
  | Some n -> FStar.IO.print_string (string_of_int n ^ "\n")
  | None   -> FStar.IO.print_string "none\n"
