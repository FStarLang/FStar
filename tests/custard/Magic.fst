module Magic

(* Section 5.4/5.0: a class over a type *constructor* -- [m a] with [m] a bound
   [Type -> Type] -- is not something the IR's type language or OCaml can name.
   But [m] is a type binder like any other, so a call whose instance is known
   specializes on it, and nothing abstract is left: everything below comes out
   at [option], with no coercion anywhere.

   The case that genuinely cannot be named is the one where the dictionary is
   only known at run time; that is [HigherKind]. *)

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
