module Mymon

open FStar.All

class monoid (s : Type) = { mzero : s; mplus : s -> s -> s }
instance monoid_list (a:Type) : monoid (list a) = { mzero = []; mplus = (fun x y -> x @ y) }

class monad (m : Type -> Type) = {
  ret  : #a:Type -> a -> m a;
  bind : #a:Type -> #b:Type -> m a -> (a -> ML (m b)) -> ML (m b);
}

type writer (s : Type) {| monoid s |} (a : Type) = | Wr of s & a

instance monad_writer (s : Type) (d : monoid s) : monad (writer s) = {
  ret  = (fun #a (x:a) -> Wr (mzero, x));
  bind = (fun #a #b (x : writer s a) (f : a -> ML (writer s b)) ->
            let Wr (s1, v) = x in
            let Wr (s2, w) = f v in
            Wr (mplus s1 s2, w));
}

let rec iterM (#m : Type -> Type) {| monad m |} (#a : Type)
              (f : a -> ML (m unit)) (l : list a) : ML (m unit) =
  match l with
  | [] -> ret ()
  | x :: xs -> bind (f x) (fun _ -> iterM f xs)

(* The point of the test: a *partially applied* type abbreviation used as the
   monad of a specialization. *)
let mymon = writer (list int)

let step (n:int) : ML (mymon unit) = Wr ([n], ())

let main () : ML unit =
  let Wr (l, ()) = iterM step [1;2;3] in
  FStar.IO.print_string (string_of_int (List.length l));
  FStar.IO.print_string "\n"
