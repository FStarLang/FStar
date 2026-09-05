module MonoState

(* Section 5.0: a higher-kinded [Mono] argument arrives as a *lambda*, and
   substituting it leaves a beta-redex in type position.

   [FStarC.SMTEncoding.Pruning] is the case this was found in.  Its state
   monad is [st a = ctxt -> ML (a & ctxt)], and rule 5 of section 3.1 makes
   the [m] of [class monad (m:Type -> Type)] [Mono], since the dictionary's
   type mentions it.  [specialize] then substitutes [m := fun a -> ctxt -> ML
   (a & ctxt)] into every binder sort and into the result comp -- with
   [SS.subst], which does not reduce -- so [m a] becomes [(fun a -> ...) a].
   Only the definition's *body* is normalized, so the redex survives in the
   signature alone, and its head is a [Tm_abs] rather than a name.

   Read as [any] that made the whole of the monad's plumbing [Obj.t], with an
   [Obj.magic] at every bind: 528 of them in the compiler's own extracted
   output, against 80 with the redex reduced.  So the GREP here is on the
   *type* [ctxt -> ('a * ctxt)] being written down, and the NOGREP on there
   being no [Obj] left at all. *)

open FStar.All
open FStar.IO
open FStar.Custard

class monad (m:Type -> Type) = {
  mreturn : #a:Type -> a -> m a;
  mbind   : #a:Type -> #b:Type -> m a -> (a -> ML (m b)) -> ML (m b);
}

type ctxt = { seen : int; sum : int }

let st a = ctxt -> ML (a & ctxt)

let st_return (#a:Type) (x:a) : st a = fun s -> (x, s)
let st_bind (#a #b:Type) (m:st a) (f:a -> ML (st b)) : ML (st b) =
  fun s -> let (x, s) = m s in (f x) s

instance st_monad : monad st = {
  mreturn = st_return;
  mbind   = st_bind;
}

let get : st ctxt = fun s -> (s, s)
let put (c:ctxt) : st unit = fun _ -> ((), c)

(* [let!] over the class, exactly as Pruning writes it: the definition is
   generic in [m] and every use of it here specializes at [st]. *)
let bind (#m:Type -> Type) {| monad m |} (#a #b:Type)
         (x : m a) (f : a -> ML (m b)) : ML (m b) = mbind x f

let visit (n:int) : ML (st unit) =
  bind get (fun c -> put { seen = c.seen + 1; sum = c.sum + n })

let rec walk (l:list int) : ML (st unit) =
  match l with
  | [] -> mreturn ()
  | x :: xs -> bind (visit x) (fun _ -> walk xs)

let run (l:list int) : ML (int & int) =
  let _, c = walk l { seen = 0; sum = 0 } in
  (c.seen, c.sum)

let main () : ML unit =
  let n, t = run [1; 2; 3; 4] in
  print_string (string_of_int n ^ " " ^ string_of_int t ^ "\n")
