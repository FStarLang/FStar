module FStar.Tactics.Typeclasses

(* TODO: This must be in the FStar.Tactics.* namespace or we fail to build
 * fstarlib. That seems silly, but I forget the details of the library split. *)

open FStar.Tactics

(* The attribute that marks instances *)
irreducible
let instance : unit = ()

let rec first (f : 'a -> Tac 'b) (l : list 'a) : Tac 'b =
    match l with
    | [] -> fail "no cands"
    | x::xs -> (fun () -> f x) `or_else` (fun () -> first f xs)

let rec tcresolve () : Tac unit =
    local `or_else` (fun () -> global `or_else` (fun () -> fail "Typeclass resolution failed"))
and local () : Tac unit =
    let bs = binders_of_env (cur_env ()) in
    first (fun b -> trywith (pack (Tv_Var (bv_of_binder b)))) bs
and global () : Tac unit =
    let cands = lookup_attr (`instance) (cur_env ()) in
    first (fun fv -> trywith (pack (Tv_FVar fv))) cands
and trywith t : Tac unit =
    debug ("Trying to apply hypothesis/instance: " ^ term_to_string t);
    (fun () -> apply t) `seq` tcresolve

(* Solve an explicit argument by typeclass resolution *)
let solve (#a:Type) (#[tcresolve] ev : a) () : Tot a = ev
