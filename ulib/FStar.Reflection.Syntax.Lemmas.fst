module FStar.Reflection.Syntax.Lemmas

open FStar.Reflection.Syntax

val uncurry : ('a -> 'b -> 'c) -> ('a * 'b -> 'c)
let uncurry f (x, y) = f x y

val curry : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
let curry f x y = f (x, y)

val mk_app_collect_inv_s : (t:term) -> (args:list term) ->
                            Lemma (uncurry mk_app (collect_app' args t) == mk_app t args)
let rec mk_app_collect_inv_s t args =
    match inspect t with
    | Tv_App l r ->
        mk_app_collect_inv_s l (r::args);
        pack_inspect_inv t
    | _ -> ()

val mk_app_collect_inv : (t:term) -> Lemma (uncurry mk_app (collect_app t) == t)
let rec mk_app_collect_inv t = mk_app_collect_inv_s t []

(*
 * The way back is not stricly true: the list of arguments could grow.
 * It's annoying to even state, might do it later
 *)
