module VC

open FStar.Tactics

(* Testing that all VCs needed here are trivial by normalization/simplification *)
#set-options "--no_smt"

let test1 (#a: Type) (f: a -> Tac unit) (l: list a): Tac unit = ()

let test2 (#a: Type) (f: a -> Tac unit) (l: list a): Tac unit =
    match l with
    | [] -> fail ""
    | h::_ -> f h
    | _ -> fail "impossible" // needed, we don't do syntactic coverage checks

let test3 (#a: Type) (f: a -> Tac unit) (l: list a): Tac unit =
    begin match l with
    | [] -> fail ""
    | h::_ -> (f h ; f h ; f h)
    | _ -> fail "impossible" // needed, we don't do syntactic coverage checks

    end;
    dump ""

let tau b tm : Tac term =
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    match inspect (quote b) with
    | Tv_App l r -> tm
    | Tv_Type _ -> tm
    | Tv_AscribedT _ _ None -> tm
    | _ -> tm
