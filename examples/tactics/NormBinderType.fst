module NormBinderType

open FStar.Tactics

assume val p : int
assume val q : int

let f : int -> int = fun x -> x + 2

let g =
    synth_by_tactic #((f 3 == f 5) -> q == p)
            (b <-- intro;

             norm_binder_type [delta; primops] b;;

             e <-- cur_env;
             match binders_of_env e with
             | [b] ->
                 let t = type_of_binder b in
                 q <-- quote (eq2 #int 5 7);
                 if FStar.Order.ne (compare_term t q)
                 then fail "type was not normalized"
                 else idtac
             | _ ->
                 fail "should be impossible")
