module CalcImpl

open FStar.Calc

assume val p : prop
assume val q : prop

assume val lem : unit -> Lemma (requires p) (ensures q)

let test () =
  calc (==>) {
    p;
    ==> { lem () } (* this is only working since desugaring is wrapping
                    * the justification with a calc_push_impl, otherwise
                    * our goal would be squash (p ==> q) and we could
                    * not call lem (as p cannot be proven) *)
    q;
  }

let any p q = True

let test3  () =
  calc any {
    p /\ p;
    <==> {}
    p;
    ==> { lem () } (* works per-step, even if the final relation is something else *)
    q /\ q;
    <==> {}
    q;
  }

let test4  () =
  calc any {
    p /\ p;
    <==> {}
    p;
    l_imp { lem () } (* can also use l_imp instead of ==> *)
    q /\ q;
    <==> {}
    q;
  }

(* overriding ==> should not cause confusion *)

let (==>) = (<)

let test5 () =
  calc (==>) {
    1;
    ==> {}
    2;
  }
