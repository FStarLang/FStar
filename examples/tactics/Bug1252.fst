module Bug1252

open FStar.Tactics

assume val p: int -> prop
assume val p1 : p 1

type intp = x:int{p x}

let id_intp (x: intp) : intp = x

let f : intp =
  synth_by_tactic (exact_guard (q_id <-- quote id_intp;
                                q_one <-- quote 1;
                                return (pack (Tv_App q_id (q_one, Q_Explicit)))))
