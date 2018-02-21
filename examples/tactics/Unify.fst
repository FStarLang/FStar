module Unify

open FStar.Tactics

let h : int =
    synth_by_tactic (
        l <-- fresh_uvar None; // None: we don't provide a type
        r <-- fresh_uvar None;
        apply (quote op_Addition);;
        exact (return l);;
        exact (return r);;
        ocho <-- quote 8;
        unify r ocho;;
        unify l r;;
        return ()
    )

let _ = assert (h == 16)
