module LaxOn

open FStar.Tactics

let a : int =
    synth_by_tactic (fun () -> guard (not (lax_on ()));
                               exact (`1))

#set-options "--lax"

let b : int =
    synth_by_tactic (fun () -> guard (lax_on ());
                               exact (`2))
