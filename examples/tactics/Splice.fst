module Splice

open FStar.Tactics

let make_x_42 () : Tac unit =
    (* The let binds are needed due to the Tac effect *)
    (* TODO: make the cur_module call unneeded? it doesn't make sense to use another module *)
    let sv : sigelt_view = Sg_Let false (pack_fv (cur_module () @ ["x"])) (`nat) (`42) in
    let ses : list sigelt = [pack_sigelt sv] in
    exact (quote ses)

%splice[x] make_x_42

let _ = assert (x == 42)
