module Splice

open FStar.Tactics

let make_x_42 () : Tac unit =
    (* The let binds are needed due to the Tac effect *)
    let sv : sigelt_view = Sg_Let false (pack_fv ["x"]) (`nat) (`42) in
    let ses : list sigelt = [pack_sigelt sv] in
    exact (quote ses)

%splice make_x_42
