module Splice

open FStar.Tactics

let make_42 (nm:string) () : Tac unit =
    (* The let binds are needed due to the Tac effect *)
    (* TODO: make the cur_module call unneeded? it doesn't make sense to use another module *)
    let sv : sigelt_view = Sg_Let false (pack_fv (cur_module () @ [nm])) (`nat) (`42) in
    let ses : list sigelt = [pack_sigelt sv] in
    exact (quote ses)

%splice[x] (make_42 "x")
%splice[]  (make_42 "y")

let _ = assert (x == 42)

(* This fails at desugaring time, since `y` cannot be found. *)
(* let _ = assert (y == 42) *)
