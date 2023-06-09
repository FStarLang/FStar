module Quals

open FStar.Tactics.V2

let tau () : Tac decls =
  let lb = {
    lb_fv = (pack_fv ["Quals"; "sp1"]);
    lb_us = [];
    lb_typ = (`int);
    lb_def = (`42);
  } in
  let se : sigelt = pack_sigelt (Sg_Let {isrec=false; lbs=[lb]}) in
  let se = set_sigelt_quals [Unfold_for_unification_and_vcgen; Inline_for_extraction] se in
  [se]

%splice[sp1] (tau ())

let test_sp1 () =
  assert True by (match lookup_typ (cur_env ()) ["Quals"; "sp1"] with
               | Some se ->
                 begin match sigelt_quals se with
                 | [Unfold_for_unification_and_vcgen; Inline_for_extraction] -> ()
                 | _ -> fail "1"
                 end
               | None -> fail "2")
