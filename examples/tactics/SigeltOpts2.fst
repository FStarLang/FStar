module SigeltOpts2

(* This is just a regression test: we had a bug where `verify_module`
was being taken from the optionstate in the check_with, causing the
definitions to be lax-checked if the check_with moved across modules. *)

open SigeltOpts
open FStar.Tactics

let tau () : Tac decls =
  match lookup_typ (top_env ()) ["SigeltOpts"; "sp1"] with
  | None -> fail "1"
  | Some se ->
    match sigelt_opts se with
    | None -> fail "2"
    | Some opts ->
      let lb = pack_lb ({lb_fv = pack_fv ["SigeltOpts2"; "blah"];
                         lb_us = [];
                         lb_typ = (`_);
                         lb_def = (`(assert False))}) in
      let se : sigelt = pack_sigelt (Sg_Let false [lb]) in
      let se = add_check_with opts se in
      [se]

[@@ expect_failure [19]]
%splice[blah] (tau ())
