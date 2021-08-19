module SigeltOpts

open FStar.Tactics

#set-options "--max_fuel 0"

#push-options "--max_fuel 2 --record_options"
let sp1 = assert (List.length [1] == 1)
#pop-options

(* Fails without fuel *)
[@@expect_failure]
let sp2 = assert (List.length [1] == 1)

let tau () : Tac decls =
  match lookup_typ (top_env ()) ["SigeltOpts"; "sp1"] with
  | None -> fail "1"
  | Some se ->
    match sigelt_opts se with
    | None -> fail "2"
    | Some opts ->
      let lb = pack_lb ({lb_fv = pack_fv ["SigeltOpts"; "blah"];
                         lb_us = [];
                         lb_typ = (`_);
                         lb_def = (`(assert (List.length [2] == 1)))}) in
      let se : sigelt = pack_sigelt (Sg_Let false [lb]) in
      let se = add_check_with opts se in
      [se]
(* Splice `blah`, using the options for sp1, i.e. --max_fuel 2 *)
%splice[blah] (tau ())

(* Outside, still with max_fuel = 0 *)
[@@expect_failure]
let sp3 = assert (List.length [1] == 1)
