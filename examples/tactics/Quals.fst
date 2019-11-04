module Quals

open FStar.Tactics

let tau () : Tac decls =
  let se : sigelt = pack_sigelt (Sg_Let false (pack_fv ["Quals"; "sp1"]) [] (`int) (`42)) in
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
