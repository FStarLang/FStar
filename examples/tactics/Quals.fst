module Quals

open FStar.Tactics

let attr = 42

[@attr]
unfold
let x = 2

let test () =
  assert True by (
                match lookup_attr (`attr) (cur_env ()) with
                | [x] ->
                  begin match lookup_typ (cur_env ()) (inspect_fv x) with
                  | Some se ->
                    let qs = sigelt_quals se in
                    print (term_to_string (quote qs));
                    let se' = set_sigelt_quals (qs @ [Irreducible]) se in
                    let qs' = sigelt_quals se' in
                    print (term_to_string (quote qs'))
                  | None -> fail "2"
                  end
                | _ -> fail "1")
