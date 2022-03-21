module DeltaQual

module T = FStar.Tactics

unfold
let f0 = 0

inline_for_extraction
let f1 = f0

let test () =
  let open T in
  assert (f1 == 0)
    by (T.norm [delta_qualifier ["inline_for_extraction"; "unfold"]];
        let g = T.cur_goal () in
        match T.term_as_formula g with
        | Comp (Eq _) tv _ ->
          (match T.inspect tv with
           | Tv_Const (C_Int 0) -> T.trefl()
           | _ -> T.fail "unreduced")
        | _ -> T.fail "unreduced")
