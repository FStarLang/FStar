module DependentSynth
open FStar.Tactics

let myty b = if b then int else unit

let mk_if (test e_true e_false: term) : Tot term =
  let br_true = (Pat_Constant C_True, e_true) in
  let br_false = (Pat_Constant C_False, e_false) in
  let m = pack (Tv_Match test [ br_true; br_false ] ) in
  m

let t : tactic unit =
  b <-- quote bool ;
  let test' = fresh_binder b in
  let test = pack (Tv_Var test') in
  e_true <-- quote 3 ;
  e_false <-- quote () ;
  let body = mk_if test e_true e_false in
  let res = pack (Tv_Abs test' body) in
  // should print: function true -> 3 | false -> ()
  //print (term_to_string res) ;;
  t_exact true false (return res)

let f : ((b: bool) -> Tot (myty b)) = synth_by_tactic t
