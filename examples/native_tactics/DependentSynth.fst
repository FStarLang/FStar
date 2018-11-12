module DependentSynth
open FStar.Tactics

let myty b = if b then int else unit

let mk_if (test e_true e_false: term) : Tac term =
  let br_true = (Pat_Constant C_True, e_true) in
  let br_false = (Pat_Constant C_False, e_false) in
  let m = pack (Tv_Match test [ br_true; br_false ] ) in
  m

[@plugin]
let t () : Tac unit =
  let b = `bool in
  let test' = fresh_bv b in
  let test = pack (Tv_Var test') in
  let e_true = `3 in
  let e_false = `() in
  let body = mk_if test e_true e_false in
  let res = pack (Tv_Abs (mk_binder test') body) in
  // should print: function true -> 3 | false -> ()
  //print (term_to_string res);
  t_exact true true res

let f : ((b: bool) -> Tot (myty b)) = synth_by_tactic t
