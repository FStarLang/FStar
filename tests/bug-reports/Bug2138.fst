module Bug2138

open FStar.Tactics

type t1 = {
  x : bool;
}

let x = (Mkt1 true = Mkt1 false)
let y = (Mkt1 true = Mkt1 true)

let _ = assert True by begin
  let check (b:bool) : Tac unit =
    if not b then fail "test failed"
  in
  check (term_eq (norm_term [primops;delta] (`x)) (`false));
  check (term_eq (norm_term [primops;delta] (`y)) (`true));
  ()
end
