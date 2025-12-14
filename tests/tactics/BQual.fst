module BQual

open FStar.Tactics.V2

let _ = assert True by begin
  let b : binder = { 
    uniq = 0;
    ppname = Sealed.seal "xyz";
    sort = (`int);
    qual = Q_Equality;
    attrs = [];
  }
  in
  let t : term = pack (Tv_Arrow b (C_Total (`int))) in
  let s = term_to_string t in
  if term_to_string t <> "$xyz: int -> int" then
    fail ("unexpected: " ^ s)
end
