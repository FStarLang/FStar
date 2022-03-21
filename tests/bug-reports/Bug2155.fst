module Bug2155

open FStar.Tactics

let f (x:int) = [normalize_term x; x]

let _ = assert True by begin
  let t = `(f (100 + 100)) in
  let t = norm_term [delta] t in
  (* dump (term_to_string t); *)
  guard (term_eq t (`(Cons #int 200 (Cons #int (100+100) (Nil #int)))));
  ()
end
