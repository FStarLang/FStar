let mk_list n =
  Camlstack.push_frame ();
  let out = Camlstack.mk_ref [] in
  for i = 0 to n do
    out := Camlstack.cons i !out;
  done;
  Camlstack.pop_frame()

let _ = mk_list 1000

  

