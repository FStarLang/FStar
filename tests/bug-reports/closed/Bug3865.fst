module Bug3865

(* unfold *)
let myty t = t -> Tot t

noeq
type pak = {
  t : Type0;
  f : myty t;
}

let intpak = {
  t = int;
  f = (fun x -> x + 1);
}

let use =
  let x = intpak.f 123 in
  IO.print_string (string_of_int x ^ "\n")
