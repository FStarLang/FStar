module IO = struct

open Printf

(* https://ocaml.org/learn/tutorials/file_manipulation.html#Reading *)
(* http://rosettacode.org/wiki/Read_entire_file#OCaml *)

let read f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let write f s =
  let oc = open_out f in
  fprintf oc "%s" s;
  close_out oc

end
