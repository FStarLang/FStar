module CherryProjVal
module U32 = FStar.UInt32
open FStar.All

(* A generated projector passed as a function: its pattern variable has no
   sort, so extraction types it any while the pattern binds it concretely. *)
type payload = | P1 of int | P2 of string

let rec filter_map (f: 'a -> option 'b) (l: list 'a) : list 'b =
  match l with
  | [] -> []
  | x :: xs -> (match f x with Some y -> y :: filter_map f xs | None -> filter_map f xs)

let main () : ML U32.t =
  let l : list (string & option payload & list int) =
    [("a", Some (P1 1), []); ("b", None, [2]); ("c", Some (P2 "x"), [])] in
  let r = filter_map Mktuple3?._2 l in
  if List.Tot.length r = 2 then 0ul else 1ul
