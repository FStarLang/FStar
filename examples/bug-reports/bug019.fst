module Bug019

val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec map f l = match l with
  | [] -> []
  | hd::tl -> f hd::map f tl


val test_map_1: unit -> Lemma (ensures (map (fun n -> n + 1) [1;2;3] = [2;3;4]))
let test_map_1 () = ()

let plus_one n = n + 1
val test_map_2: unit -> Lemma (ensures (map plus_one [1;2;3] = [2;3;4]))
let test_map_2 () = ()
