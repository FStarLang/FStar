module Unit2

(* Some simple tests that require --rel2 to succeed; to be expanded *)
let f1 (l:list nat) = 0::l
let f2 (x:nat) (y:int) = x=y 
let f3 : list nat = 
  let y = [0;1] in 
  y


(* THIS SHOULD WORK EVENTUALLY, but not right now; requires an annotation  *)
(* assume val f4 : nat -> Tot bool *)
(* assume val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b) *)
(* let test4 = map (fun n -> [f n]) [2] *) //needs n:nat
  
