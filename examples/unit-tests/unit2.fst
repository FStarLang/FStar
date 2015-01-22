module Unit2

(* Some simple tests that require --rel2 to succeed; to be expanded *)
let f1 (l:list nat) = 0::l
let f2 (x:nat) (y:int) = x=y 
let f3 : list nat = 
  let y = [0;1] in 
  y
  
