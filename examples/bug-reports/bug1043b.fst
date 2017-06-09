module Bug1043b

(* 42 gets blamed; super strange *)
let foo () : int =
    let (l1, l2) = "haha" in 42

(* whole match gets blamed; better, but still not ideal *)
(* let foo () : int = *)
(*     match "haha" with *)
(*     | (l1, l2) -> 42 *)

(* works *)
(* let foo () : int = *)
(*     let l1 : int = "haha" in 42 *)
