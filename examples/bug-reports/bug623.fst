module Bug623

open FStar.All

val null: unit -> All unit
  (requires (fun h -> True))
  (ensures  (fun h r h' -> True))
let null () = ()

(* Fails *)
(* let test0 = assert(false); null () *)

(* Succeeds *)
let test1 () = assert(false); null ()

(* Succeeds *)
let test2 (u:unit) = assert(false); null ()

(* Fails *)
(* let test3 (u:unit) : All unit (requires (fun h -> True)) (ensures (fun h r h' -> True)) = assert(false); null() *)

(* Succeeds *)
let test3' () : All unit (requires (fun h -> True)) (ensures (fun h r h' -> True)) = assert(false); null()

(* Succeeds *)
let test4 (u:unit) : ML unit = assert(false); null()

(* Fails *)
(* let test5 (u:unit) : ML unit = assert(false) *)

val null2: unit -> Div unit
  (requires (True))
  (ensures  (fun r -> True))
let null2 () = ()

(* Succeeds *)
let test6 (u:unit) : ML unit = assert(false); null2()

val null3: unit -> Pure unit
  (requires (True))
  (ensures  (fun r -> True))
let null3 () = ()

(* Fails *)
let test7 (u:unit) : ML unit = assert(false); null3()
