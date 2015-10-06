module Bug

val bar : (u:unit & unit) -> Tot unit
let bar p = 
  let r1 = fst (p, p) in    (* fails *)
(*   let r1, _ = p, p in *) (* also fails *)
(*   let r1 = p in *)       (* works *)
  let (|_, _|) = r1 in 
  () 
