#light "off"
module FStar_ST
  type 'a __ref = 'a ref
  type 'a ref = 'a __ref
  let read x = !x
  let op_Colon_Equals x y = x := y
  let alloc x = ref x
  
  let recall = (fun r -> ())
  let write x y = x.contents <- y
