#light "off"
module FStar.ST
  type 'a __ref = 'a ref
  type 'a ref = 'a __ref
  let read x = !x
  let op_Colon_Equals x y = x := y
  let alloc x = ref x
