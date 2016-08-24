(* https://www.lexifi.com/blog/references-physical-equality *)
type 'a ref = {
  mutable contents: 'a;
  id: int
}

let read x =
  x.contents

let op_Colon_Equals x y =
  x.contents <- y

let uid = ref 0

let alloc contents =
  let id = incr uid; !uid in
  let r = { id; contents } in
  Obj.(set_tag (repr r) object_tag);
  r

let op_Bang = read

let new_region = (fun r0 -> ())
let new_colored_region = (fun r0 c -> ())
let ralloc = (fun i x -> ref x)
let recall = (fun i r -> ())
let recall_region = (fun r -> ())
let get () = ()
