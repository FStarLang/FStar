(* https://www.lexifi.com/blog/references-physical-equality *)
type 'a ref = {
  mutable contents: 'a;
  id: int
}

let read x =
  x.contents

let op_Bang x = read x

let write x y =
  x.contents <- y

let op_Colon_Equals x y = write x y

let uid = ref 0

let alloc contents =
  let id = incr uid; !uid in
  let r = { id; contents } in
  Obj.(set_tag (repr r) object_tag);
  r

let new_region = (fun r0 -> ())
let new_colored_region = (fun r0 c -> ())

let ralloc i contents =
  alloc contents

let recall = (fun r -> ())
let recall_region = (fun r -> ())
let get () = ()

(* AR: adding these for HST *)
let push_frame () = ()
let pop_frame () = ()

let salloc contents = alloc contents
