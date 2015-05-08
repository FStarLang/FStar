module Bug187

opaque type verified : unit -> unit -> Type
assume type vkey = k:unit{verified k == verified k}

assume val test : option (d:unit & vkey)

let fail =
  match test with
  | Some (| sender, vk |) -> ()
  | None -> ()

(* The following equivalent code does typecheck*)
let no_fail =
  let x = test in
  if is_Some x then
    let (|sender, vk|) = Some.v x in  ()
