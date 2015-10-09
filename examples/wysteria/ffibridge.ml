open AST

exception FFI_error of string

let cast x = Obj.magic x
    
let project_value_content (v:unit value) :Obj.t =
  let content =
    match v with
      | V_prin p -> cast p
      | V_eprins eps -> cast eps
      | V_prins ps -> cast ps
      | V_unit -> cast ()
      | V_bool b -> cast b
      | V_opaque (_, v, _, _, _, _) -> cast v
      | V_box _ -> cast v
      | V_wire _ -> cast v
      | _ -> raise (FFI_error ("FFI fn input not an expected alue"))
  in
  content

let exec_ffi (n:int) (ffi_fn:Obj.t) (l:dvalue list) (ffi_inj:Obj.t) :dvalue =
  let f = cast ffi_fn in
  let ffi_ret =
    match n with
      | 1 ->
	let a = List.hd l in
	f (cast a)

      | 2 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	f (cast a1) (cast a2)

      | 3 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	let a3 = List.hd (List.tl (List.tl l)) in
	f (cast a1) (cast a2) (cast a3)

      | 4 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	let a3 = List.hd (List.tl (List.tl l)) in
	let a4 = List.hd (List.tl (List.tl (List.tl l))) in
	f (cast a1) (cast a2) (cast a3) (cast a4)

      | 5 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	let a3 = List.hd (List.tl (List.tl l)) in
	let a4 = List.hd (List.tl (List.tl (List.tl l))) in
	let a5 = List.hd (List.tl (List.tl (List.tl (List.tl l)))) in
	f (cast a1) (cast a2) (cast a3) (cast a4) (cast a5)

      | _ ->
	let msg =
	  if n = 0 then "Zero argument FFI call not expected"
	  else "Add support for more arguments in FFI"
	in
	raise (FFI_error msg)
  in
  cast ((cast ffi_inj) ffi_ret)
  
let verified_eq _ _ = true
