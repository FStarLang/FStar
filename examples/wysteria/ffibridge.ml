open AST

exception FFI_error of string

let cast x = Obj.magic x
    
let project_value_content (dv:dvalue) :Obj.t =
  let D_v (_, v) = dv in
  let content =
    match v with
      | V_prin p -> cast p
      | V_eprins eps -> cast eps
      | V_prins ps -> cast ps
      | V_unit -> cast ()
      | V_bool b -> cast b
      | V_opaque (_, v, _, _, _, _) -> cast v
      | V_box _ -> cast dv
      | V_wire _ -> cast dv
      | _ -> raise (FFI_error ("FFI fn input not an expected alue"))
  in
  content

let process_list (l:dvalue list) :Obj.t list =
  List.rev (
    List.map (fun dv ->
      project_value_content dv
    ) l)

let exec_ffi (n:int) (ffi_fn:Obj.t) (l:dvalue list) (ffi_inj:Obj.t) :dvalue =
  let f = cast ffi_fn in
  let l = process_list l in
  let ffi_ret =
    match n with
      | 1 ->
	let a = List.hd l in
	f a

      | 2 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	f a1 a2

      | 3 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	let a3 = List.hd (List.tl (List.tl l)) in
	f a1 a2 a3

      | 4 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	let a3 = List.hd (List.tl (List.tl l)) in
	let a4 = List.hd (List.tl (List.tl (List.tl l))) in
	f a1 a2 a3 a4

      | 5 ->
	let a1 = List.hd l in
	let a2 = List.hd (List.tl l) in
	let a3 = List.hd (List.tl (List.tl l)) in
	let a4 = List.hd (List.tl (List.tl (List.tl l))) in
	let a5 = List.hd (List.tl (List.tl (List.tl (List.tl l)))) in
	f a1 a2 a3 a4 a5

      | _ ->
	let msg =
	  if n = 0 then "Zero argument FFI call not expected"
	  else "Add support for more arguments in FFI"
	in
	raise (FFI_error msg)
  in
  cast ((cast ffi_inj) ffi_ret)
  
let verified_eq _ _ = true
