type 'a ref = 'a FStar_ST.ref

(*
 * TODO: null and is_null?
 *)

let alloc = FStar_ST.alloc

let read (perm:unit) (v:unit) (r:'a ref) = FStar_ST.read r

let read_refine (perm:unit) (q:unit) (r:'a ref) = read () () r

let write (v:unit) (r:'a ref) (x:'a) = FStar_ST.write r x

let free (v:unit) (r:'a ref) = raise (Steel_Common.Steel_function_unsupported "free")
