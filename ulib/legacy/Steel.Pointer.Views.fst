module Steel.Pointer.Views

module A = Steel.Array
module HS = FStar.HyperStack
module P = LowStar.Permissions

open Steel.RST


(* View and resource for (heap-allocated, freeable) pointer resources *)

let pointer (t: Type) = ptr:A.array t{A.vlength ptr == 1}

noeq type vptr (a: Type) = {
  ptr_x: a;
  ptr_p: P.permission
}

let ptr_resource (#a:Type) (ptr:pointer a) : resource =
  refine_view (A.array_resource ptr) (fun (av: A.varray ptr) ->
    { ptr_x = Seq.index av.A.s 0; ptr_p = av.A.p }
  )

let get_val
  (#a: Type)
  (ptr: pointer a)
  (#r: resource{ptr_resource #a ptr `is_subresource_of` r})
  (h: rmem r) : GTot a =
  (h (ptr_resource ptr)).ptr_x

let get_perm
  (#a: Type)
  (ptr: pointer a)
  (#r: resource{ptr_resource #a ptr `is_subresource_of` r})
  (h: rmem r) : GTot P.permission =
  let v : vptr a = h (ptr_resource ptr) in
  v.ptr_p
