(* Model implementation of FStar.All: verified, but never extracted (the real implementation is native).
   References are modeled as optional values, without a heap. *)
module FStar.All

type ref ([@@@ strictly_positive] a:Type0) : Type0 = | Ref : v:option a -> ref a

let nonempty_ref a = nonempty_intro (Ref #a None)

let rec loop (#a:Type) () : Dv a = loop ()

let alloc #a x = Ref (Some x)
let ( ! ) #a r = match Ref?.v r with Some x -> x | None -> loop ()
let ( := ) #a _ _ = ()

let exit _ = loop ()
let try_with f _ = f ()
let failwith s = FStar.Exn.raise (Failure s)
