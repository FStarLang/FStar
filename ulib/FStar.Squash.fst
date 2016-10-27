module FStar.Squash

(* This file shows that there is another natural partial model for
   some of the squash things *)

let get_proof (p:Type) = ()

let give_proof (#p:Type) _ = ()

let proof_irrelevance (p:Type) x y = ()

(* CH: Couldn't use assume val for these guys, since then I was getting
       val squash_double_arrow is repeated in the implementation *)
let squash_double_arrow (#a:Type) (#p:(a -> Type)) f = magic()

let squash_double_sum (#a:Type) (#p:(a -> Type)) f = magic()

let return_squash (#a:Type) x = ()

let bind_squash (#a:Type) (#b:Type) f g = magic()

let map_squash (#a:Type) (#b:Type) s f =
  bind_squash #a #b s (fun x -> return_squash (f x))

let join_squash (#a:Type) (x:squash (squash a)) = bind_squash x (fun x -> x)
