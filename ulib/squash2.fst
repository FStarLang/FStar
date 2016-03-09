(*--build-config
    options:--warn_top_level_effects;
    other-files:FStar.Squash.fsti;
--*)
module FStar.Squash

(* This file shows that there is another natural model for some of the
   squash things; for this one it doesn't seem to harm importing this
   file (exposing the implementation); it probably doesn't help either *)

type squash (t:Type) = u:unit{t}

let return_squash x = ()

assume val bind_squash : #a:Type -> #b:Type -> squash a -> 
  (a -> Tot (squash b)) -> Tot (squash b)

let map_squash (#a:Type) (#b:Type) s f = 
  bind_squash #a #b s (fun x -> return_squash (f x))
  
let get_proof (p:Type) = ()

let give_proof (p:Type) _ = ()

let proof_irrelevance (p:Type) x y = ()

assume val squash_double_arrow : #a:Type -> #p:(a -> Type) ->
  =f:(squash (x:a -> Tot (squash (p x)))) -> Tot (squash (x:a -> Tot (p x)))
