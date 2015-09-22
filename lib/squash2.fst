(*--build-config
    options:--warn_top_level_effects;
    other-files:squash.fsti;
--*)
module FStar.Squash

(* This file shows that there is another natural model for some of the
   squash things; for this one it doesn't seem to harm importing this
   file (exposing the implementation); it probably doesn't help either *)

type squash (t:Type) = u:unit{t}

assume val return_squash : #a:Type -> a -> Tot (squash a)

assume val bind_squash : #a:Type -> #b:Type -> squash a -> (a -> Tot (squash b)) ->
  Tot (squash b)

assume val map_squash : #a:Type -> #b:Type -> squash a -> (a -> Tot b) ->
  Tot (squash b)

val get_proof : p:Type ->
  Pure (squash p) (requires p) (ensures (fun _ -> True))
let get_proof (p:Type) = ()

val give_proof : #p:Type -> squash p ->
  Pure unit (requires True) (ensures (fun _ -> p))
let give_proof (p:Type) _ = ()

val proof_irrelevance : p:Type -> x:squash p ->
                                  y:squash p -> Tot (squash (x = y))
let proof_irrelevance (p:Type) x y = ()

assume val squash_double_arrow : #a:Type -> #p:(a -> Type) ->
  =f:(squash (x:a -> Tot (squash (p x)))) -> Tot (squash (x:a -> Tot (p x)))
