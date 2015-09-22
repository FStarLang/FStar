(*--build-config
    options:--warn_top_level_effects;
    other-files:constr.fst classical.fst squash.fsti;
--*)
module FStar.Squash

type squash (t:Type) = t

let return_squash x = x

let bind_squash x f = f x

let map_squash x f = f x

assume val get_proof : p:Type ->
  Pure (squash p) (requires p) (ensures (fun _ -> True))

assume val give_proof : #p:Type -> squash p ->
  Pure unit (requires True) (ensures (fun _ -> p))
