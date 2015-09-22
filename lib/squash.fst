(*--build-config
    options:--warn_top_level_effects;
    other-files:constr.fst classical.fst squash.fsti;
--*)
module FStar.Squash

(* This file shows that there is a natural model some of the squash things;
   DO NOT IMPORT THIS FILE; USE squash.fsti and --admit_fsi FStar.Squash INSTEAD
 *)

type squash (t:Type) = t

let return_squash x = x

let bind_squash x f = f x

let map_squash x f = f x

assume val get_proof : p:Type ->
  Pure (squash p) (requires p) (ensures (fun _ -> True))

assume val give_proof : #p:Type -> squash p ->
  Pure unit (requires True) (ensures (fun _ -> p))

assume val proof_irrelevance : p:Type -> x:squash p ->
                                         y:squash p -> Tot (squash (x = y))
