(*--build-config
    options:--warn_top_level_effects;
    other-files:FStar.Squash.fsti;
--*)
module FStar.Squash

(* This file shows that there is a natural model for some of the squash things;
   DO NOT IMPORT THIS FILE; USE FStar.Squash.fsti and --admit_fsi FStar.Squash INSTEAD
 *)

type squash (t:Type) = t

let return_squash x = x

let bind_squash x f = f x

let map_squash x f = f x

(* Inconsistent, see #355 *)
assume val get_proof : p:Type ->
  Pure (squash p) (requires p) (ensures (fun _ -> True))

let give_proof (#p:Type) (s:squash p) = ()

(* Inconsistent *)
assume val proof_irrelevance : p:Type -> x:squash p ->
                                        y:squash p -> Tot (squash (x = y))

let squash_double_arrow (#a:Type) (#p:a -> Type) f = f
