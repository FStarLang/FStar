(* Interface for squash types; somehow inspired by:
   Quotient Types: A Modular Approach. Aleksey Nogin, TPHOLs 2002.
   http://www.nuprl.org/documents/Nogin/QuotientTypes_02.pdf
*)
module FStar.Squash

(* NS: This is really not the right model for squash.
       It doesn't demote the universe back to 0.
       We should use Prims.squash
*)

(* This file shows that there is a natural model for some of the squash things;
 *)

abstract type squash (t:Type) = t

abstract val give_proof : #p:Type -> squash p ->
  Pure unit (requires True) (ensures (fun _ -> p))

abstract val proof_irrelevance : p:Type -> x:squash p ->
                                 y:squash p -> Tot (squash (x = y))

abstract val squash_double_arrow : #a:Type -> #p:(a -> Type) ->
  =f:(squash (x:a -> Tot (squash (p x)))) -> Tot (squash (x:a -> Tot (p x)))

(* This is a monad, but not an effect *)

abstract val return_squash : #a:Type -> a -> Tot (squash a)

abstract val bind_squash : #a:Type -> #b:Type -> squash a -> (a -> Tot (squash b)) ->
  Tot (squash b)

abstract val map_squash : #a:Type -> #b:Type -> squash a -> (a -> Tot b) ->
  Tot (squash b)

let return_squash #a x = x

let bind_squash #a #b x f = f x

let map_squash #a #b x f = f x

let give_proof #p s = ()

let squash_double_arrow #a #p f = f

(* Inconsistent *)
assume val proof_irrelevance : p:Type -> x:squash p ->
                                        y:squash p -> Tot (squash (x = y))

(* Inconsistent, see #355 *)
assume val get_proof : p:Type ->
  Pure (squash p) (requires p) (ensures (fun _ -> True))
