module IfcEffect

open IFC

(* CH: partial file, moving to ifc.fst *)

let repr (a:Type) (wp:wp a) =
    n0:label -> PURE (option (a * label)) (wp n0)

inline val bind: (a:Type) -> (b:Type) -> (wp0:wp a) -> (wp1:(a -> Tot (wp b)))
		 -> (f:repr a wp0)
		 -> (g:(x:a -> Tot (repr b (wp1 x))))
		 -> Tot (repr b (bind_wp range_0 a b wp0 wp1))
let bind a b wp0 wp1 f g
  = fun n0 -> admit(); match f n0 with
		    | None -> None
		    | Some (x, n1) -> g x n1
let return (a:Type) (x:a)
  : repr a (return_wp a x)
  = fun n0 -> Some (x, n0)

(* The read and write actions are new, the rest of the effect definition old *)

assume val read : l:label ->
  Tot (repr bool (fun l0 (p:post bool) -> forall b. p (Some (b, join l0 l))))
(* dummy implementation works too
let read l = fun l0 -> Some (true, join l0 l) *)

assume val write : l:label -> b:bool ->
  Tot (repr unit (fun l0 (p:post unit) -> if flows l0 l then p (Some ((), l0))
                                                        else p None))
(* dummy implementation works too
let write l b = fun l0 -> if flows l0 l then (Some ((), l0)) else None *)

(* Normally we would remove reifiable reflectable below,
   but that's not yet supported *)
reifiable reflectable new_effect {
  ExnState : a:Type -> wp:wp a -> Effect
  with //repr is new; it's the reprentation of ST as a value type
       repr         = repr
       //bind_wp is exactly as it is currently
       //produced by the *-translation of bind above
     ; bind_wp      = bind_wp
       //bind is new, it is the elaboration of the bind above
     ; bind         = bind
      //return_wp is a renaming of the current return, it is the *-translation of the return above
     ; return_wp    = return_wp
      //return is new; it is the elaboration of the return above
     ; return       = return
     //the remaining are just as what we have now
     ; if_then_else = if_then_else
     ; ite_wp       = ite_wp
     ; stronger     = stronger
     ; close_wp     = close_wp
     ; assert_p     = assert_p
     ; assume_p     = assume_p
     ; null_wp      = null_wp
     ; trivial      = trivial
  and effect_actions
      read = read
    ; write = write
}

inline let lift_pure_exnst (a:Type) (wp:pure_wp a) (h0:label) (p:post a) = wp (fun a -> p (Some (a, h0)))
sub_effect PURE ~> ExnState = lift_pure_exnst

effect ExnSt (a:Type) (req:pre) (ens:label -> option (a * label) -> GTot Type0) =
       ExnState a
         (fun (h0:label) (p:post a) -> req h0 /\ (forall r. (req h0 /\ ens h0 r) ==> p r))

effect S (a:Type) =
       ExnState a (fun h0 p -> forall x. p x)

(* Here is where the more interesting part starts *)

val p : unit -> ExnSt unit (requires (fun l   -> True))
                           (ensures  (fun l r -> r = None))
let p () =
  let b1 = ExnState.read Low in
  let b2 = ExnState.read Low in
  ExnState.write Low (b1 && b2);
  let b3 = ExnState.read High in
  ExnState.write High (b1 || b3);
  ExnState.write Low (xor b3 b3)

(* [8:14:57 PM] Nik Swamy: I think for bonus points, in the ifc monad we could *)
(* [8:15:33 PM] Nik Swamy: 1. add outputs, a list of Booleans, e.g., and have the write cons to it *)
(* [8:15:48 PM] Nik Swamy: 2. add an input state so that read is not a constant *)
(* [8:16:23 PM] Nik Swamy: 3. do a relational proof of the p program showing that despite the exception, the outputs would be the same in 2 runs *)
