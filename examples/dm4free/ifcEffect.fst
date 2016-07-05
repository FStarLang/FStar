module IfcEffect

open IFC

(* This first part is a copy of most exnst, with int replaced by label *)

let pre = label -> Type0
let post (a:Type) = option (a * label) -> Type0
let wp (a:Type) = label -> post a -> Type0
inline let return_wp (a:Type) (x:a) (n0:label) (post:post a) =
  forall y. y=Some (x, n0) ==> post y

//working around #517 by adding an explicit 'val'
inline val bind_wp : r:range -> (a:Type) -> (b:Type) -> (f:wp a) -> (g:(a -> Tot (wp b))) -> Tot (wp b)
let bind_wp r a b f g =
    fun n0 post -> f n0 (function
        | None -> post None
	| Some (x, n1) -> g x n1 post)

inline let if_then_else  (a:Type) (p:Type)
                         (wp_then:wp a) (wp_else:wp a)
                         (h0:label) (post:post a) =
     l_ITE p
        (wp_then h0 post)
	(wp_else h0 post)
inline let ite_wp        (a:Type)
                         (wp:wp a)
                         (h0:label) (post:post a) =
  wp h0 post
inline let stronger  (a:Type) (wp1:wp a) (wp2:wp a) =
     (forall (p:post a) (h:label). wp1 h p ==> wp2 h p)

inline let close_wp      (a:Type) (b:Type)
                            (wp:(b -> GTot (wp a)))
                            (h:label) (p:post a) =
     (forall (b:b). wp b h p)
inline let assert_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:label) (q:post a) =
     p /\ wp h q
inline let assume_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:label) (q:post a) =
     p ==> wp h q
inline let null_wp       (a:Type)
                         (h:label) (p:post a) =
     (forall x. p x)
inline let trivial       (a:Type)
                            (wp:wp a) =
     (forall h0. wp h0 (fun r -> True))

//new
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

new_effect {
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
                           (ensures  (fun l r -> True))
let p () =
  (* let b1, b2 = read Low, read Low in *)
  let b1 = ExnState.read Low in ()

(*
  let b2 = ExnState.read Low in
  ExnState.write Low (b1 && b2);
  let b3 = ExnState.read High in
  ExnState.write High (b1 || b3);
  ExnState.write Low (xor b3 b3)
*)
