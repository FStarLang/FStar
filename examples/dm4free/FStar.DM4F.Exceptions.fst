module FStar.DM4F.Exceptions

let ex (a:Type) = 
  unit -> M (option a)

val return_ex : a:Type -> x:a -> ex a
let return_ex a x = fun _ -> Some x

val bind_ex : a:Type -> b:Type -> f:ex a -> g:(a -> ex b) -> ex b
let bind_ex a b f g = fun _ -> 
  let r = f () in 
  match r with 
  | None -> None
  | Some x -> g x ()

(* #set-options "--debug FStar.DM4F.Exceptions --debug_level Extreme --print_universes --print_implicits" *)
reifiable reflectable new_effect_for_free {
  EXN : a:Type -> Effect
  with
    repr         = ex
  ; bind         = bind_ex
  ; return       = return_ex
}


let ex_pre = Type0
let ex_post (a:Type) = option a -> Type0
let ex_wp (a:Type) = unit -> ex_post a -> Type0

inline let lift_pure_ex (a:Type) (wp:pure_wp a) (_:unit) (p:ex_post a) = wp (fun a -> p (Some a))
sub_effect PURE ~> EXN = lift_pure_ex

effect Exn (a:Type) (pre:ex_pre) (post:ex_post a) =
       EXN a
         (fun (_:unit) (p:ex_post a) -> pre /\ (forall (r:option a). (pre /\ post r) ==> p r)) (* WP *)

effect Ex (a:Type) = //(pre:ex_pre) (post:ex_post a) ...adding this mistakenly causes a crash!
       EXN a (fun _ p -> forall x. p x)

let ex_repr (a:Type) (wp:ex_wp a) =
    unit -> PURE (option a) (wp ())

val raise_ : a:Type -> Tot (ex_repr a (fun (_:unit) (p:ex_post a) -> p None))
let raise_ a (_:unit) = None

//You can also build a new action "on the fly" using reflect
reifiable let raise (a:Type) : Exn a True (fun r -> r==None)
  = EXN.reflect (raise_ a)

val div_intrinsic : i:nat -> j:int -> Exn int
  (requires True)
  (ensures (function None -> j=0 | Some z -> j<>0 /\ z = i / j))
let div_intrinsic i j =
  if j=0 then raise int
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : Ex int =
  if j=0 then raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) () with
         | None -> j = 0
	 | Some z -> j <> 0 /\ z = i / j) = ()

