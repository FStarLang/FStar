module FStar.DM4F.ExnSt

open FStar.DM4F

let stexn a = int -> M (option (a * int))

let return (a: Type) (x: a): stexn a =
  fun s -> Some (x, s)

let bind (a: Type) (b: Type) (f: stexn a) (g: a -> stexn b): stexn b =
  fun s0 ->
    let res = f s0 in
    match res with
    | None -> None
    | Some (ret, s1) -> g ret s1

reifiable reflectable new_effect_for_free {
  EXNST: a:Type -> Effect with
    repr = stexn;
    bind = bind;
    return = return
}

let pre = int -> Type0
let post (a:Type) = option (a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0

let repr (a:Type) (wp:wp a) =
    n0:int -> PURE (option (a * int)) (wp n0)

inline let lift_pure_exnst (a:Type) (wp:pure_wp a) (h0:int) (p:post a) = wp (fun a -> p (Some (a, h0)))
sub_effect PURE ~> EXNST = lift_pure_exnst

let lift_state_exnst_wp (a:Type) (wp:IntST.wp a) (h0:int) (p:post a) = wp h0 (function (x, h1) -> p (Some (x, h1)))
let lift_state_exnst (a:Type) (wp:IntST.wp a) (f:IntST.repr a wp)
  : (repr a (lift_state_exnst_wp a wp))
  = fun h0 -> admit(); Some (f h0)

sub_effect IntST.STINT ~> EXNST {
  lift_wp = lift_state_exnst_wp;
  lift = lift_state_exnst
}

let action_raise (a: Type): repr a (fun _ post -> post None) =
  fun _ -> None

reifiable let raise (a: Type): EXNST a (fun _ post -> post None) =
  EXNST.reflect (action_raise a)

effect ExnSt (a:Type) (req:pre) (ens:int -> option (a * int) -> GTot Type0) =
       EXNST a
         (fun (h0:int) (p:post a) -> req h0 /\ (forall r. (req h0 /\ ens h0 r) ==> p r))

effect S (a:Type) =
       EXNST a (fun h0 p -> forall x. p x)

val div_intrinsic : i:nat -> j:int -> ExnSt int
  (requires (fun h -> True))
  (ensures (fun h0 x -> match x with
		     | None -> j=0
		     | Some (z, h1) -> h0 = h1 /\ j<>0 /\ z = i / j))
let div_intrinsic i j =
  if j=0
  then (IntST.incr (); raise int) //despite the incr (implicitly lifted), the state is reset
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : S int =
  if j=0 then raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) 0 with
         | None -> j = 0
	 | Some (z, 0) -> j <> 0 /\ z = i / j) = ()
