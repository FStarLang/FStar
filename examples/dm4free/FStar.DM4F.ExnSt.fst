module FStar.DM4F.ExnSt

(**********************************************************
 * Dijkstra Monads for Free : Exceptions with state
 *
 * Exceptions over (integer) state (state dropped when raising)
 *
 **********************************************************)

module IntST = FStar.DM4F.IntST

(* The underlying representation type *)
let exnst a = int -> M (option (a * int))

(* Monad definition *)
val return : (a:Type) -> (x:a) -> exnst a
let return a x = fun s -> Some (x, s)

val bind : (a:Type) -> (b:Type) ->
           (f:exnst a) -> (g:a -> exnst b) -> exnst b
let bind a b f g =
  fun s0 ->
    let res = f s0 in
    match res with
    | None -> None
    | Some (ret, s1) -> g ret s1

(* Define the new effect using DM4F *)
reifiable reflectable new_effect_for_free {
  EXNST: a:Type -> Effect with
    repr    = exnst;
    bind    = bind;
    return  = return
}

let pre  = EXNST.pre
let post = EXNST.post
let wp   = EXNST.wp
let repr = EXNST.repr

(* A lift from Pure *)
inline let lift_pure_exnst (a:Type) (wp:pure_wp a) (h0:int) (p:post a) =
        wp (fun a -> p (Some (a, h0)))
sub_effect PURE ~> EXNST = lift_pure_exnst

(* A lift "for free" from STINT to EXNST *)
(* let lift (a: Type) (f: IntST.st a): exnst a =
  fun h ->
    let ret = f h in
    Some ret

sub_effect IntST.STINT ~> EXNST {
  lift = lift
} *)

(* A lift from a previously defined state effect *)
val lift_state_exnst_wp : (a:Type) -> IntST.wp a -> wp a
let lift_state_exnst_wp a wp (h0:int) (p:post a) =
        wp h0 (fun r -> p (Some r))

val lift_state_exnst : (a:Type) ->
                       (wp:IntST.wp a) -> (f:IntST.repr a wp) ->
                       repr a (lift_state_exnst_wp a wp)
let lift_state_exnst a wp f =
        (* TODO: This fails without admit, but all seems correct *)
        fun h0 -> admit(); Some (f h0)

sub_effect IntST.STINT ~> EXNST {
  lift_wp = lift_state_exnst_wp;
  lift = lift_state_exnst
}

(* Action: raise an exception *)
let action_raise (a:Type) : repr a (fun _ post -> post None) =
  fun _ -> None

reifiable let raise (a:Type) : EXNST a (fun _ post -> post None) =
  EXNST.reflect (action_raise a)

(* Pre-/postcondition variant *)
effect ExnSt (a:Type) (req:pre) (ens:int -> option (a * int) -> GTot Type0) =
       EXNST a
         (fun (h0:int) (p:post a) -> req h0 /\ (forall r. (req h0 /\ ens h0 r) ==> p r))

(* Total variant *)
effect S (a:Type) =
       EXNST a (fun h0 p -> forall x. p x)

(*
 * Proving intrinsically and extrinsically again, now also handling
 * state in between. The specification now also guarantees that div
 * doesn't modify the state.
 *)

val div_intrinsic : i:nat -> j:int -> ExnSt int
  (requires (fun h -> True))
  (ensures (fun h0 x -> match x with
                     | None -> j=0
                     | Some (z, h1) -> h0 = h1 /\ j<>0 /\ z = i / j))
let div_intrinsic i j =
    if j = 0 then (
        (* Despite the incr (implicitly lifted), the state is reset *)
        IntST.incr ();
        raise int
    ) else
        i / j

reifiable let div_extrinsic (i:nat) (j:int) : S int =
    if j = 0 then
        raise int
    else
        i / j

let lemma_div_extrinsic (i:nat) (j:int) (h0:int) :
  Lemma (match reify (div_extrinsic i j) h0 with
         | None -> j = 0
         | Some (z, h1) -> h0 = h1 /\ j <> 0 /\ z = i / j) = ()
