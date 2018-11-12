module FStar.DM4F.StExnC

(**********************************************************
 * Dijkstra Monads for Free : State with exceptions
 *
 * State over exceptions (state kept when raising).
 *
 * We don't define a get and put, but instead use the state
 * for counting the amount of exceptions thrown.
 *
 **********************************************************)

(* The underlying representation type. The two ints are
 * resulting state and exception count, respectively. *)
let stexnc a =
  int -> M (option a * (int * int))

(* Monad definition *)
val return : (a:Type) -> (x:a) -> stexnc a
let return a x = fun s -> Some x, (s, 0)

val bind : (a:Type) -> (b:Type) ->
           (m:stexnc a) -> (f:a -> stexnc b) -> stexnc b
let bind a b m f =
  fun s0 ->
    let r0 = m s0 in
    match r0 with
    | None, (s1, c1) -> None, (s1, c1)
    | Some r, (s1, c1) -> let res, (s, c2) = f r s1
                           in res, (s, c1 + c2)

let raise (a:Type) : stexnc a = fun s0 -> (None, (s0, 1))

(*
 * Define the new effect using DM4F. We don't mark it as reflectable
 * so we know the invariant of exception-counting is enforced
 *)
total reifiable new_effect {
  STEXNC: a:Type -> Effect
  with repr    = stexnc
     ; return  = return
     ; bind    = bind
     ; raise   = raise
}

(* A lift from Pure *)
unfold let lift_pure_stexnc (a:Type) (wp:pure_wp a) (h0:int) (p:STEXNC?.post a) =
        wp (fun a -> p (Some a, (h0, 0)))
sub_effect PURE ~> STEXNC = lift_pure_stexnc

(* NOTE: no lift from STEXN to STEXNC, since that would break
         the abstraction of counting exceptions *)

(* Pre-/postcondition variant *)
effect StExnC (a:Type) (req:STEXNC?.pre)
                       (ens:int -> option a -> int -> int -> GTot Type0) =
       STEXNC a
         (fun (h0:int) (p:STEXNC?.post a) -> req h0
          /\ (forall (r:option a) (h1:int) (c:int).
                 (req h0 /\ ens h0 r h1 c) ==> p (r, (h1, c))))

(* Total variant *)
effect SC (a:Type) =
       STEXNC a (fun h0 p -> forall x. p x)

(* This rightfully fails, since STEXNC is not reflectable *)

(* val f_impl : (a:Type) -> STEXNC?.repr a (fun h0 post -> post (None, (h0, 0))) *)
(* let f_impl a = fun h0 -> None, (h0, 0) *)

(* let f (a:Type) : STEXNC a (fun h0 post -> post (None, (h0, 0))) = *)
(*         STEXNC?.reflect (f_impl a) *)

val div_intrinsic : i:nat -> j:int -> StExnC int
  (requires (fun h -> True))
  (ensures (fun h0 x h1 c -> match x with
                        | None -> h0 = h1 /\ c = 1 /\ j = 0
                        | Some z -> h0 = h1 /\ c = 0 /\ j <> 0 /\ z = i / j))
let div_intrinsic i j = 
  if j = 0 then STEXNC?.raise int
  else i / j

 let div_extrinsic (i:nat) (j:int) : SC int =
  if j = 0 then STEXNC?.raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) (h0:int) :
  Lemma (match reify (div_extrinsic i j) h0 with
         | None, (h1, 1) -> h1 = h0 /\ j = 0
         | Some z, (h1, 0) -> h1 = h0 /\ j <> 0 /\ z = i / j) = ()
