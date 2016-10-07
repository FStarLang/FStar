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

(* TODO: parametrize heap? not sure that it can be done easily:
 *       we can't write a lift unless we instantiate it to a proper
 *       effect, and using FStar.DM4F.Heap does not give us an
 *       equality comparison of heaps, difficulting our last example.
 *)

(* The underlying representation type. The two ints are
 * resulting state and exception count, respectively. *)
let stexnc a =
  int -> M (option a * (int * int))

(* Monad definition *)
val return : (a:Type) -> (x:a) -> stexnc a
let return a x = fun s -> Some x, (s, 0)

val bind : (a:Type) -> (b:Type) ->
           (f:stexnc a) -> (g:a -> stexnc b) -> stexnc b
let bind a b f g =
  fun s0 ->
    (* TODO: need to letbind f s0 to match on it; expected? idem grs1 *)
    let fs0 = f s0 in
    match fs0 with
    | None, (s1, c1) -> None, (s1, c1)
    | Some r, (s1, c1) -> let grs1 = g r s1 in
                          match grs1 with
                          | res, (s, c2) -> res, (s, c1 + c2)

let put (s:int) : stexnc unit =
        fun s0 -> (Some (), (s0, 0))

let get (_:unit) : stexnc int =
        fun s0 -> (Some s0, (s0, 0))

(* Same error as StExn *)
//let raise (a:Type) : stexnc a =
//        fun s0 -> (None, (s0, 1))

(*
 * Define the new effect using DM4F. We don't mark it as reflectable
 * so we know the invariant of exception-counting is enforced
 *)
(* TODO: remove reflectable *)
reifiable reflectable new_effect_for_free {
  STEXNC: a:Type -> Effect
  with repr    = stexnc
     ; return  = return
     ; bind    = bind
  and effect_actions
       put     = put
     ; get     = get
     //; raise   = raise
}

let pre  = STEXNC.pre
let post = STEXNC.post
let wp   = STEXNC.wp
let repr = STEXNC.repr

(* A lift from Pure *)
inline let lift_pure_stexnc (a:Type) (wp:pure_wp a) (h0:int) (p:post a) =
        wp (fun a -> p (Some a, (h0, 0)))
sub_effect PURE ~> STEXNC = lift_pure_stexnc

(* NOTE: no lift from STEXN to STEXNC, since that would break
         the abstraction of counting exceptions *)

(* Pre-/postcondition variant *)
effect StExnC (a:Type) (req:pre) (ens:int -> option a -> int -> int -> GTot Type0) =
       STEXNC a
         (fun (h0:int) (p:post a) -> req h0
          /\ (forall (r:option a) (h1:int) (c:int).
                 (req h0 /\ ens h0 r h1 c) ==> p (r, (h1, c))))

(* Total variant *)
effect SC (a:Type) =
       STEXNC a (fun h0 p -> forall x. p x)

(* This rightfully fails, since STEXNC is not reflectable *)

// val f_impl : (a:Type) -> repr a (fun h0 post -> post (None, (h0, 0)))
// let f_impl a = fun h0 -> None, (h0, 0)
//
// reifiable let f (a:Type) : STEXNC a (fun h0 post -> post (None, (h0, 0))) =
//         STEXNC.reflect (f_impl a)

(* TODO: remove and make proper action *)
val raise_impl : (a:Type) -> repr a (fun h0 p -> p (None, (h0, 1)))
let raise_impl a h0 = (None, (h0, 1))

reifiable val raise : (a:Type) -> STEXNC a (fun h0 p -> p (None, (h0, 1)))
reifiable let raise a = STEXNC.reflect (raise_impl a)

val div_intrinsic : i:nat -> j:int -> StExnC int
  (requires (fun h -> True))
  (ensures (fun h0 x h1 c -> match x with
                        | None -> h0 = h1 /\ c = 1 /\ j = 0
                        | Some z -> h0 = h1 /\ c = 0 /\ j <> 0 /\ z = i / j))
let div_intrinsic i j =
  if j = 0 then raise int
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : SC int =
  if j = 0 then raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) (h0:int) :
  Lemma (match reify (div_extrinsic i j) h0 with
         | None, (h1, 1) -> h1 = h0 /\ j = 0
         | Some z, (h1, 0) -> h1 = h0 /\ j <> 0 /\ z = i / j) = ()
