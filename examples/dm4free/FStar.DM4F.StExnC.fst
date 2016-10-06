module FStar.DM4F.StExn

(**********************************************************
 * Dijkstra Monads for Free : State with exceptions
 *
 * State over exceptions (state kept when raising).
 *
 * We don't define a get and put, but instead use the state
 * for counting the amount of exceptions thrown.
 *
 **********************************************************)

(* TODO: parametrize heap? *)

(* The underlying representation type. The two ints are
 * resulting state and exception count, respectively. *)
let stexn a =
  int -> M (option a * (int * int))

(* Monad definition *)
val return : (a:Type) -> (x:a) -> stexn a
let return a x = fun s -> Some x, (s, 0)

val bind : (a:Type) -> (b:Type) ->
           (f:stexn a) -> (g:a -> stexn b) -> stexn b
let bind a b f g =
  fun s0 ->
    (* TODO: need to letbind f s0 to match on it; expected? idem grs1 *)
    let fs0 = f s0 in
    match fs0 with
    | None, (s1, c1) -> None, (s1, c1)
    | Some r, (s1, c1) -> let grs1 = g r s1 in
                          match grs1 with
                          | res, (s, c2) -> res, (s, c1 + c2)

let put (s:int) : stexn unit =
        fun s0 -> (Some (), (s0, 0))

let get (_:unit) : stexn int =
        fun s0 -> (Some s0, (s0, 0))

(* Same error as StExn *)
let raise (a:Type) : stexn a =
        fun s0 -> (None, (s0, 1))

(*
 * Define the new effect using DM4F. We don't mark it as reflectable
 * so we know the invariant of exception-counting is enforced
 *)
reifiable new_effect_for_free {
  STEXN: a:Type -> Effect
  with repr    = stexn
     ; return  = return
     ; bind    = bind
  and effect_actions
       put     = put
     ; get     = get
     ; raise   = raise
}

let pre  = STEXN.pre
let post = STEXN.post
let wp   = STEXN.wp
let repr = STEXN.repr

(* A lift from Pure *)
inline let lift_pure_stexn (a:Type) (wp:pure_wp a) (h0:int) (p:post a) =
        wp (fun a -> p (Some a, (h0, 0)))
sub_effect PURE ~> STEXN = lift_pure_stexn

(* NOTE: no lift from IntST.STATE to StateExn, since that would break
         the abstraction of counting exceptions *)

(* TODO: but why? there are no exception in IntST. Maybe StExn is meant?  *)

(* Pre-/postcondition variant *)
effect StExn (a:Type) (req:pre) (ens:int -> option a -> int -> int -> GTot Type0) =
       STEXN a
         (fun (h0:int) (p:post a) -> req h0
          /\ (forall (r:option a) (h1:int) (c:int).
                 (req h0 /\ ens h0 r h1) ==> p (r, (h1, c))))

(* Total variant *)
effect S (a:Type) =
       STEXN a (fun h0 p -> forall x. p x)

(* This rightfully fails, since StateExn is not reflectable *)

// reifiable let f (a:Type) : STEXN a (fun h0 post -> post (None, h0)) =
//         STEXN.reflect (fun h0 -> None, h0)

val div_intrinsic : i:nat -> j:int -> StExn int
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> match x with
                        | None -> h0 + 1 = h1 /\ j=0
                        | Some z -> h0 = h1 /\ j<>0 /\ z = i / j))
let div_intrinsic i j =
  if j=0 then raise int
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : S int =
  if j=0 then raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) 0 with
         | None, 1 -> j = 0
         | Some z, 0 -> j <> 0 /\ z = i / j) = ()
