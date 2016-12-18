module FStar.DM4F.State

assume val precede_app (#a #b : Type) (f : a -> Tot b) (x:a) : Lemma (requires True) (ensures (f x << f))
let apply (#a #b : Type) (f : a -> Tot b) (x:a) : Pure b (requires True) (ensures (fun r -> r == f x /\ r << f)) =
    precede_app f x ; f x





let cps (datatype : Type0 -> Type0 -> Tot Type0) (ans a:Type0) : Type = (datatype ans a -> M ans) -> M ans


noeq type free_state0 (ans a:Type0) =
  | Return : (unit -> M a) -> free_state0 ans a
  | Write : int -> cps free_state0 ans a -> free_state0 ans a
  | Read : f:(int -> cps free_state0 ans a) -> free_state0 ans a

let free_state (ans a:Type0) = cps free_state0 ans a


let rec normalize_aux (#ans #a:Type0) n m0 =
  fun cont ->
    match m0 with
    | Return x -> cont (Write n (fun cont -> cont (Return x)))
    | Write n' m' -> m' (fun m0 -> normalize_aux n' m0 cont)
    | Read f -> f n (fun m0 -> normalize_aux n m0 cont)

let normalize (#ans #a:Type0) (m:free_state ans a) =
  fun cont ->
    m (fun m0 -> cont (Read (fun n -> normalize_aux n m0)))





(* noeq monadic type free_state (a:Type0) = *)
(*   | Return : (unit -> M a) -> M (free_state a) *)
(*   | Write : int -> M (free_state a) -> M (free_state a) *)
(*   | Read : f:(int -> M (free_state a)) -> M (free_state a) *)

(* let is_normalized m = *)
(*   Read? m /\ (forall (n:int). match Read?.f m n with | Write _ (Return _) -> True | _ -> False) *)

(* let state (a:Type) = m:(M (free_state a)){is_normalized m} *)

(* let rec normalize_aux (#a:Type0) (m : free_state a) (n:int) *)
(*         : Pure (M (free_state a)) *)
(*                (requires True) *)
(*                (ensures (fun m -> match m with | Write _ (Return _) -> True | _ -> False)) *)
(*                (decreases m) *)
(* = *)
(*   match m with *)
(*   | Return x -> Write n (Return x) *)
(*   | Write n' m' -> normalize_aux m' n' *)
(*   | Read f -> normalize_aux (apply f n) n *)

(* let normalize (#a:Type0) (m : free_state a) : (m':(M (free_state a)){is_normalized1 m'}) = *)
(*   Read (normalize_aux m) *)
