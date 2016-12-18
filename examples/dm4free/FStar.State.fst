module FStar.State

(** We try to recover the state monad from its presentation.                 **
 ** See FStar.StateInt for an explanation in the case where the state is int **)

(** We first define the operations **)
noeq type free_state (s a:Type0) =
  | Return : a -> free_state s a
  | Write : s -> free_state s a -> free_state s a
  | Read : f:(s -> free_state s a) -> free_state s a

(** and the normal forms **)
let is_normalized1 (#s #a:Type) (m : free_state s a) =
  Read? m /\ (forall (n:s). match Read?.f m n with | Write _ (Return _) -> True | _ -> False)

let is_normalized = is_normalized1

(** which allows us to carve out the subtype of state **)
let state (s a:Type) = m:(free_state s a){is_normalized m}


(** We then proceed by defining a normalization procedure  **
 ** [normalize m] maps a free_state [m] to its normal form **)

(* This is missing in baked in F^* (<<) *)
assume val precede_app (#a #b : Type) (f : a -> Tot b) (x:a)
  : Lemma (requires True) (ensures (f x << f))
let apply (#a #b : Type) (f : a -> Tot b) (x: a)
  : Pure b (requires True) (ensures (fun r -> r == f x /\ f x << f))
= precede_app f x ; f x

(* Need to be toplevel because of #786 *)
let rec normalize_aux (#s #a:Type0) (m : free_state s a) (n:s)
        : Pure (free_state s a)
               (requires True)
               (ensures (fun m -> match m with | Write _ (Return _) -> True | _ -> False))
               (decreases m)
=
  match m with
  | Return x -> Write n (Return x)
  | Write n' m' -> normalize_aux m' n'
  | Read f -> normalize_aux (apply f n) n

let normalize (#s #a:Type0) (m : free_state s a) : (m':(free_state s a){is_normalized1 m'}) =
  Read (normalize_aux m)

(** We can now define the monadic operations **)

let return (#s #a:Type) (x:a) : state s a = normalize (Return x)
let bind (#s #a #b : Type) (m : state s a) (f : a -> state s b) : state s b =
  Read (fun n -> match Read?.f m n with
              | Write n' (Return x) -> Read?.f (f x) n')


(** And try to show that we verify the monadic laws **)

let unit_left (s a b:Type) (x:a) (f : a -> state s b) = assert_norm (bind (return x) f == f x)

(* TODO : These two equations need some amount of functional extensionality *)
let unit_right (s a:Type) (x: state s a) =
  admit () ; assert_norm (bind x return == x)
let assoc (s a b c : Type) (x: state s a) (f : a -> state s b) (g : b -> state s c)
= admit() ; assert (bind x (fun x0 -> bind (f x0) g) == bind (bind x f) g)
