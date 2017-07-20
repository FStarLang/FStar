module FStar.StateInt

open FStar.WellFounded
open FStar.FunctionalExtensionality

/// We try to recover the state monad from its presentation.
/// We restrict ourself to only one cell containing an integer in order to
/// keep the presentation simple.


/// The state monad can be given by the following presentation
///
/// One lookup/read operation whose arity depends on the content of the cell
/// (in our case the arity is \aleph_0 since we store an integer)
/// For each possible cell content [n] we are giving a continuation
///
///    Read : (int -> state a) -> state a
///
/// A write operation for each potential element in the store
///
///    Write : int -> state a -> state a
///
/// There are then 3 equations relating these operations
///
///   Write p (Write q cont) == Write q cont
///   Write p (Read f) == Write p (f p)
///   Read (fun p -> Write p cont) == cont
///
/// It can then be proved that orientating correctly these equations leads
/// to a strongly normalizing and confluent rewriting system whose normal
/// forms are given by
///
///    Read (fun n -> Write (f n) (Return (g n)))
///
/// This normal form means exactly that elements of [state a] are of the form
///
///    int -> a * int


/// We first define the operations
noeq type free_state (a:Type0) =
  | Return : a -> free_state a
  | Write : int -> free_state a -> free_state a
  | Read : f:(int -> free_state a) -> free_state a

/// and the normal forms
let is_normalized1 m =
  Read? m /\ (forall (n:int). match Read?.f m n with | Write _ (Return _) -> True | _ -> False)

let is_normalized = is_normalized1

/// which allows us to carve out the subtype of state
let state (a:Type) = m:(free_state a){is_normalized m}


/// We then proceed by defining a normalization procedure
/// [normalize m] maps a free_state [m] to its normal form

(* This is missing in baked in F^* (<<) *)
assume val precede_app (#a #b : Type) (f : a -> Tot b) (x:a)
  : Lemma (requires True) (ensures (f x << f))
let apply (#a #b : Type) (f : a -> Tot b) (x: a)
  : Pure b (requires True) (ensures (fun r -> r == f x /\ f x << f))
= precede_app f x ; f x

(* Need to be toplevel because of #786 *)
let rec normalize_aux (#a:Type0) (m : free_state a) (n:int)
        : Pure (free_state a)
               (requires True)
               (ensures (fun m -> match m with | Write _ (Return _) -> True | _ -> False))
               (decreases m)
=
  match m with
  | Return x -> Write n (Return x)
  | Write n' m' -> normalize_aux m' n'
  | Read f -> normalize_aux (apply f n) n

let normalize (#a:Type0) (m : free_state a) : (m':(free_state a){is_normalized1 m'}) =
  Read (normalize_aux m)

(* let is_normalized0 m = m == normalize m *)
(* let is_normalized2 m = *)
(*   (exists m'. {:pattern normalize m'} m == (normalize m' <: free_state _)) *)


/// We can now define the monadic operations

let return (#a:Type) (x:a) : state a = normalize (Return x)
let bind (#a #b : Type) (m : state a) (f : a -> state b) : state b =
  Read (fun n -> match Read?.f m n with
              | Write n' (Return x) -> Read?.f (f x) n')


/// And try to show that we verify the monadic laws

let unit_left (a b:Type) (x:a) (f : a -> state b) = assert_norm (bind (return x) f == f x)

let unit_right (a:Type) (x: state a) =
  assert (forall n. Read?.f (bind x return) n == Read?.f x n) ;
  assert (Read?.f (bind x return) `feq` Read?.f x) ;
  assert (bind x return == x)

let assoc (a b c : Type) (x: state a) (f : a -> state b) (g : b -> state c) =
  assert (forall n. Read?.f (bind x (fun x0 -> bind (f x0) g)) n ==
               Read?.f (bind (bind x f) g) n) ;
  assert (Read?.f (bind x (fun x0 -> bind (f x0) g)) `feq` Read?.f (bind (bind x f) g)) ;
  assert (bind x (fun x0 -> bind (f x0) g) == bind (bind x f) g)
