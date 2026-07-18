module UvarPatternBug

noeq
[@@erasable]
type injection (a b : Type) = {
  f : a -> GTot b;

  is_inj : x:_ -> y:_ -> squash (f x == f y ==> x == y);
}

// Terrible symbol, but F* is limited in operator support.
[@@erasable]
let ( @~> ) a b = injection a b

[@@erasable]
noeq
type idesc : nat -> Type =
  | INil : idesc 0
  | ICons : #n:nat -> w:nat -> tl:(idesc n) -> idesc (n+1)

inline_for_extraction noextract
let rec abs #n (i : idesc n) : eqtype =
  match i with
  | INil -> unit
  | ICons h ts -> nat & abs ts

[@@erasable]
noeq
type mlayout (rows cols : nat) = {
  len : nat;
  map : nat & nat @~> nat;
}

[@@erasable]
noeq
type tlayout (#r : Ghost.erased nat) (d : idesc r) = {
  (* Underlying length of base array (Kuiper.Array) *)
  ulen : nat;
  (* Injection from (abstract) index space into base array. *)
  imap : abs d @~> nat;
}

let col_flayout (#rows #cols : nat) (l : mlayout rows cols) (j : nat)
  : tlayout (ICons rows INil)
  = {
      ulen = l.len;
      imap = {
        f = (fun (i, ()) -> l.map.f (i, j));
        is_inj = (fun (x, ()) (y, ()) -> l.map.is_inj (x, j) (y, j));
      };
    }
