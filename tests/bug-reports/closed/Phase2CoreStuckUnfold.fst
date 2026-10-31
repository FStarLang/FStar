module Phase2CoreStuckUnfold

(* Unfolding a recursive head to a stuck match is only useful against another match;
   unfolding it otherwise could diverge, relating ever-growing branch instances. *)
noeq type bs : nat -> Type =
  | Stop : bs 0
  | Field : sz:nat -> rest:bs sz -> bs (sz + 1)
  | Sum : key:eqtype -> n:nat -> payload:(key -> bs n) -> bs (n + 1)

let rec ty' (#n:nat) (b:bs n) : Tot Type (decreases n) =
  match b with
  | Stop -> unit
  | Field _ rest -> (nat & ty' rest)
  | Sum key _ payload -> (k:key & ty' (payload k))

let ty (#n:nat) (b:bs n) : Type = ty' b

let ty_sum (key:eqtype) (n:nat) (payload:key -> bs n) : Type = (k:key & ty (payload k))

let elim (key:eqtype) (n:nat) (payload:key -> bs n) (x:ty (Sum key n payload)) : ty_sum key n payload = x
