module Phase2CoreRecUnfold

(* Relating a recursive type function applied to a constructor term [abs (rows @| cols @| INil)]
   to the tuple it computes must unfold the recursive head even where no guard is allowed. *)
type natlt (n:nat) = i:nat{i < n}
type shape : nat -> Type =
  | INil : shape 0
  | ICons : #n:nat -> w:nat -> tl:(shape n) -> shape (n+1)
unfold let ( @| ) (#n:nat) = ICons #n
let rec abs #n (i : shape n) : eqtype =
  match i with
  | INil -> unit
  | ICons h ts -> natlt h & abs ts

assume val f : #rows:nat -> #cols:nat -> abs (rows @| cols @| INil) -> nat

#push-options "--fuel 2 --ifuel 2"
let test (#rows #cols : nat) (rc : natlt rows & (natlt cols & unit))
  : Lemma (f rc == f rc)
  = ()
