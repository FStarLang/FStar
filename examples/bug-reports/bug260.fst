module Bug260

type pnat =
  | O : pnat
  | S : pnat -> pnat

type validity : n:pnat -> Type =
  | VSucc : n:pnat -> Tot (validity (S n))

(* val bad : t:pnat -> Tot (validity (S (S t)))           (\* wrong type: *\) *)
val bad : t:pnat -> Tot (validity (S t)) //-- right type:
let bad t = VSucc t

(* we could have probably proved false with a variant of this *)
type validity' : n:pnat -> Type =
  | VSucc' : n:pnat -> (validity' n) -> Tot (validity' (S n))

val validity'_empty : n:pnat -> validity' n -> Lemma (requires True) (ensures (False))
let rec validity'_empty n h =
  match h with
  | VSucc' n' h' -> validity'_empty n' h'

assume val bad' : t:pnat -> Tot (validity' (S (S t)))

val ff : unit -> Lemma (requires True) (ensures (False))
let ff () = validity'_empty (S (S O)) (bad' O)
