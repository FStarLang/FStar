module Bug576

type exp =
  | EVar   : exp
  | ELam   : exp -> exp

val appears_free_in : e:exp -> Tot bool
let rec appears_free_in e =
  match e with
  | EVar -> true
  | ELam e1 -> appears_free_in e1

let closed (e : exp) : Tot bool = not (appears_free_in e)

(* This variant makes things work
let closed (e : exp) : Tot bool = not (EVar? e) *)

val subst_closed : e:exp -> Lemma (requires (closed e)) (ensures (True))
let rec subst_closed e =
  match e with
  | ELam e1 -> ()
  (* | EVar -> () *)
