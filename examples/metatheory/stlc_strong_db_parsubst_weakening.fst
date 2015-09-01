(*--build-config
    other-files: constr.fst classical.fst ext.fst stlc_strong_db_parsubst.fst
  --*)

module StlcWeakening

(* Weakening (or shifting preserves typing) *)
(* Useless now, showing that it follows from substitution lemma *)
val sub_inc_above : nat -> var -> Tot exp
let sub_inc_above n y = if y<n then EVar y else EVar (y+1)

val shift_up_above : nat -> exp -> Tot exp
let shift_up_above n e = subst (sub_inc_above n) e

val extend_gen : var -> typ -> env -> Tot env
let extend_gen x t g y = if y < x then g y
                         else if y = x then Some t
                         else g (y-1)

opaque val weakening : n:nat -> #g:env -> #e:exp -> #t:typ -> t':typ ->
      h:typing g e t -> Tot (typing (extend_gen n t' g) (shift_up_above n e) t)
      (decreases h)
let rec weakening n g v t t' h =
  let hs : subst_typing (sub_inc_above n) g (extend_gen n t' g) =
    fun y -> if y < n then TyVar y else TyVar (y+1)
  in substitution (sub_inc_above n) h hs
