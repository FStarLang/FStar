module UnifyInterpreted

(* We had a unification bug here. This should succeed without any
 * need for SMT simply by unfolding `id` into its definition, but
 * that was not happening since `non_neg_inv` had a Delta_equational
 * qualifier, and the unifier was sending the constraint to the SMT
 * solver since it considered the symbol as "interpreted".
 *)
let id (x:'a) : 'a = x

assume val memory : Type

let non_neg_inv (r:int) : memory -> Type0 =
  (fun m -> exists v. r == v)

assume val lock : int -> (memory -> Type0) -> Type
assume val r : int
assume val f : lock r (non_neg_inv r) -> unit
assume val l : lock r (fun m -> id (non_neg_inv r m))

#set-options "--no_smt"

(* Requires proving that (non_neg_inv r) == (fun m -> id (non_neg_inv r m)) *)
let test () : Tot unit = f l
