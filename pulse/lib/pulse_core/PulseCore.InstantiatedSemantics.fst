module PulseCore.InstantiatedSemantics
module Sem = PulseCore.Semantics2
module Mem = PulseCore.Memory
module U = FStar.Universe
module F = FStar.FunctionalExtensionality
open Mem

let laws ()
: squash (
    Sem.associative star /\
    Sem.commutative star /\
    Sem.is_unit emp star
  )
= let equiv_eq (x y:slprop)
    : Lemma (x `equiv` y <==> x == y)
          [SMTPat (x `equiv` y)]
    = introduce x `equiv` y ==> x == y
      with _h . slprop_extensionality x y
  in
  let _ : squash (Sem.associative star) =
    introduce 
        forall x y z. 
            ((x `star` y) `star` z) ==
            (x `star` (y `star` z))
    with star_associative x y z
  in
  let _ : squash (Sem.commutative star) = 
    introduce 
        forall x y.
            x `star` y == y `star` x
        with star_commutative x y
  in
  let _ : squash (Sem.is_unit emp star) =
    introduce
        forall x.
            (x `star` emp) == x /\
            (emp `star` x) == x
        with emp_unit x
  in
  ()

let state0 (e:inames) : Sem.state = {
    max_act = U.raise_t u#0 u#100 unit;
    s = mem;
    is_full_mem = full_mem_pred;
    pred = slprop;
    emp = emp;
    star = star;
    interp = interp;
    evolves = mem_evolves;
    invariant = locks_invariant e;
    laws = laws ()
}

let state : Sem.state = state0 Set.empty

let slprop = slprop
let _eq : squash (slprop == state.pred) = ()
let emp = emp
let pure p = pure p
let ( ** ) p q = p `star` q
let ( exists* ) #a p = h_exists (F.on_dom a p)

let prop_squash_idem (p:prop)
  : Tot (squash (p == squash p))
  = FStar.PropositionalExtensionality.apply p (squash p)

let slprop_equiv p q = Mem.equiv p q

let unsquash (p:squash (slprop_equiv 'p 'q)) : slprop_equiv 'p 'q =
    prop_squash_idem (slprop_equiv 'p 'q);
    coerce_eq () p
    
let slprop_equiv_refl p = unsquash ()
    
let slprop_equiv_elim p q =
    introduce (p `slprop_equiv` q) ==> p==q
    with _ . Mem.slprop_extensionality p q

let slprop_equiv_unit p = unsquash ()
let slprop_equiv_comm p1 p2 = unsquash ()
let slprop_equiv_assoc p1 p2 p3 = unsquash ()
module T = FStar.Tactics.V2
let slprop_equiv_exists 
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. slprop_equiv (p x) (q x)))
= introduce forall x. p x == q x
  with slprop_equiv_elim (p x) (q x);
  F.extensionality _ _ p q;
  let pf : squash (eq2 #(F.arrow a (fun _ -> slprop))
                        (F.on_dom a p)
                        (F.on_dom a q)) = ()
  in
  let x : squash (op_exists_Star p == op_exists_Star q) = _ by (
      T.norm [delta_only [`%op_exists_Star; `%F.on_dom]; unascribe];
      let bindings = T.cur_vars() in
      let bindings = List.Tot.rev bindings in
      match bindings with
      | hd::_ -> (
        match T.term_as_formula hd.sort with
        | T.Comp (T.Eq _) lhs rhs ->
          T.grewrite lhs rhs;
          T.trefl();
          T.exact (T.binding_to_term hd)
        | _ -> T.fail "Unexpected type of hd"
      )
      | _ ->
        T.fail "empty bindings"
  ) in
  unsquash x

(* The type of general-purpose computations *)
let stt (a:Type u#a) 
        (pre:slprop)
        (post:a -> slprop)
: Type0
= unit -> Dv (Sem.m u#2 u#100 u#a #state a pre post)

let return (#a:Type u#a) (x:a) (p:a -> slprop)
: stt a (p x) p
= fun _ -> Sem.ret x p

let bind
    (#a:Type u#a) (#b:Type u#b)
    (#pre1:slprop) (#post1:a -> slprop) (#post2:b -> slprop)
    (e1:stt a pre1 post1)
    (e2:(x:a -> stt b (post1 x) post2))
: stt b pre1 post2
= fun _ -> Sem.mbind (e1()) (fun x -> e2 x ())

let frame
  (#a:Type u#a)
  (#pre:slprop) (#post:a -> slprop)
  (frame:slprop)
  (e:stt a pre post)
: stt a (pre `star` frame) (fun x -> post x `star` frame)
= fun _ -> Sem.frame frame (e())

