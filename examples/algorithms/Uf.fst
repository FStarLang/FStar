module Uf

open FStar.Heap
open FStar.List.Tot
open FStar.Squash
open FStar.Classical
open FStar.Ghost
open FStar.ST
open FStar.TSet
open FStar.FunctionalExtensionality
open FStar.MarkovsPrinciple


(** TODO : Prove that forall u1 u2 : ufh a h. u1.parent = u2.parent ==> u1 = u2  using reification *)

type uf (a : Type) : Type = { content:a ; parent:ref (option (uf a)) }


let rec p (a:Type) (h:heap) (u: uf a) (n:nat) : GTot bool (decreases n) =
    match sel h u.parent with
        | None -> true
        | Some v -> if n = 0 then false else p a h v (n-1)

noeq type funcaccessible (#a:Type0) (f: a -> GTot (option a)) (u : a) : Type0 =
| FAcc : next:(match f u with | Some v -> funcaccessible f v | None -> unit) -> funcaccessible f u

let ufh a h = x:(uf a){Heap.contains h x.parent}

let reach (a:eqtype) h (u : uf a) : GTot (option (uf a)) = sel h u.parent

let not_intro (#p:Type) ($f: p -> Lemma False) : Lemma (~p) = impl_intro f

let markov_from_funcaccessible (#a:eqtype) (h:heap) (u: uf a) (w:funcaccessible (reach a h) u)
  : GTot (squash (~(forall n. ~(p a h u n)))) =
  let rec witness (v:uf a) (w:funcaccessible (reach a h) v) : GTot (n:nat{p a h v n}) (decreases w)=
    match sel h v.parent with | None -> 0 | Some v -> witness v w.next + 1
  in
  let n0 = witness u w in
  let aux0 (f : forall n. ~(p a h u n)) : Lemma False = give_witness f ; assert (~(p a h u n0)) ; assert (False) in
  not_intro aux0 ; get_proof (~(forall n. ~(p a h u n)))

let reprfun (a:eqtype) (h:heap) = f:(uf a -> GTot (uf a)){
  (forall u. if Heap.contains h u.parent then Heap.contains h (f u).parent else u = f u) /\
  (forall (u:ufh a h). sel h (f u).parent = None /\ (sel h u.parent = None ==> f u = u)) /\
  (forall (u:ufh a h) (v:ufh a h). sel h u.parent = Some v ==> f u = f v)
}

let funcaccessible_from_markov (#a:eqtype) (h:heap) (u:uf a)
: Ghost (funcaccessible (reach a h) u)
        (requires (~(forall n. ~(p a h u n))))
        (ensures (fun _ -> True)) =
  let n0 = stronger_markovs_principle (p a h u) in
  let rec build_witness (n:nat) (v:uf a) : Ghost (funcaccessible (reach a h) v) (requires (p a h v n)) (ensures (fun _ -> True)) =
    match sel h v.parent with
    | None -> FAcc ()
    | Some v' -> FAcc (build_witness (n-1) v')
  in build_witness n0 u


(** An strenghening of recall : any reference reachable through
    some heap h from some reference contained in h is also in h **)
(* TODO : prove it using Danel's monotonic predicates *)
assume val recall_reachable : #a:Type -> #a2:Type -> #b:Type -> h:heap -> r:ref a -> f:(a2 -> Tot (ref b)) ->
  Lemma (requires (has_type (sel h r) a2 /\ f (sel h r) << sel h r))
        (ensures (has_type (sel h r) a2 /\ Heap.contains h (f (sel h r))))

let recall_step (#a:eqtype) (h:heap) (z:uf a) (y:uf a)
  : Lemma (requires (reach a h z = Some y))
          (ensures (Heap.contains h y.parent)) =
  recall_reachable h z.parent (fun (r : (option (uf a)){Some? r}) -> match r with | Some y -> y.parent)

//assume val recall_step : #a:eqtype -> h:heap -> z:uf a -> y:uf a -> Lemma (requires (reach a h z = Some y)) (ensures (Heap.contains h y.parent))

let uf_invariant (a:eqtype) (h:heap) : Type0 = (forall (u0:ufh a h). funcaccessible (reach a h) u0)
let uf_invariant_fun (#a:eqtype) (h:heap) : Tot Type0 = (u0:ufh a h) -> GTot (funcaccessible (reach a h) u0)

let maintain_uf_invariant (#a:eqtype) (#h0:heap) (#h1:heap) ($f : uf_invariant_fun h0 -> GTot (uf_invariant_fun h1)) : Lemma (requires (uf_invariant a h0)) (ensures (uf_invariant a h1)) =
  give_proof #(uf_invariant a h1) (map_squash (get_proof (uf_invariant a h0)) (fun (sq_uf_inv0 : squash (uf_invariant_fun h0)) -> map_squash sq_uf_inv0 f))


let uf_invariant_termination (a:eqtype) (h:heap) (u:ufh a h)
  : Ghost (funcaccessible (reach a h) u)
          (requires (uf_invariant a h))
          (ensures (fun _ -> True))
  = give_proof (bind_squash (get_proof (funcaccessible (reach a h) u))
                           (markov_from_funcaccessible h u) ) ;
    assert (~(forall n. ~(p a h u n)));
    funcaccessible_from_markov h u


//assume val uf_invariant_termination : (a:eqtype) -> (h:heap) -> (u:ufh a h) -> (p:ufh a h) -> Lemma (requires (uf_invariant a h /\ sel h u.parent = Some p)) (ensures (p << u))


let reprfun_prop (#a:eqtype) (h:heap) (f1:reprfun a h) (f2:reprfun a h) : Lemma (requires (uf_invariant a h)) (ensures (f1 == f2)) =
  let rec equality_proof (u:ufh a h) (w : funcaccessible (reach a h) u): Lemma (requires True) (ensures (f1 u == f2 u)) (decreases w) =
    match sel h u.parent with
    | None -> ()
    | Some v -> recall_step h u v ; equality_proof v w.next
  in
  let aux (u:ufh a h) : Lemma (ensures (f1 u == f2 u)) = let w = uf_invariant_termination a h u in equality_proof u w in
  forall_intro aux ; assert (gfeq f1 f2)


let retrieve_reprfun (a:eqtype) (h:heap) : Pure (reprfun a h) (requires (uf_invariant a h)) (ensures (fun _ -> True)) =
  let rec f0 (u:ufh a h) (w:funcaccessible (reach a h) u)
    : Ghost (uf a)
            (requires True)
            (ensures (fun r -> Heap.contains h r.parent /\ sel h r.parent = None /\ (sel h u.parent = None ==> u = r)))
            (decreases w)
    = match reach a h u with | None -> u | Some v -> recall_step h u v ; f0 v w.next
  in
  let f (u:uf a)
    : Ghost (uf a)
      (requires True)
      (ensures (fun r -> if Heap.contains h u.parent
                      then Heap.contains h r.parent /\ sel h r.parent = None /\ (sel h u.parent = None ==> u = r)
                      else u = r))
    = if Heap.contains h u.parent
      then let w = uf_invariant_termination a h u in f0 u w
      else u
  in
  let reprfun_prop (u:ufh a h) (v:ufh a h) : Lemma (requires (reach a h u = Some v)) (ensures (f u == f v)) = admit () (* replace when bug#739 is fixed*)
    (*match reach a h v with
    | None -> ()
    | Some w -> recall_step h v w ; reprfun_prop v w *)
  in (*TODO : investigate why it does not go through *)
  let reprfun_prop' (u:ufh a h) : Lemma (forall (v:ufh a h). sel h u.parent = Some v ==> f u = f v) = forall_intro (move_requires (reprfun_prop u)) in
  forall_intro reprfun_prop' ;
  //assert (forall (u:ufh a h) (v:ufh a h). sel h u.parent = Some v ==> f u = f v) ;
  f


let same_reprfun (a:eqtype) (h0:heap) (h1:heap) : Pure Type0 (requires (uf_invariant a h0 /\ uf_invariant a h1)) (ensures (fun _ -> True)) =
  let f0 = retrieve_reprfun a h0 in let f1 = retrieve_reprfun a h1 in f1 == f0

let merge_reprfun (a:eqtype) (h0:heap) (h1:heap) (x:uf a) (y:uf a) (z:uf a)
  : Pure Type0
         (requires (uf_invariant a h0 /\
                    uf_invariant a h1))
         (ensures (fun _ -> True)) =
  let f0 = retrieve_reprfun a h0 in
  let f1 = retrieve_reprfun a h1 in
  let rx = f0 x in let ry = f0 y in
  if rx.parent = ry.parent then same_reprfun a h0 h1
  else f1 == (fun w -> if f0 w = rx || f0 w = ry then z else f0 w)

(*************************************************************************************)
(**                 Implementation of the union-find interface                      **)
(*************************************************************************************)

(* Without invariants :
   let make_uf (#a:eqtype) (x:a) : St (uf a) =
     { content = x ; parent = alloc None }
*)

let make_uf (#a:eqtype) (x:a)
  : ST (uf a)
      (requires (uf_invariant a))
      (ensures (fun h0 x h1 -> modifies_none h0 h1 /\
                            uf_invariant a h1 /\
                            uf_invariant a h0 /\
                            same_reprfun a h0 h1)) =
  let h0 = get () in
  let res : uf a = { content = x ; parent = alloc None } in
  let h1 = get () in
  let uf_inv1 (uf_inv0:uf_invariant_fun h0) (u: ufh a h1) : GTot (funcaccessible (reach a h1) u) =
    let rec pushforward_accessible (u:ufh a h1) (acc0 : funcaccessible (reach a h0) u) : GTot (funcaccessible (reach a h1) u) (decreases acc0) =
      match reach a h1 u with | None -> FAcc () | Some v -> recall_step h1 u v ; FAcc (pushforward_accessible v acc0.next)
    in if u.parent = res.parent then FAcc () else let u : uf a = u in pushforward_accessible u (uf_inv0 u)
  in maintain_uf_invariant uf_inv1 ;
  res


(* Without invariants :

  let rec root (u:uf a) : St (uf a) =
    match !u.parent with
    | none -> u
    | some p ->
      let r = root p in
      u.parent := r
      r
*)

let distinct_cell_lemma (#a:eqtype) (h:heap) (r1:ref a) (r2: ref a) : Lemma (sel h r1 <> sel h r2 ==> r1 <> r2) = ()

(** TODO : why do I need to ask for uf_invariant a h0 in the post-condition ??? *)
let rec root0 (#a:eqtype) (h0:heap) (u:uf a) (w: erased (funcaccessible (reach a h0) u))
  : ST (uf a)
       (requires (fun h -> uf_invariant a h /\ h == h0))
       (ensures (fun h0 r h1 -> uf_invariant a h0 /\
                             uf_invariant a h1 /\
                             same_reprfun a h0 h1 /\
                             retrieve_reprfun a h1 u = r) )
       (decreases (reveal w)) (* WARNING : check the decrease clause by hand for now *) =
  match !u.parent with
  | None -> u
  | Some p ->
    let h0 = get () in
    recall u.parent ;
    recall p.parent ;
    let w_next : erased (funcaccessible (reach a h0) p) =
      (* TODO : investigate why elift1 (fun w -> w.next) w fails *)
      let next (w0:funcaccessible (reach a h0) u) : Tot (funcaccessible (reach a h0) p) =
        w0.next
      in
      elift1 next w
    in
    assert ( reveal w_next << reveal w ) ;
    let r = root0 h0 p w_next in
    let h1 = get () in
    distinct_cell_lemma h0 r.parent u.parent ;
    recall u.parent ;
    u.parent := Some r ;
    let h2 = get () in
    let uf_inv2 (uf_inv1: uf_invariant_fun h1) (u1:ufh a h2) : GTot (funcaccessible (reach a h2) u1) =
      let rec pushforward (u0:ufh a h1) (w : funcaccessible (reach a h1) u0)
        : GTot (funcaccessible (reach a h2) u0) (decreases w) =
        if u0.parent = u.parent
        then FAcc (FAcc () <: funcaccessible (reach a h2) r)
        else match reach a h2 u0 with | None -> FAcc () | Some v -> recall_step h1 u0 v ; FAcc (pushforward v w.next)
      in let u1 : uf a = u1 in pushforward u1 (uf_inv1 u1)
    in maintain_uf_invariant uf_inv2 ;
    r


let root (#a:eqtype) (u:uf a)
  : ST (uf a)
       (requires (uf_invariant a))
       (ensures (fun h0 r h1 -> uf_invariant a h0 /\
                             uf_invariant a h1 /\
                             same_reprfun a h0 h1 /\
                             retrieve_reprfun a h1 u = r))
  = let h0 = get () in
    recall u.parent ;
    let v : ufh a h0 = u in
    let reified_proof = get_proof (uf_invariant a h0) in
    let w : erased (funcaccessible (reach a h0) v) =
      let intermezzo _ : GTot (funcaccessible (reach a h0) v) =
          give_proof reified_proof ;
          uf_invariant_termination a h0 v
      in
      elift1 intermezzo (hide ())
    in
    root0 h0 v w

(* Without invariants :

   let rec uf_equiv (#a:eqtype) (u1:uf a) (u2:uf a) : St bool = root u1 = root u2

*)

let rec uf_equiv (#a:eqtype) (u1:uf a) (u2:uf a)
  : ST bool
      (requires (uf_invariant a))
      (ensures (fun h0 b h1 -> uf_invariant a h0 /\
                            uf_invariant a h1 /\
                            same_reprfun a h0 h1 /\
                            (let f = retrieve_reprfun a h0 in b = (f u1 = f u2))))
  = root u1 = root u2


 (* Without invariants :

    let rec uf_merge (#a:eqtype) (u1:uf a) (u2:uf a) : St unit =
    let r1 = root u1 in
    let r2 = root u2 in
    if r1 = r2 then () else r1.parent := Some r2

 *)

let rec uf_merge (#a:eqtype) (u1:uf a) (u2:uf a)
  : ST (uf a)
      (requires (uf_invariant a))
      (ensures (fun h0 r h1 -> uf_invariant a h0 /\
                            uf_invariant a h1 /\
                            merge_reprfun a h0 h1 u1 u2 r)) =
  let r1 = root u1 in
  let r2 = root u2 in
  if r1.parent = r2.parent then r1
  else
    let h0 = get () in
    recall r1.parent ;
    (* needed to prove that sel h1 r2.parent = None *)
    recall r2.parent ;
    r1.parent := Some r2 ;
    let h1 = get () in

    let uf_inv1 (uf_inv0:uf_invariant_fun h0) (u:ufh a h1) : GTot (funcaccessible (reach a h1) u) =
      let rec pushforward (u:ufh a h1) (acc0 : funcaccessible (reach a h0) u)
        : GTot (funcaccessible (reach a h1) u) (decreases acc0) =
        if u.parent = r1.parent
        then FAcc (FAcc () <: funcaccessible (reach a h1) r2)
        else match reach a h1 u with | None -> FAcc () | Some v -> recall_step h1 u v ; FAcc (pushforward v acc0.next)
      in let u : uf a = u in pushforward u (uf_inv0 u)
    in maintain_uf_invariant uf_inv1 ;
    r2


