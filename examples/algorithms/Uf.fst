module Uf

open FStar.Heap
open FStar.List.Tot
open FStar.Squash
open FStar.Classical
open FStar.Ghost
open FStar.ST
open FStar.TSet
open FStar.FunctionalExtensionality


(** TODO : Prove that forall u1 u2 : ufh a h. u1.parent = u2.parent ==> u1 = u2  using reification *)

type uf (a : Type) : Type = { content:a ; parent:ref (option (uf a)) }



noeq type funcaccessible (#a:Type0) (f: a -> GTot (option a)) (u : a) : Type0 =
| FAcc : next:(match f u with | Some v -> funcaccessible f v | None -> unit) -> funcaccessible f u


let ufh a h = x:(uf a){Heap.contains h x.parent}

let reach (a:eqtype) h (u : uf a) : GTot (option (uf a)) = sel h u.parent


assume val recall_reachable : #a:Type -> #a2:Type -> #b:Type -> h:heap -> r:ref a -> f:(a2 -> Tot (ref b)) ->
Lemma (requires (has_type (sel h r) a2 /\ f (sel h r) << sel h r)) (ensures (has_type (sel h r) a2 /\ Heap.contains h (f (sel h r))))


let recall_step (#a:eqtype) (h:heap) (z:uf a) (y:uf a)
  : Lemma (requires (reach a h z = Some y)) (ensures (Heap.contains h y.parent)) =
  recall_reachable h z.parent (fun (r : (option (uf a)){is_Some r}) -> match r with | Some y -> y.parent)


assume val recall_step : #a:eqtype -> h:heap -> z:uf a -> y:uf a -> Lemma (requires (reach a h z = Some y)) (ensures (Heap.contains h y.parent))


let reprfun (a:eqtype) (h:heap) = f:(uf a -> GTot (uf a)){
  (forall u. if Heap.contains h u.parent then Heap.contains h (f u).parent else u = f u) /\
  (forall (u:ufh a h). sel h (f u).parent = None /\ (sel h u.parent = None ==> f u = u)) /\
  (forall (u:ufh a h) (v:ufh a h). sel h u.parent = Some v ==> f u = f v)
}



let uf_invariant (a:eqtype) (h:heap) : Type0 = (forall (u0:ufh a h). funcaccessible (reach a h) u0)
let uf_invariant_fun (#a:eqtype) (h:heap) : Tot Type0 = (u0:ufh a h) -> GTot (funcaccessible (reach a h) u0)

let maintain_uf_invariant (#a:eqtype) (#h0:heap) (#h1:heap) ($f : uf_invariant_fun h0 -> GTot (uf_invariant_fun h1)) : Lemma (requires (uf_invariant a h0)) (ensures (uf_invariant a h1)) =
  give_proof #(uf_invariant a h1) (map_squash (get_proof (uf_invariant a h0)) (fun (sq_uf_inv0 : squash (uf_invariant_fun h0)) -> map_squash sq_uf_inv0 f))

assume val uf_invariant_termination : (a:eqtype) -> (h:heap) -> (u:ufh a h) -> (p:ufh a h) -> Lemma (requires (uf_invariant a h /\ sel h u.parent = Some p)) (ensures (p << u))


(** Ghost functional extensionality **)
type gfun (a:Type) (b:Type) = a -> GTot b

type gfeq (#a:Type) (#b:Type) (f:gfun a b) (g:gfun a b) =
    (forall x.{:pattern (f x) \/ (g x)} f x == g x)

assume GhostExtensionality : forall (a:Type) (b:Type) (f: gfun a b) (g: gfun a b).
                        {:pattern gfeq #a #b f g} gfeq #a #b f g <==> f==g


let reprfun_prop (#a:eqtype) (h:heap) (f1:reprfun a h) (f2:reprfun a h) : Lemma (requires (uf_invariant a h)) (ensures (f1 == f2)) =
  let w = get_proof (uf_invariant a h) in (* TODO : check that not having this proposition in the closire of equality_proof is normal *)
  let rec equality_proof (u:ufh a h) : Lemma (requires True) (ensures (f1 u == f2 u)) (decreases u) =
    match sel h u.parent with
    | None -> ()
    | Some v -> recall_step h u v ; give_proof w ; uf_invariant_termination a h u v ; equality_proof v
  in
  forall_intro equality_proof ; assert (gfeq f1 f2)


let retrieve_reprfun (a:eqtype) (h:heap) : Pure (reprfun a h) (requires (uf_invariant a h)) (ensures (fun _ -> True)) =
  let w = get_proof (uf_invariant a h) in
  let rec f (u:uf a) : Ghost (uf a) (requires True) (ensures (fun r -> if Heap.contains h u.parent then Heap.contains h r.parent /\ sel h r.parent = None /\ (sel h u.parent = None ==> u = r) else u = r)) =
    if Heap.contains h u.parent then
      match reach a h u with | None -> u | Some v -> recall_step h u v ; give_proof w ; uf_invariant_termination a h u v ; f v
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

let merge_reprfun (a:eqtype) (h0:heap) (h1:heap) (x:uf a) (y:uf a) (z:uf a) : Pure Type0 (requires (uf_invariant a h0 /\ uf_invariant a h1)) (ensures (fun _ -> True)) =
  let f0 = retrieve_reprfun a h0 in
  let f1 = retrieve_reprfun a h1 in
  let rx = f0 x in let ry = f0 y in
  if rx.parent = ry.parent then same_reprfun a h0 h1
  else f1 == (fun w -> if f0 w = rx || f0 w = ry then z else f0 w)


(* Without invariants :
   let make_uf (#a:eqtype) (x:a) : St (uf a) =
     { content = x ; parent = alloc None }
*)


let make_uf (#a:eqtype) (x:a) : ST (uf a) (requires (uf_invariant a)) (ensures (fun h0 x h1 -> modifies_none h0 h1 /\ uf_invariant a h1 /\ uf_invariant a h0 /\ same_reprfun a h0 h1)) =
  let h0 = get () in
  let res : uf a = { content = x ; parent = alloc None } in
  let h1 = get () in
  let uf_inv1 (uf_inv0:uf_invariant_fun h0) (u: ufh a h1) : GTot (funcaccessible (reach a h1) u) =
    let rec pushforward_accessible (u:ufh a h1) (acc0 : funcaccessible (reach a h0) u) : GTot (funcaccessible (reach a h1) u) (decreases acc0) =
      match reach a h1 u with | None -> FAcc () | Some v -> recall_step h1 u v ; FAcc (pushforward_accessible v acc0.next)
    in if u.parent = res.parent then FAcc () else let u : uf a = u in pushforward_accessible u (uf_inv0 u)
  in maintain_uf_invariant uf_inv1 ;
  res



let distinct_cell_lemma (#a:eqtype) (h:heap) (r1:ref a) (r2: ref a) : Lemma (sel h r1 <> sel h r2 ==> r1 <> r2) = ()


(* Without invariants :

  let rec root (u:uf a) : St (uf a) =
    match !u.parent with
    | none -> u
    | some p ->
      let r = root p in
      u.parent := r
      r
*)

(** TODO : why do I need to ask for uf_invariant a h0 in the post-condition ??? *)
let rec root (#a:eqtype) (u:uf a) : ST (uf a) (requires (uf_invariant a)) (ensures (fun h0 r h1 -> uf_invariant a h0 /\ uf_invariant a h1 /\ same_reprfun a h0 h1 /\ (*sel h0 r.parent = None /\ sel h1 r.parent = None*) retrieve_reprfun a h1 u = r) ) (decreases u) (* WARNING : check the decrease clause by hand for now *) =
  match !u.parent with
  | None -> u
  | Some p ->
    let h0 = get () in
    recall u.parent ;
    recall p.parent ;
    uf_invariant_termination a h0 u p ;
    assert ( p << u ) ;
    let r = root p in
    let h1 = get () in
//   assert (sel h0 u.parent = Some p) ;
    distinct_cell_lemma h0 r.parent u.parent ;
//    assert (r.parent <> u.parent) ;
    recall u.parent ;
    u.parent := Some r ;
    let h2 = get () in
//    assert (forall (u0 : ufh a h2). Heap.contains h1 u0.parent);
//    assert (forall (u0 : ufh a h2). u0.parent <> u.parent ==> reach a h2 u0 = reach a h1 u0);
    let uf_inv2 (uf_inv1: uf_invariant_fun h1) (u1:ufh a h2) : GTot (funcaccessible (reach a h2) u1) =
      let rec pushforward (u0:ufh a h1) (w : funcaccessible (reach a h1) u0) : GTot (funcaccessible (reach a h2) u0) (decreases w) =
        if u0.parent = u.parent
        then begin match reach a h2 u0 with
          | Some r0 -> let wr0 : funcaccessible (reach a h2) r0 = match reach a h2 r0 with | None -> FAcc () in FAcc wr0
          end(* TODO : Something's wrong here FAcc (FAcc ()) should be enough  *)
        else match reach a h2 u0 with | None -> FAcc () | Some v -> recall_step h1 u0 v ; FAcc (pushforward v w.next)
      in let u1 : uf a = u1 in pushforward u1 (uf_inv1 u1)
    in maintain_uf_invariant uf_inv2 ;
//   if p = r then give_witness #(reachable h0 r u) (Immediately u) else give_proof (map_squash (get_proof (reachable h0 r p)) (fun w -> Later p w u)) ;
    r


(* Without invariants :

   let rec uf_equiv (#a:eqtype) (u1:uf a) (u2:uf a) : St bool = root u1 = root u2

*)



let rec uf_equiv (#a:eqtype) (u1:uf a) (u2:uf a) : ST bool (requires (uf_invariant a)) (ensures (fun h0 b h1 -> uf_invariant a h0 /\ uf_invariant a h1 /\ same_reprfun a h0 h1 /\ (let f = retrieve_reprfun a h0 in b = (f u1 = f u2)))) =
  let h0 = get () in
  let r1 = root u1 in
  let h1 = get () in
  let r2 = root u2 in
  let h2 = get () in
  r1 = r2


 (* Without invariants :

    let rec uf_merge (#a:eqtype) (u1:uf a) (u2:uf a) : St unit =
    let r1 = root u1 in
    let r2 = root u2 in
    if r1 = r2 then () else r1.parent := Some r2

 *)



 let rec uf_merge (#a:eqtype) (u1:uf a) (u2:uf a) : ST (uf a) (requires (uf_invariant a)) (ensures (fun h0 r h1 -> uf_invariant a h0 /\ uf_invariant a h1 /\ merge_reprfun a h0 h1 u1 u2 r)) =
  let r1 = root u1 in
  let r2 = root u2 in
  if r1.parent = r2.parent then r1
  else
    let h0 = get () in
    recall r1.parent ;
    recall r2.parent ; // needed to prove that sel h1 r2.parent = None
    r1.parent := Some r2 ;
    let h1 = get () in

    let uf_inv1 (uf_inv0:uf_invariant_fun h0) (u:ufh a h1) : GTot (funcaccessible (reach a h1) u) =
      let rec pushforward (u:ufh a h1) (acc0 : funcaccessible (reach a h0) u) : GTot (funcaccessible (reach a h1) u) (decreases acc0) =
        if u.parent = r1.parent
        then begin match reach a h1 u with
                | Some r0 -> let wr0 : funcaccessible (reach a h1) r0 = match reach a h1 r0 with | None -> FAcc () in FAcc wr0
          end(* TODO : Something's wrong here FAcc (FAcc ()) should be enough  *)
        else match reach a h1 u with | None -> FAcc () | Some v -> recall_step h1 u v ; FAcc (pushforward v acc0.next)
      in let u : uf a = u in pushforward u (uf_inv0 u)
    in maintain_uf_invariant uf_inv1 ;
    r2


