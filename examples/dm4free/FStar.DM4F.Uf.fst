module FStar.DM4F.Uf

open FStar.DM4F.Heap
open FStar.List.Tot
open FStar.Squash
open FStar.Classical
open FStar.Ghost
open FStar.DM4F.Heap.ST
open FStar.Set
open FStar.FunctionalExtensionality


(** TODO : Prove that forall u1 u2 : ufh a h. u1.parent = u2.parent ==> u1 = u2  using reification *)

type uf (a : Type) : Type = { content:a ; parent:ref (option (uf a)) }


noeq type funcaccessible (#a:Type0) (f: a -> GTot (option a)) (u : a) : Type0 =
| FAcc : next:(match f u with | Some v -> funcaccessible f v | None -> unit) -> funcaccessible f u


let ufh a h = x:(uf a){h `contains_a_well_typed` x.parent}

assume val recall_step : #a:eqtype -> h:heap -> z:ufh a h -> y:uf a -> Lemma (requires (sel h z.parent = Some y)) (ensures (h `contains_a_well_typed` y.parent))

let reach (a:eqtype) h (u : ufh a h) : GTot (option (ufh a h)) =
  match sel h u.parent with
  | None -> None
  | Some v -> recall_step h u v ; Some v



let reprfun (a:eqtype) (h:heap) = f:(uf a -> GTot (uf a)){
  (forall u. (h `contains_a_well_typed` u.parent ==> h `contains_a_well_typed` (f u).parent) /\ (~(h `contains_a_well_typed` u.parent) ==> u = f u)) /\
  (forall (u:ufh a h). sel h (f u).parent = None /\(sel h u.parent = None ==> f u = u)) /\
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
  let rec f (u:uf a) : Ghost (uf a) (requires True)
                       (ensures (fun r ->
                       (h `contains_a_well_typed` u.parent ==> h `contains_a_well_typed` r.parent /\
                                                               sel h r.parent = None /\
                                                               (sel h u.parent = None ==> u = r))
                       /\ (~(h `contains_a_well_typed` u.parent) ==> u = r))) =
    if excluded_middle (h `contains_a_well_typed` u.parent) then
      match reach a h u with
      | None -> u
      | Some v ->
        recall_step h u v ;
        give_proof w ;
        uf_invariant_termination a h u v ;
        f v
    else u
  in
  let reprfun_prop (u:ufh a h) (v:ufh a h) : Lemma (requires (reach a h u = Some v)) (ensures (f u = f v)) = admit () (* replace when bug#739 is fixed*)
    (*match reach a h v with
    | None -> ()
    | Some w -> recall_step h v w ; reprfun_prop v w *)
  in (*TODO : investigate why it does not go through *)
  let reprfun_prop' (u:ufh a h) : Lemma (forall (v:ufh a h). sel h u.parent = Some v ==> f u = f v) = forall_intro (move_requires (reprfun_prop u)) in
  forall_intro reprfun_prop' ;
  //assert (forall (u:ufh a h) (v:ufh a h). sel h u.parent = Some v ==> f u = f v) ;

  assert (forall u. (h `contains_a_well_typed` u.parent ==> h `contains_a_well_typed` (f u).parent));
  assert (forall u. (~(h `contains_a_well_typed` u.parent) ==> u = f u)) ;
  assert (forall (u:ufh a h). sel h (f u).parent = None /\(sel h u.parent = None ==> f u = u)) ;
  assert (forall (u:ufh a h) (v:ufh a h). sel h u.parent = Some v ==> f u = f v) ;

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


let make_uf (#a:eqtype) (x:a) : ST (uf a) (requires (uf_invariant a)) (ensures (fun h0 x h1 -> uf_invariant a h1 /\ uf_invariant a h0 /\ same_reprfun a h0 h1)) =
  let h0 : heap = STATE.get () in
  let res : uf a = { content = x ; parent = alloc None } in
  let h1 = STATE.get () in
  let uf_inv1 (uf_inv0:uf_invariant_fun h0) (u: ufh a h1) : GTot (funcaccessible (reach a h1) u) =
    let rec pushforward_accessible (u:(uf a){h0 `contains_a_well_typed` u.parent /\ h1 `contains_a_well_typed` u.parent}) (acc0 : funcaccessible (reach a h0) u) : GTot (funcaccessible (reach a h1) u) (decreases acc0) =
      match reach a h1 u with | None -> FAcc () | Some v -> recall_step h1 u v ; FAcc (pushforward_accessible v acc0.next)
    in if u.parent = res.parent then FAcc () else let u : uf a = u in assert (h0 `contains_a_well_typed` u.parent) ; pushforward_accessible u (uf_inv0 u)
  in maintain_uf_invariant uf_inv1 ;
  res



let distinct_cell_lemma (#a:eqtype) (h:heap) (r1:(ref a){h `contains_a_well_typed` r1}) (r2: (ref a){h `contains_a_well_typed` r2}) : Lemma (sel h r1 <> sel h r2 ==> r1 <> r2) = ()


(* Without invariants :

  et rec root (u:uf a) : St (uf a) =
    match !u.parent with
    | none -> u
    | some p ->
      let r = root p in
      u.parent := r
      r
*)
let build_uf_inv2 (#a:eqtype) (h1:heap) (h2:heap) (u:uf a) (r:uf a)  : Pure ((uf_inv1 : uf_invariant_fun h1) -> uf_invariant_fun h2)
                                                                          (requires (modifies (Set.singleton u.parent) h1 h2 /\
                                                                            h1 `contains_a_well_typed` u.parent /\
                                                                            h1 `contains_a_well_typed` r.parent /\
                                                                            h2 `contains_a_well_typed` u.parent /\
                                                                            h2 `contains_a_well_typed` r.parent /\
                                                                            (exists r'. sel h2 u.parent = Some r' /\ r' === r) /\
                                                                            sel h2 r.parent = None /\
                                                                            (forall (r:ref (uf a)). h2 `contains_a_well_typed` r ==> h1 `contains_a_well_typed` r)))
                                                                           (ensures (fun _ -> True)) =
  assert (forall (u:uf a). h1 `contains_a_well_typed` u.parent ==> h2 `contains_a_well_typed` u.parent) ;
  let bidule (u:ufh a h1) : Tot (ufh a h2) = let u : uf a = u in u in
  let cobidule (u:ufh a h2) : Tot (ufh a h1) = let u : uf a = u in u in
  assert (u === bidule u) ;
  assert (u === cobidule u) ;
  let r' : ufh a h2 = r in
  let rec pushforward (u0:ufh a h1) (w : funcaccessible (reach a h1) u0) : GTot (funcaccessible (reach a h2) (bidule u0)) (decreases w) =
    if u0.parent = u.parent
    then FAcc (FAcc () <: funcaccessible (reach a h2) r')
    else match reach a h2 (bidule u0) with | None -> FAcc () | Some v -> assert (sel h1 u0.parent = Some v) ; recall_step h1 u0 v ; FAcc (pushforward v w.next)
  in
  let uf_inv2 (uf_inv1 : uf_invariant_fun h1) (u1:ufh a h2) : GTot (funcaccessible (reach a h2) u1) = pushforward (cobidule u1) (uf_inv1 (cobidule u1)) in
  uf_inv2


(** TODO : why do I need to ask for uf_invariant a h0 in the post-condition ??? *)
let rec root (#a:eqtype) (u:uf a) : ST (uf a)
             (requires (fun h0 -> uf_invariant a h0 /\
                               h0 `contains_a_well_typed` u.parent))
             (ensures (fun h0 r h1 -> uf_invariant a h0 /\
                                   uf_invariant a h1 /\
                                   (forall (r : ref (uf a)). h0 `contains_a_well_typed` r ==> h1 `contains_a_well_typed` r) /\
                                   same_reprfun a h0 h1 /\
                                   retrieve_reprfun a h1 u = r) ) (decreases u) (* WARNING : check the decrease clause by hand for now *) =
  match !u.parent with
  | None -> u
  | Some p ->
    let h0 : heap = STATE.get () in
    recall_step h0 u p ;
    uf_invariant_termination a h0 u p ;
    assert ( p << u ) ;
    let r = root p in
    let h1 = STATE.get () in
//   assert (sel h0 u.parent = Some p) ;
    distinct_cell_lemma h0 r.parent u.parent ;
//    assert (r.parent <> u.parent) ;
      assert (h0 `contains_a_well_typed` u.parent) ;
      assert (h1 `contains_a_well_typed` u.parent) ;
    u.parent := Some r ;
    let h2 = STATE.get () in

    maintain_uf_invariant (build_uf_inv2 h1 h2 u r) ;
//    assert (forall (u0 : ufh a h2). Heap.contains h1 u0.parent);
//    assert (forall (u0 : ufh a h2). u0.parent <> u.parent ==> reach a h2 u0 = reach a h1 u0);
//   if p = r then give_witness #(reachable h0 r u) (Immediately u) else give_proof (map_squash (get_proof (reachable h0 r p)) (fun w -> Later p w u)) ;
    admit () ;
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

(*

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


*)
