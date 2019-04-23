module LowStar.Lens.DependentMap

open LowStar.Lens
open FStar.HyperStack.ST
open FStar.Tactics
open FStar.BigOps
open FStar.Classical 
open LowStar.BufferOps 
open FStar.Modifies

module L = LowStar.Lens
module LB = LowStar.Lens.Buffer
module DGM = FStar.DependentGMap
module DM = FStar.DependentMap

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module LB = LowStar.Lens.Buffer
module List = FStar.List.Tot.Base
module ListP = FStar.List.Tot.Properties

unfold 
let fin (#a:eqtype) (lst:list a) = (forall x. List.memP x lst) /\ List.noRepeats lst

// all pointers in a heap are live in a given mem 
unfold
let map_inv' (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (dom:list t) (h : HS.mem) : Type0 =
  big_and' #t (fun x -> B.live h (DM.sel m x)) dom

unfold 
let map_inv (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (h : HS.mem) : Type0 =
  forall (x:t). B.live h (DM.sel m x)
  

 
// locations of a dependent map
let rec map_loc (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (dom:list t) : GTot B.loc =
match dom with 
| [] -> B.loc_none
| k :: ks -> B.loc_union (B.loc_buffer (DM.sel m k)) (map_loc f m ks)

// Union of locations in a pointer list
let map_eloc #t f m dom : eloc = Ghost.hide (map_loc #t f m dom)

// Lemmas about map_inv
let map_inv_mem' (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x)))
   (dom:list t) (h : imem (map_inv' f m dom)) (x:t{List.memP x dom}) : Lemma (B.live h (DM.sel m x)) =
   let p = big_and'_forall #t (fun x -> B.live h (DM.sel m x)) dom in ()

let map_inv_mem (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x)))
  (h : imem (map_inv f m)) (x:t) : Lemma (B.live h (DM.sel m x)) = ()

(* Preservation of liveness after memory updates *)

val g_upd_preserves_live : #a:Type -> #b:Type -> h:HS.mem -> b1:B.pointer a{B.live h b1} -> b2:B.pointer b{B.live h b2} -> v:a ->
  Lemma (let h' = B.g_upd b1 0 v h in B.modifies (B.loc_buffer b1) h h' /\ B.live h' b1 /\ B.live h' b2)
                                   
let g_upd_preserves_live #a #b h b1 b2 v = 
  let p = B.g_upd_seq_as_seq b1 (Seq.upd (B.as_seq h b1) 0 v) h in ()
  
// update preserves livenes of the pointer being updated and the heap invariant
val g_upd_preserves_map_inv' : #a:Type -> #t:eqtype -> f:(t -> Type) -> h:HS.mem -> b:B.pointer a{B.live h b} -> v:a ->
  ptr:(DM.t t (fun (x:t) -> B.pointer (f x))) -> dom:list t{map_inv' f ptr dom h} ->
  Lemma (let h' = B.g_upd b 0 v h in B.modifies (B.loc_buffer b) h h' /\ B.live h' b /\ map_inv' f ptr dom h')

let g_upd_preserves_map_inv' #a #t f h b v ptr dom = 
  let h' = B.g_upd b 0 v h in
  let _ = g_upd_preserves_live h b b v in
  assert (B.live h' b);
  assert (B.modifies (B.loc_buffer b) h h');  
  // map liveness, going through all of the key   
  let rec aux (ks : list t{map_inv' f ptr ks h}) : Lemma (map_inv' f ptr ks h') = 
    match ks with 
    | [] -> admit ()
    | k :: ks' -> 
      let b' = DM.sel ptr k in
      let p1 = g_upd_preserves_live h b b' v in
      assert (B.live h' b); 
      aux ks'
  in aux dom

val g_upd_preserves_map_inv : #a:Type -> #t:eqtype -> f:(t -> Type) -> h:HS.mem -> b:B.pointer a{B.live h b} -> v:a ->
  ptr:(DM.t t (fun (x:t) -> B.pointer (f x))){map_inv f ptr h} ->
  Lemma (let h' = B.g_upd b 0 v h in B.modifies (B.loc_buffer b) h h' /\ B.live h' b /\ map_inv f ptr h')

let g_upd_preserves_map_inv #a #t f h b v ptr =
  let h' = B.g_upd b 0 v h in
  let _ = g_upd_preserves_live h b b v in
  assert (B.live h' b);
  assert (B.modifies (B.loc_buffer b) h h'); 
  let lem (x : t) : Lemma (B.live h' (DM.sel ptr x)) = 
    let b' = DM.sel ptr x in
    let h' = B.g_upd b 0 v h in
    let _ = g_upd_preserves_live h b b' v in ()
  in 
  ()

// Lemmas about map_eloc
let map_loc_includes (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (dom:list t{fin dom}) (x:t) 
: Lemma (B.loc_includes (map_loc f m dom) (B.loc_buffer (DM.sel m x))) = 
  assert (List.memP x dom);
  let rec aux (ks : list t {List.memP x ks}) : Lemma (ensures (B.loc_includes (map_loc f m ks) (B.loc_buffer (DM.sel m x)))) (decreases ks) =
    match ks with 
    | [] -> ()
    | k :: ks' ->
      if (x = k) then  
        (B.loc_includes_refl (B.loc_buffer (DM.sel m k));
         B.loc_includes_union_l (B.loc_buffer (DM.sel m x)) (map_loc f m ks') (B.loc_buffer (DM.sel m k)))
      else 
        (aux ks';
         B.loc_includes_union_l (B.loc_buffer (DM.sel m k)) (map_loc f m ks') (B.loc_buffer (DM.sel m x)))
  in aux dom

let map_eloc_includes (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (dom:list t{fin dom}) x
: Lemma (B.loc_includes (L.as_loc (map_eloc f m dom)) (B.loc_buffer (DM.sel m x))) =
  map_loc_includes f m dom x 
  
let map_eloc_eq (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (ks:list t) 
: Lemma (as_loc (map_eloc f m ks) == map_loc f m ks) = 
  Ghost.reveal_hide (map_loc f m ks)

(* put *)
let rec put_aux (#t:eqtype) (f:t -> Type) (keys:list t) (ptr:DM.t t (fun x -> B.pointer (f x))) (vmap : DGM.t t f) (h : imem (map_inv f ptr))
: GTot (imem (map_inv f ptr)) =
  match keys with 
  | [] -> h 
  | k :: ks' -> 
    let b = DM.sel ptr k in 
    let v = DGM.sel vmap k in 
    let h' = B.g_upd b 0 v h in
    (* liveness preservation *)
     let _ = g_upd_preserves_map_inv f h b v ptr in 
     put_aux f ks' ptr vmap h'


let put (#t:eqtype) (f:t -> Type) (keys:list t) (ptr:DM.t t (fun x -> B.pointer (f x))) : put_t (imem (map_inv f ptr)) (DGM.t t f) = put_aux f keys ptr 

(* get *) 
let get (#t:eqtype) (f:t -> Type) (ptr:DM.t t (fun x -> B.pointer (f x))) : get_t (imem (map_inv f ptr)) (DGM.t t f) = 
  fun h -> 
    let value (k:t) : GTot (f k) =
      let b = DM.sel ptr k in 
      let _ = map_inv_mem #t f ptr h k in 
      assert (B.live h b);
      B.get h b 0
    in DGM.create value 

let get_eq (#t:eqtype) (f:t -> Type) (ptr:DM.t t (fun x -> B.pointer (f x))) (x:t) (h : (imem (map_inv f ptr)))
: Lemma (DGM.sel (get f ptr h) x == (let b = DM.sel ptr x in 
                                     let _ = map_inv_mem #t f ptr h x in 
                                     B.get h b 0)) = ()

let get_reads_lemma' (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) 
  (h0 h1:imem (map_inv f ptr)) loc : 
  Lemma (requires (B.loc_disjoint (L.as_loc (map_eloc f ptr keys)) loc /\
                   B.modifies loc h0 h1))
        (ensures (get f ptr h0 == get f ptr h1)) = 
     let lem (x:t) : Lemma (DGM.sel (get f ptr h0) x == DGM.sel (get f  ptr h1) x) = 
       let m0 = get f ptr h0 in
       let m1 = get f ptr h1 in
       let b = DM.sel ptr x in 
       map_inv_mem #t f ptr h0 x;
       map_inv_mem #t f ptr h1 x;
       assert (DGM.sel m0 x == B.get h0 b 0);
       assert (DGM.sel m1 x ==  B.get h1 b 0);
       map_eloc_includes f ptr keys x;
       B.loc_includes_refl loc;
       B.loc_disjoint_includes (L.as_loc (map_eloc f ptr keys)) loc (B.loc_buffer b) loc;
       assert (B.loc_disjoint (B.loc_buffer b) loc);
       B.modifies_buffer_elim b loc h0 h1
     in  
     forall_intro lem;
     let _ = DGM.equal_elim (get f ptr h0) (get f ptr h1) in ()

let get_reads_lemma (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) 
: Lemma (L.get_reads_loc #_ #(map_inv f ptr) (map_eloc f ptr keys) (get f ptr)) = 
  let lem h0 h1 loc : Lemma (B.loc_disjoint (L.as_loc (map_eloc f ptr keys)) loc /\ B.modifies loc h0 h1 ==> get f ptr h0 == get f ptr h1)[SMTPat (B.modifies loc h0 h1); SMTPat (get f ptr h1)] = 
     move_requires (get_reads_lemma' f keys ptr h0 h1) loc
  in ()


let put_modifies_lemma' (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) (vmap : DGM.t t f) (h : imem (map_inv f ptr))
: Lemma (B.modifies (as_loc (map_eloc f ptr keys)) h (put f keys ptr vmap h))[SMTPat (put f keys ptr vmap h)]  = 
let rec aux (ks : list t) (h : imem (map_inv f ptr)) : Lemma (B.modifies (as_loc (map_eloc f ptr ks)) h (put f ks ptr vmap h)) = 
   match ks with 
   | [] -> B.modifies_refl (as_loc (map_eloc f ptr ks)) h
   | k :: ks' ->
     let b = DM.sel ptr k in 
     let v = DGM.sel vmap k in 
     let h' = B.g_upd b 0 v h in
     let _ = g_upd_preserves_map_inv f h b v ptr in 
     aux ks' h';
     B.modifies_trans (B.loc_buffer b) h h' (as_loc (map_eloc f ptr ks')) (put f ks' ptr vmap h');
     map_eloc_eq f ptr ks';
     map_eloc_eq f ptr ks;
     assert (B.modifies (as_loc (map_eloc f ptr ks)) h (put f ks ptr vmap h))
 in aux keys h

 let put_modifies_lemma (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x)))
 : Lemma (L.put_modifies_loc #_ #(map_inv f ptr) (map_eloc f ptr keys) (put f keys ptr)) =  
 let _ = put_modifies_lemma' f keys ptr in ()


let invariant_reads_loc_lemma' (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) 
  (h0 h1:imem (map_inv f ptr)) loc : Lemma (requires (map_inv f ptr h0 /\ B.loc_disjoint (as_loc (map_eloc f ptr keys)) loc /\ B.modifies loc h0 h1))
                                           (ensures (map_inv f ptr h1)) = 
  let aux (x:t) : Lemma (B.live h1 (DM.sel ptr x)) =
    let b = DM.sel ptr x in 
    map_eloc_includes f ptr keys x;
    B.loc_includes_refl loc;
    B.loc_disjoint_includes (L.as_loc (map_eloc f ptr keys)) loc (B.loc_buffer b) loc;
    assert (B.loc_disjoint (B.loc_buffer b) loc);
    B.address_liveness_insensitive_buffer b;
    assert (B.live h0 b); 
    B.loc_includes_none B.address_liveness_insensitive_locs;
    B.modifies_liveness_insensitive_buffer loc B.loc_none h0 h1 b
  in ()

let invariant_reads_loc_lemma (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) 
: Lemma (L.invariant_reads_loc (map_inv f ptr) (map_eloc f ptr keys)) =
  let lem (h0 h1:imem (map_inv f ptr)) loc : Lemma (map_inv f ptr h0 /\ B.loc_disjoint (as_loc (map_eloc f ptr keys)) loc /\ B.modifies loc h0 h1 ==> map_inv f ptr h1)[SMTPat (B.modifies loc h0 h1); SMTPat (map_inv f ptr h1)] = 
    move_requires (invariant_reads_loc_lemma' f keys ptr h0 h1) loc
  in admit ()

(* First lens law *)
let put_property (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x)))
  (m : DGM.t t f) (h : (imem (map_inv f ptr))) (k : t) : Lemma (let b = DM.sel ptr k in B.get (put f keys ptr m h) b 0 == DGM.sel m k) =
  admit ()

let get_put_lem (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) 
  (h : (imem (map_inv f ptr))) (m : DGM.t t f) (k : t) : Lemma (DGM.sel (get f ptr (put f keys ptr m h)) k == DGM.sel m k) = 
   let h' = put f keys ptr m h in 
   let _ = put_property f keys ptr m h k in  // main assumption about put
   () 
   
let get_put_lem_ext (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) 
  (h : (imem (map_inv f ptr))) (m : DGM.t t f) : Lemma (get f ptr (put f keys ptr m h) == m)[SMTPat (get f ptr (put f keys ptr m h))] = 
  forall_intro (get_put_lem f keys ptr h m);
  DGM.equal_elim (get f ptr (put  f keys ptr m h)) m

// These do not work when nested 
let get_put_law (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) : Lemma (get_put (get f ptr) (put f keys ptr)) = 
  let p = get_put_lem_ext f keys ptr in
  ()

let get_put_law' (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) : squash (get_put (get f ptr) (put f keys ptr)) = 
  let p = get_put_lem_ext f keys ptr in
  ()


let mem_lens (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) fp : imem_lens (map_inv f ptr) (DGM.t t f) fp = 
  get_reads_lemma f keys ptr;
  put_modifies_lemma f keys ptr;
  invariant_reads_loc_lemma f keys ptr;
  let p = {  
    get = get f ptr;
    put = put f keys ptr;
    lens_laws = get_put_law' f keys ptr 
  }
  in admit() // XXX doesn't work
  

let reader_t (#t:eqtype) (#f: t -> Type) (l : hs_lens (DM.t t (fun (x:t) -> B.pointer (f x))) (DGM.t t f)) = 
    (i:t) -> 
    LensST (f i) l 
      (requires (fun f1 -> True)) 
      (ensures (fun f1 v f2 -> f1 == f2 /\ v == DGM.sel f2 i))

let writer_t (#t:eqtype) (#f: t -> Type) (l : hs_lens (DM.t t (fun (x:t) -> B.pointer (f x))) (DGM.t t f)) = 
    (i:t) -> (v: f i) -> 
    LensST unit l 
      (requires (fun f1 -> True)) 
      (ensures (fun f1 _ f2 -> f2 == DGM.upd f1 i v))
noeq
type map_lens (#t:eqtype) (f:t -> Type) = 
  | Mk : lens:hs_lens (DM.t t (fun (x:t) -> B.pointer (f x))) (DGM.t t f) -> 
         reader:LB.with_state lens reader_t -> 
         writer:LB.with_state lens writer_t ->
         map_lens f

(* Lens constructor *)

let mk (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) (h:imem (map_inv f ptr)) 
: map_lens f =
  (* invariant *) 
  let inv = map_inv f ptr in
  (* mem snapshot *)
  let (snap : imem (map_inv f ptr)) = h in 
  (* footprint *)
  let fp = map_eloc #t f ptr keys in
  let lens : hs_lens (DM.t t (fun (x:t) -> B.pointer (f x))) (DGM.t t f) = { 
    footprint = fp;
    invariant = map_inv f;
    x = ptr;
    snapshot = snap;
    l = mem_lens f keys ptr fp
  } in
  let reader : LB.with_state lens reader_t = 
    fun s i -> 
      reveal_inv ();
      let h = HST.get () in 
      assume (L.inv lens h); // XXX fails
      assume (map_inv f ptr h); // XXX fails
      let b = DM.sel ptr i in 
      assume (B.live h b); // XXX fails
      let v = B.index b 0ul in 
      assert (v == B.get h b 0);
      let _ =  gest_eq f ptr i h in 
      v
  in 
  let writer : LB.with_state lens writer_t = 
    fun s i v -> 
      let b = DM.sel ptr i in
      admit () // B.upd b 0ul v
  in 
  Mk lens reader writer
  
      


// Allocation: scoped allocation
// Experiment: swap with dep map 
// Get/put with lens composition 

let test1 = 
  fin #(n:nat{n <= 2}) [0;1;2]

(* Idea 2 : the domain of the map is resrticted in the elements of the list *)

unfold
let dom (#a:eqtype) (lst:list a) : Tot eqtype = x:a{List.memP x lst} 

// let coerce (#a:eqtype) (l : list a) : list (dom #a l) = admit ()

// let mk2 (#t:eqtype) (f:t -> Type) (keys:list t) (ptr:DGM.t (dom keys) (fun x -> B.pointer (f x))) (h:imem (map_inv f ptr (coerce keys))) 
// : hs_lens (DGM.t (dom keys) (fun (x:t) -> B.pointer (f x))) (DGM.t (dom keys) f) = admit ()
*)
