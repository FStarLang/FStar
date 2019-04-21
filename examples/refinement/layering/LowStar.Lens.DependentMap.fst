module LowStar.Lens.DependentMap

open LowStar.Lens
open FStar.HyperStack.ST
open FStar.Tactics
open FStar.BigOps
open FStar.Classical 

module DGM = FStar.DependentGMap
module DM = FStar.DependentMap

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module LB = LowStar.Lens.Buffer
module List = FStar.List.Tot.Base

// DependentMap iterators on the sub-domain of interest

// let fold (#t:eqtype) #a (f:t -> Type) (m:DM.t t f) (dom:list t) 
//   (h : (k:t -> b:(f k) -> a -> a)) (acc : a) : GTot a = 
//   List.fold_left (fun v k -> h k (DM.sel m k) v) acc dom 

// let map  (#t:eqtype) #a (f:t -> Type) (m:DM.t t f) (dom:list t) 
//   (h : (k:t -> b:(f k) -> a)) : list a = 
//   List.map (fun k -> h k (DM.sel m k)) dom 

// // List of dependent pairs from a dependent map
// let to_list (#t:eqtype) (f:t -> Type) (m:DM.t t f) (dom:list t) : list (x:t & (f x)) = 
//   List.map (fun k -> (| k,  DM.sel m k |)) dom 

// all pointers in a heap are live in a given mem 
unfold
let map_inv (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (dom:list t) (h : HS.mem) : Type0 =
  big_and' #t (fun x -> B.live h (DM.sel m x)) dom

// locations of a dependent map
let rec map_loc (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x))) (dom:list t) : GTot B.loc =
match dom with 
| [] -> B.loc_none
| k :: ks -> B.loc_union (B.loc_buffer (DM.sel m k)) (map_loc f m ks)

// Union of locations in a pointer list
let map_eloc #t f m dom : eloc = Ghost.hide (map_loc #t f m dom)

// Lemmas about map_inv
let map_inv_mem (#t:eqtype) (f: t -> Type) (m:DM.t t (fun (x:t) -> B.pointer (f x)))
   (dom:list t) (h : imem (map_inv f m dom)) (x:t{List.memP x dom}) : Lemma (B.live h (DM.sel m x)) =
   let p = big_and'_forall #t (fun x -> B.live h (DM.sel m x)) dom in ()

(* Preservation of liveness after memory updates *)

val g_upd_preserves_live : #a:Type -> #b:Type -> h:HS.mem -> b1:B.pointer a{B.live h b1} -> b2:B.pointer b{B.live h b2} -> v:a ->
  Lemma (let h' = B.g_upd b1 0 v h in B.modifies (B.loc_buffer b1) h h' /\ B.live h' b1 /\ B.live h' b2)
                                   
let g_upd_preserves_live #a #b h b1 b2 v = 
  let p = B.g_upd_seq_as_seq b1 (Seq.upd (B.as_seq h b1) 0 v) h in ()

// and update preserves livenes of the pointer being updated and of any other live list in the heap  
val g_upd_preserves_map_inv : #a:Type -> #t:eqtype -> f:(t -> Type) -> h:HS.mem -> b:B.pointer a{B.live h b} -> v:a ->
  ptr:(DM.t t (fun (x:t) -> B.pointer (f x))) -> dom:list t{map_inv f ptr dom h} ->
  Lemma (let h' = B.g_upd b 0 v h in B.modifies (B.loc_buffer b) h h' /\ B.live h' b /\ map_inv f ptr dom h')


let g_upd_preserves_map_inv #a #t f h b v ptr dom = 
  let h' = B.g_upd b 0 v h in
  let _ = g_upd_preserves_live h b b v in
  assert (B.live h' b);
  assert (B.modifies (B.loc_buffer b) h h');  
  // map liveness, going through all of the key   
  let rec aux (ks : list t{map_inv f ptr ks h}) : Lemma (map_inv f ptr ks h') = 
    match ks with 
    | [] -> admit ()
    | k :: ks' -> 
      let b' = DM.sel ptr k in
      let p1 = g_upd_preserves_live h b b' v in
      assert (B.live h' b); 
      aux ks'
  in aux dom
    

unfold
let dom (#a:eqtype) (lst:list a) : Tot eqtype = x:a{List.memP x lst} 

unfold 
let fin (#a:eqtype) (lst:list a) = (forall x. List.memP x lst) /\ List.noRepeats lst

(* put helper *)

// let rec put_aux (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) (vmap : DM.t t f) (h : imem (map_inv f ptr keys)) : GTot (imem (map_inv f ptr keys))  = 
//   let rec aux (ks : list t{List.noRepeats ks}) (h : imem (map_inv f ptr keys){map_inv f ptr ks h})
//   : GTot (h':imem (map_inv f ptr keys){forall x, ~ List.mem x ks /\ B.live h x => B.get }) = 
//     match ks with 
//     | [] -> h 
//     | k :: ks' ->
//       let b = DM.sel ptr k in 
//       let v = DM.sel vmap k in 
//       let h' = B.g_upd b 0 v h in
//       (* liveness preservation *)
//       let _ = g_upd_preserves_map_inv f h b v ptr keys in 
//       let _ = g_upd_preserves_map_inv f h b v ptr ks' in   
//       aux ks' h'
//   in aux keys h


//   let rec put_aux (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) (vmap : DM.t t f) (h : imem (map_inv f ptr keys)) : GTot (imem (map_inv f ptr keys))  = 
//     let rec aux (ks : list t{List.noRepeats ks}) (h : imem (map_inv f ptr keys){map_inv f ptr ks h})
//     : GTot (h':imem (map_inv f ptr keys){ forall x}) = 
//       match ks with 
//       | [] -> h 
//       | k :: ks' ->
//         let b = DM.sel ptr k in 
//         let v = DM.sel vmap k in 
//         let h' = B.g_upd b 0 v h in
//         (* liveness preservation *)
//         let _ = g_upd_preserves_map_inv f h b v ptr keys in 
//         let _ = g_upd_preserves_map_inv f h b v ptr ks' in   
//         aux ks' h'
//     in aux keys h


(* Lens constructor *)

(* Try 1 : every element of the type t is in the list *)

let mk (#t:eqtype) (f:t -> Type) (keys:list t{fin keys}) (ptr:DM.t t (fun x -> B.pointer (f x))) (h:imem (map_inv f ptr keys)) 
: hs_lens (DM.t t (fun (x:t) -> B.pointer (f x))) (DM.t t f) =
  (* invariant *) 
  let inv = map_inv f ptr keys in
  (* mem snapshot *)
  let (snap : imem (map_inv f ptr keys)) = h in 
  (* footprint *)
  let fp = map_eloc #t f ptr keys in
  (* put *)
  let put : put_t (imem (map_inv f ptr keys)) (DM.t t f) = 
    let rec aux (ks : list t) (vmap : DM.t t f) (h : imem (map_inv f ptr keys){map_inv f ptr ks h})
    : GTot (imem (map_inv f ptr keys))  = 
      match ks with 
      | [] -> h 
      | k :: ks' ->
        let b = DM.sel ptr k in 
        let v = DM.sel vmap k in 
        let h' = B.g_upd b 0 v h in
        (* liveness preservation *)
        let _ = g_upd_preserves_map_inv f h b v ptr keys in 
        let _ = g_upd_preserves_map_inv f h b v ptr ks' in   
        aux ks' vmap h'
    in aux keys
  in
  (* get *) 
  let get : get_t (imem (map_inv f ptr keys)) (DM.t t f) = 
    let aux h = 
      let value (k:t) : GTot (f k) =
        let b = DM.sel ptr k in 
        let _ = map_inv_mem #t f ptr keys h k in 
        assert (B.live h b);
        B.get h b 0
      in DM.create value in aux
  in 
  (* First lens law *)
  let put_property (m : DM.t t f) (h : (imem (map_inv f ptr keys))) (k : t) : Lemma (let b = DM.sel ptr k in B.get (put m h) b 0 == DM.sel m k) =
    admit ()
  in
  let get_put_lem (h : (imem (map_inv f ptr keys))) (m : DM.t t f) (k : t) : Lemma (DM.sel (get (put m h)) k == DM.sel m k) = 
     let h' = put m h in 
     let _ = put_property m h k in  // main assumption about put
     let value (k:t) : GTot (f k) =
       let b = DM.sel ptr k in 
       let _ = map_inv_mem #t f ptr keys h k in 
       B.get h' b 0
     in     
     let _ = DM.sel_create value k in 
     assert (DM.sel (get h') k == (let b = DM.sel ptr k in 
                                   let _ = map_inv_mem #t f ptr keys h k in 
                                   B.get h' b 0));
     ()
  in
  let get_put_lem_ext (h : (imem (map_inv f ptr keys))) (m : DM.t t f) : Lemma (get (put m h) == m)[SMTPat (get (put m h))] = 
      forall_intro (get_put_lem h m);
      DM.equal_elim (get (put m h)) m
  in
  // let get_put' () : Lemma (get_put get put) =
  //   forall_intro_2 #(imem (map_inv f ptr keys)) #(fun _ -> DM.t t f) #(fun h m -> get (put m h) == m) get_put_lem_ext in 
  let l : imem_lens inv (DM.t t f) fp = { 
    get = get;
    put = put;
    lens_laws = admit () // XXX
  } in
  { 
    footprint = fp;
    invariant = (fun ptr -> map_inv f ptr keys);
    x = ptr;
    snapshot = snap;
    l = l
  }
  
// Allocation: scoped allocation
// Experiment: swap with dep map 
// Get/put with lens composition 

let test1 = 
  fin #(n:nat{n <= 2}) [0;1;2]

(* Idea 2 : the domain of the map is resrticted in the elements of the list *)

// let coerce (#a:eqtype) (l : list a) : list (dom #a l) = admit ()

// let mk2 (#t:eqtype) (f:t -> Type) (keys:list t) (ptr:DM.t (dom keys) (fun x -> B.pointer (f x))) (h:imem (map_inv f ptr (coerce keys))) 
// : hs_lens (DM.t (dom keys) (fun (x:t) -> B.pointer (f x))) (DM.t (dom keys) f) = admit ()
