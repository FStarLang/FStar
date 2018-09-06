module SL.ConcurrentActions

open SL.Heap
open SL.Effect

let par_comp #a #b (wpa : st_wp a) (wpb : st_wp b) post m1 m2 =
   wpa (fun a m1' -> wpb (fun b m2' -> post (a, b) (m1' <*> m2')) m2) m1
        
let par_wp' #a #b (wpa : st_wp a) (wpb : st_wp b) post m =
    exists m1 m2.
           m == (m1 <*> m2)
        /\ par_comp wpa wpb post m1 m2

(* Silly lemma, but allows to handle goals properly *)
let par_wp'_lemma
  #a #b
  (#wpa : st_wp a)
  (#wpb : st_wp b)
  (m m1 m2 : memory)
  (post : post (a * b))
  (_ : squash (m == (m1 <*> m2)))
  (_ : squash (par_comp wpa wpb post m1 m2))
  //(_ : squash (wpa (fun a m1' -> forall b. post (a, b) m1') m1))
  //(_ : squash (wpb (fun b m2' -> forall a. post (a, b) m2') m2))
     : Lemma (m == (m1 <*> m2)
               /\ (par_comp wpa wpb post m1 m2)) = ()

let par_wp #a #b (wpa : st_wp a) (wpb : st_wp b) : st_wp (a * b) =
  frame_wp (par_wp' wpa wpb)

assume val par : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp' wpa wpb)



(* Locks and operations *)
 // Locks are over a particular reference r.
 // Can we use a list or a set? Non-trivial to make it work. Even a set of addresses causes many blowups.
 // Can we use a heap predicate? Can we automate frame inference then?
assume new type lock : list sref -> (memory -> Type0) -> Type0

(* Does there exist a memory with domain fp such that pred? *)
let dom_exists (fp:list sref) (pred:memory -> Type0) : Type0 =
  let rec aux acc fp : Tot Type0 (decreases fp) =
    match fp with
    | [] -> pred acc
    (* this case prevents spurious `emp <*>` which actually matter (the pattern doesn't kick in?) *)
    (* the pattern was wrong, so not realy needed now, but we might as well keep it I guess *)
    | [h] ->
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      exists (v:ty). pred (acc <*> r |> v)
    | h :: t -> (* Note, if we match on the sigma pair here, we might prevent reduction *)
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      exists (v:ty). aux (acc <*> r |> v) t
  in aux emp fp

let test (r s : ref int) = dom_exists [tosref s; tosref r] (fun m -> m <*> emp == m)

(* Do all memories with domain fp satisfy pred? *)
let dom_forall (fp:list sref) (pred:memory -> Type0) : Type0 =
  let rec aux acc fp : Tot Type0 (decreases fp) =
    match fp with
    | [] -> pred acc
    (* this case prevents spurious `emp <*>` which actually matter (the pattern doesn't kick in?) *)
    (* the pattern was wrong, so not realy needed now, but we might as well keep it I guess *)
    | [h] ->
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      forall (v:ty). pred (acc <*> r |> v)
    | h :: t -> (* Note, if we match on the sigma pair here, we might prevent reduction *)
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      forall (v:ty). aux (acc <*> r |> v) t
  in aux emp fp

let mklock_wp (fp:list sref) (inv : memory -> Type0) post m =
  dom_exists fp (fun m' -> mem_eq (m' == m) /\ inv m /\ (forall (l:lock fp inv). post l emp))
let frame_mklock_wp fp inv = frame_wp (with_fp fp <| mklock_wp fp inv)

assume val mklock : #inv:(memory -> Type0) -> (fp : list sref) ->
                    STATE (lock fp inv) (frame_mklock_wp fp inv)


let acquire_wp fp inv l post m = m == emp /\ (dom_forall fp (fun m -> inv m ==> post () m))
let frame_acquire_wp r inv l = frame_wp (with_fp [] <| acquire_wp r inv l)
assume val acquire : (#fp: list sref) -> (#inv : (memory -> Type0)) -> (l : lock fp inv) ->
                     STATE unit (frame_acquire_wp fp inv l)


let release_wp fp inv l post m =
  dom_exists fp (fun m' -> mem_eq (m' == m) /\ inv m /\ post () emp)
let frame_release_wp fp inv l = frame_wp (with_fp fp <| release_wp fp inv l)
assume val release : (#fp : list sref) -> (#inv : (memory -> Type0)) -> (l : lock fp inv) ->
                     STATE unit (frame_release_wp fp inv l)


// let locking_wp r l wp post m =
//     wp (fun x m' -> forall v m1. m' == (r |> v <*> m1) ==> post x m1) m
// 
// assume val locking : #a:Type -> #b:Type -> #r:(ref a) -> (l : lock r) ->
//                      (#wp : st_wp b) -> (f : unit -> STATE b wp) ->
//                   STATE b (frame_locking_wp r l wp)


(* A version with explicit heaps *)
unfold let par_wp'_exp #a #b (wpa : st_wp a) (wpb : st_wp b) (m1 m2 : memory)
                       (post : post (a * b)) (m : memory) : Type0 =
           m == (m1 <*> m2)
        /\ wpa (fun a m1' -> wpb (fun b m2' -> post (a, b) (m1' <*> m2')) m2) m1

let par_wp_exp #a #b (wpa : st_wp a) (wpb : st_wp b) (m1 m2 : memory) : st_wp (a * b) =
  frame_wp (par_wp'_exp wpa wpb m1 m2)

assume val par_exp : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 (m1 : memory) -> (m2 : memory) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp_exp #a #b wpa wpb m1 m2)

(* Unframed, explicit variant. Not very user-friendly. *)
assume val par_exp' : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 (m1 : memory) -> (m2 : memory) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp'_exp #a #b wpa wpb m1 m2)
