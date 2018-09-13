module SL.ConcurrentActions

open SL.Heap
open SL.Effect

let par_comp #a #b (wpa : st_wp a) (wpb : st_wp b) post m1 m2 =
   wpa (fun a m1' -> wpb (fun b m2' -> post (a, b) (m1' <*> m2')) m2) m1
        
let par_wp' #a #b (wpa : st_wp a) (wpb : st_wp b) post m =
    exists m1 m2.
           m == (m1 <*> m2)
        /\ par_comp wpa wpb post m1 m2

let par_wp'_lemma
  #a #b
  (#wpa : st_wp a)
  (#wpb : st_wp b)
  (m m1 m2 : memory)
  (post : post (a * b))
  (_ : squash (m == (m1 <*> m2)))
  (_ : squash (par_comp wpa wpb post m1 m2))
     : Lemma (m == (m1 <*> m2)
               /\ (par_comp wpa wpb post m1 m2)) = ()

let par_wp #a #b (wpa : st_wp a) (wpb : st_wp b) : st_wp (a * b) =
  frame_wp (par_wp' wpa wpb)

assume val par : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp' wpa wpb) (* big footprint style *)



(* Locks and operations *)

assume new type lock : list sref -> (memory -> Type0) -> Type0

let mklock_wp (fp:list sref) (inv : memory -> Type0) post m =
  dom_exists fp (fun m' -> mem_eq (m' == m) /\ inv m /\ (forall (l:lock fp inv). post l emp))

assume val mklock : #inv:(memory -> Type0) -> (fp : list sref) ->
                    ST (lock fp inv) (mklock_wp fp inv) fp


let acquire_wp fp inv l post m = m == emp /\ (dom_forall fp (fun m -> inv m ==> post () m))
assume val acquire : (#fp: list sref) -> (#inv : (memory -> Type0)) -> (l : lock fp inv) ->
                     ST unit (acquire_wp fp inv l) []


let release_wp fp inv l post m =
  dom_exists fp (fun m' -> mem_eq (m' == m) /\ inv m /\ post () emp)
assume val release : (#fp : list sref) -> (#inv : (memory -> Type0)) -> (l : lock fp inv) ->
                     ST unit (release_wp fp inv l) fp
