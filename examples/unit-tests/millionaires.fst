module Wysteria
open Prims.STATE

type prin 
type prins = set prin 
type p_or_s = 
  | Par 
  | Sec
type mode = { 
  p_or_s: p_or_s; 
  prins: prins 
}
assume (* private *) logic val moderef : ref mode

kind Pre = mode => Type
kind Post ('a:Type) = mode => 'a => mode => Type
effect Wys ('a:Type) ('Pre:Pre) ('Post:Post 'a) =
      STATE 'a 
         (fun 'p h0 =>  'Pre (SelHeap h0 moderef) /\ (forall xxx hhh1. 'Post (SelHeap h0 moderef) xxx (SelHeap hhh1 moderef) ==> 'p xxx hhh1))
         (fun 'p h0 => (forall x h1. ('Pre (SelHeap h0 moderef) /\ 'Post (SelHeap h0 moderef) x (SelHeap h1 moderef)) ==> 'p x h1))

type Requires ('pre:Pre) = 'pre
type Ensures ('a:Type) ('post:Post 'a) = 'post


assume val rd : string -> Wys mode (Requires (fun h => True)) (Ensures mode (fun m1 r m2 => m1==r /\ r==m2))
assume val wr : m:mode -> Wys unit (Requires (fun h => True)) (Ensures unit (fun m1 r m2 => m2==m))

assume val f: int -> Wys bool (Requires (fun h => True)) (Ensures bool (fun m0 u m1 => True))
val test_st : m:mode -> State unit
                            (fun 'p h0 => (forall h1. SelHeap h1 moderef==SelHeap h0 moderef ==> 'p () h1))
let test_st (m:mode) = 
  let cur = rd "hello" in
  let z = f 0 in
  ST.write moderef cur

  
(* (\* let get_mode (x:unit) = !moderef *\) *)

(* assume val get_mode : unit -> Wys mode *)
(*                            (Requires (fun h => True)) *)
(*                            (Ensures mode (fun m0 r m1 => m0==m1 /\ r==m1)) *)
(* (\* let get_mode (x:unit) = !moderef *\) *)


(* (\* private  *\) *)
(* assume val set_mode : m:mode -> Wys unit *)
(*                              (Requires (fun h => True)) *)
(*                              (Ensures unit (fun m0 r m1 => m1==m)) *)
(* (\* let set_mode (m:mode) = ST.write moderef m *\) *)

(* val with_mode: 'a:Type  *)
(*              -> 'Pre:(mode => Type)  *)
(*              -> 'Post:(mode => 'a => mode => Type)  *)
(*              -> m:mode  *)
(*              -> f:(unit -> Wys 'a 'Pre 'Post) *)
(*              -> Wys 'a (Requires (fun cur => 'Pre m))// /\ (if cur.p_or_s==Sec then cur.prins==m.prins else Subset cur.prins m.prins))) *)
(*                        (Ensures _ (fun m1 a m2 => False)) *)
(* let with_mode ('a:Type) ('Pre:Pre) ('Post:Post 'a) (m:mode) (f:unit -> Wys 'a 'Pre 'Post) = *)
(*   let cur = get_mode () in *)
(*   (\* (match cur.p_or_s with *\) *)
(*   (\*  | Sec -> assert (cur.prins == m.prins) *\) *)
(*   (\*  | _ -> assert (0==0)); *\) *)
(*   let x0 = set_mode m in *)
(*   let res = f () in *)
(*   let x1 = set_mode cur in *)
(*   res *)
           
(* (\* type box 'a = *\) *)
(* (\*   | Box : v:'a -> m:mode -> box 'a *\) *)

(* (\* let mk_box (x:'a) (u:unit) = Box x (get_mode()) *\) *)

(* (\* let unbox (x:box 'a) (u:unit) = *\) *)
(* (\*   let cur = get_mode () in *\) *)
(* (\*   assert (SupsetEq prin (Box.m x).prins cur.prins); *\) *)
(* (\*   Box.v x *\) *)

(* (\* type wire 'a = PartialMap.t prin 'a *\) *)
(* (\* open PartialMap *\) *)
 
(* (\* let mk_wire (m:mode) (x:box 'a) = *\) *)
(* (\*   let f (u:unit) = ConstMap m.prins (unbox x ()) in *\) *)
(* (\*   match m.p_or_s with *\) *)
(* (\*   | Sec -> f () *\) *)
(* (\*   | Par -> with_mode m f *\) *)

(* (\* let concat_wires (w1:wire 'a) (w2:wire 'a) = *\) *)
(* (\*   assert (DisjointDom prin 'a w1 w2); *\) *)
(* (\*   Concat w1 w2 *\) *)

(* (\* let project_wire (w:wire 'a) (p:prin) = *\) *)
(* (\*   assert (InDom p w); *\) *)
(* (\*   let cur = get_mode () in *\) *)
(* (\*   (match cur.p_or_s with *\) *)
(* (\*    | Sec -> assert (InSet p cur.prins) *\) *)
(* (\*    | Par -> assert (SetEqual cur.prins (Singleton p))); *\) *)
(* (\*   Sel w p *\) *)
                                
(* (\* (\\*--------------------------------------------------------------------------------*\\) *\) *)

(* (\* module Millionaires *\) *)
(* (\* open Wysteria *\) *)
(* (\* assume val A : prin *\) *)
(* (\* assume val B : prin *\) *)
(* (\* assume AB_distinct: A=!=B *\) *)

(* (\* val is_A_richer_than_B : unit -> Wys bool *\) *)
(* (\*                                      (Requires (fun m => m.p_or_s==Par /\ SetEqual m.prins EmptySet))// (Singleton prin A)))// (Union (Singleton A) (Singleton B)))) *\) *)
(* (\*                                      (Ensures bool (fun m0 res m1 => res == false)) *\) *)
(* (\* let is_A_richer_than_B (u:unit) = *\) *)
(* (\*   let par_A = {p_or_s=Par; prins=Singleton A} in *\) *)
(* (\*   let par_B = {p_or_s=Par; prins=Singleton B} in *\) *)
(* (\*   let sec_AB = {p_or_s=Sec; prins=Union (Singleton A) (Singleton B)} in *\) *)
(* (\*   let x = with_mode par_A (mk_box 2) in *\) *)
(* (\*   let y = with_mode par_B (mk_box 3) in *\) *)
(* (\*   let z = concat_wires (mk_wire par_A x) (mk_wire par_B y) in *\) *)
(* (\*   with_mode sec_AB (fun (u:unit) -> project_wire z A > project_wire z B) *\) *)
