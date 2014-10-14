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
         (fun 'p h0 =>  'Pre (SelHeap h0 moderef) /\ (forall x h1. 'Post (SelHeap h0 moderef) x (SelHeap h1 moderef) ==> 'p x h1))
         (fun 'p h0 => (forall x h1. ('Pre (SelHeap h0 moderef) /\ 'Post (SelHeap h0 moderef) x (SelHeap h1 moderef)) ==> 'p x h1)) 

type Requires ('pre:Pre) = 'pre
type Ensures : #'a:Type => Post 'a => Post 'a = fun ('a:Type) ('post:Post 'a) => 'post
  
(* val get_mode : unit -> Wys mode *)
(*                            (Requires (fun h => True)) *)
(*                            (Ensures  (fun m0 r m1 => m0==m1 /\ r==m1)) *)
let get_mode (x:unit) = ST.read moderef


(* private *)
(* val set_mode : m:mode -> Wys unit *)
(*                              (Requires (fun h => True)) *)
(*                              (Ensures  (fun m0 r m1 => m1==m)) *)
let set_mode (m:mode) = ST.write moderef m


type CanSetMode (cur:mode) (m:mode) = (if b2t (is_Sec cur.p_or_s) then cur.prins==m.prins else Subset cur.prins m.prins)
val with_mode:  'a:Type
             -> 'req_f:(heap => Type)
             -> 'ens_f:(heap => 'a => heap => Type)
             -> m:mode
             -> f:(unit -> ST2 'a 'req_f 'ens_f)
             -> ST2 'a 
                   (fun h0 => 
                          'req_f (UpdHeap h0 moderef m) 
                          /\ CanSetMode (SelHeap h0 moderef) m)
                   (fun h0 a h1 => 
                          (SelHeap h0 moderef == SelHeap h1 moderef)
                          /\ (exists h1'. 'ens_f (UpdHeap h0 moderef m) a h1' /\ h1==UpdHeap h1' moderef (SelHeap h0 moderef)))
let with_mode m f =
  let cur = ST.read moderef in 
  (match cur.p_or_s with
   | Sec -> assert (cur.prins == m.prins)
   | _ -> assert (Subset cur.prins m.prins));
  let x0 = ST.write moderef m in 
  let res = f () in
  let x1 = ST.write moderef cur in 
  res
    
type box 'a =
  | Box : v:'a -> m:mode -> box 'a

logic val mk_box : 'a:Type -> x:'a -> u:unit -> ST2 (box 'a)
                                   (fun h0 => True)
                                   (fun h0 b h1 => h0==h1 /\ b==Box x (SelHeap h0 moderef))
let mk_box ('a:Type) (x:'a) (u:unit) = Box x (get_mode())

logic type CanUnbox ('a:Type) (m:mode) (x:box 'a) = Subset m.prins (Box.m x).prins
logic val unbox: x:box 'a -> u:unit -> ST2 'a
                                     (fun h0 => CanUnbox 'a (SelHeap h0 moderef) x)
                                     (fun h0 a h1 => h0==h1 /\ Box.v x==a)
  
let unbox (x:box 'a) (u:unit) =
  let cur = get_mode () in
  assert (CanUnbox 'a cur x);
  Box.v x

type wire 'a = PartialMap.t prin 'a
open PartialMap

type req_f ('a:Type) (x:box 'a) (h0:heap) = CanUnbox 'a (SelHeap h0 moderef) x
type ens_f ('a:Type) (m:mode) (x:box 'a) (h0:heap) (w:wire 'a) (h1:heap) = 
    HeapEq h0 h1 /\ w==ConstMap m.prins (Box.v x)
val mk_wire : m:mode -> x:box 'a -> ST2 (wire 'a)
                                        (fun h0 => (if b2t (is_Par m.p_or_s)
                                                    then (CanSetMode (SelHeap h0 moderef) m /\ CanUnbox 'a m x)
                                                    else CanUnbox 'a (SelHeap h0 moderef) x))
                                        (fun h0 w h1 => SelHeap h0 moderef==SelHeap h1 moderef (* HeapEq h0 h1 *)
                                                        /\ w==ConstMap m.prins (Box.v x))
let mk_wire (m:mode) (x:box 'a) =
  let f : unit -> ST2 (wire 'a) (req_f 'a x) (ens_f 'a m x) = 
    fun () -> let y = unbox x () in ConstMap m.prins y in
  match m.p_or_s with 
  | Par -> with_mode m f
  | _ -> f ()

let concat_wires (w1:wire 'a) (w2:wire 'a) =
  assert (DisjointDom w1 w2);
  Concat w1 w2

let project_wire (w:wire 'a) (p:prin) =
  assert (InDom p w);
  let cur = get_mode () in
  (match cur.p_or_s with
   | Sec -> assert (InSet p cur.prins)
   | Par -> assert (SetEqual cur.prins (Singleton p)));
  Sel w p
                                
(* (\*--------------------------------------------------------------------------------*\) *)

(* module Millionaires *)
(* open Wysteria *)
(* assume logic val A : prin *)
(* assume logic val B : prin *)
(* assume logic val AB: set prin *)
(* assume AB_distinct: A=!=B *)

(* type eq_check =  *)
(* val is_A_richer_than_B : unit -> Wys bool *)
(*                                      (Requires (fun m => m.p_or_s==Par /\ SetEqual m.prins (Union (Singleton A) (Singleton B)))) *)
(*                                      (Ensures  (fun m0 res m1 => res == false)) *)

(* let is_A_richer_than_B _ = *)
(*   let par_A = {p_or_s=Par; prins=Singleton A} in *)
(*   let par_B = {p_or_s=Par; prins=Singleton B} in *)
(*   let sec_AB = {p_or_s=Sec; prins=Union (Singleton A) (Singleton B)} in *)
(*   let x = with_mode par_A (mk_box 2) in *)
(*   let y = with_mode par_B (mk_box 3) in *)
(*   let z = concat_wires (mk_wire par_A x) (mk_wire par_B y) in *)
(*   let check : unit -> ST2 bool req_check ens_check = fun () -> project_wire z A > project_wire z B in *)
(*   with_mode sec_AB check *)
