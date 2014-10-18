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
assume (* TODO: private *) logic val moderef : ref mode

kind Pre = mode => Type
kind Post ('a:Type) = mode => 'a => mode => Type
effect Wys ('a:Type) ('Pre:Pre) ('Post:Post 'a) =
      STATE 'a 
         (fun 'p h0 =>  'Pre (SelHeap h0 moderef) /\ (forall x h1. 'Post (SelHeap h0 moderef) x (SelHeap h1 moderef) ==> 'p x h1))
         (fun 'p h0 => (forall x h1. ('Pre (SelHeap h0 moderef) /\ 'Post (SelHeap h0 moderef) x (SelHeap h1 moderef)) ==> 'p x h1)) 

logic type Requires ('pre:Pre) = 'pre
logic type Ensures : #'a:Type => Post 'a => Post 'a = fun ('a:Type) ('post:Post 'a) => 'post

(* TODO: private *)  let get_mode (x:unit) = ST.read moderef
(* TODO: private *)  let set_mode (m:mode) = ST.write moderef m

logic type CanSetMode (cur:mode) (m:mode) = (if b2t (is_Sec cur.p_or_s) then cur.prins==m.prins else Subset m.prins cur.prins)
val with_mode:  'a:Type
             -> 'req_f:(heap => Type)
             -> 'ens_f:(heap => 'a => heap => Type)
             -> m:mode
             -> f:(unit -> ST 'a 'req_f 'ens_f)
             -> ST 'a 
                   (fun h0 => 
                          'req_f (UpdHeap h0 moderef m) 
                          /\ CanSetMode (SelHeap h0 moderef) m)
                   (fun h0 a h1 => 
                          (SelHeap h0 moderef == SelHeap h1 moderef)
                          /\ (exists h1'. 'ens_f (UpdHeap h0 moderef m) a h1' /\ h1==UpdHeap h1' moderef (SelHeap h0 moderef)))
let with_mode m f =
  let cur = get_mode () in
  (match cur.p_or_s with
   | Sec -> assert (cur.prins == m.prins)
   | Par   -> assert (Subset m.prins cur.prins));
  set_mode m;
  let res = f () in
  set_mode cur;
  res
    
type box 'a =
  | Box : v:'a -> m:mode -> box 'a

(* No need to annotate, except for testing the result of inference *)
val mk_box : x:'a -> unit -> ST (box 'a)
                                 (fun h0 => True)
                                 (fun h0 b h1 => h0==h1 /\ b==Box x (SelHeap h0 moderef))
let mk_box x u = Box x (get_mode())


logic type CanUnbox ('a:Type) (m:mode) (x:box 'a) = Subset m.prins (Box.m x).prins
(* No need to annotate, except for testing the result of inference *)
val unbox: x:box 'a -> unit -> ST 'a
                                   (fun h0 => CanUnbox 'a (SelHeap h0 moderef) x)
                                   (fun h0 a h1 => h0==h1 /\ Box.v x==a)
let unbox x u =
  let cur = get_mode () in
  assert (CanUnbox _ cur x);
  Box.v x

type wire 'a = PartialMap.t prin 'a
open PartialMap

logic type req_f ('a:Type) (x:box 'a) (h0:heap) = CanUnbox 'a (SelHeap h0 moderef) x
logic type ens_f ('a:Type) (m:mode) (x:box 'a) (h0:heap) (w:wire 'a) (h1:heap) = 
    HeapEq h0 h1 /\ w==ConstMap m.prins (Box.v x)

(* No need to annotate, except for testing the result of inference *)
val mk_wire : 'a:Type -> m:mode -> x:box 'a -> ST (wire 'a)
                                        (fun h0 => (if b2t (is_Par m.p_or_s)
                                                    then (CanSetMode (SelHeap h0 moderef) m /\ CanUnbox 'a m x)
                                                    else CanUnbox 'a (SelHeap h0 moderef) x))
                                        (fun h0 w h1 => SelHeap h0 moderef==SelHeap h1 moderef (* HeapEq h0 h1 *) (* TODO: Need to sort our extensional equality on heaps *) 
                                                        /\ w==ConstMap m.prins (Box.v x))
let mk_wire ('a:Type) m x =
  let f : unit -> ST (wire 'a) (req_f 'a x) (ens_f 'a m x) = (* TODO, should infer an ST type automatically *)
    fun () -> ConstMap m.prins (unbox x ()) in   
  match m.p_or_s with 
    | Par -> with_mode m f
    | Sec -> f ()

let concat_wires (w1:wire 'a) (w2:wire 'a) =
  assert (DisjointDom prin 'a w1 w2);
  Concat w1 w2

logic type proj_ok ('a:Type) (w:wire 'a) (p:prin) (cur:mode) = 
    InDom p w /\ 
    (if b2t (is_Sec cur.p_or_s) 
     then InSet p cur.prins
     else SetEqual cur.prins (Singleton p))

(* no need to annotate, unless you want to check this 
   val project_wire: w:wire 'a -> p:prin -> Wys 'a (proj_ok 'a w p) (fun m1 a m2 => a==Sel w p /\ m1==m2) 
*)
let project_wire (w:wire 'a) (p:prin) =
  assert (InDom p w);
  let cur = get_mode () in
  (match cur.p_or_s with
   | Sec -> assert (InSet p cur.prins)
   | _ -> assert (SetEqual cur.prins (Singleton p)));
  Sel w p
                                
(*--------------------------------------------------------------------------------*)

module Millionaires
open Wysteria
open PartialMap
assume logic val A : prin
assume logic val B : prin
assume logic val AB: set prin
assume AB_distinct: A=!=B

(* LOTS OF BORING TESTS *)
val test2 : unit -> Tot unit
let test2 u = 
  let initial_mode = {p_or_s=Par; prins=(Union (Singleton A) (Singleton B))} in 
  let par_B = {p_or_s=Par; prins=Singleton B} in 
  let par_A = {p_or_s=Par; prins=Singleton A} in 
  let sec_AB = {p_or_s=Sec; prins=Union (Singleton A) (Singleton B)} in
  assert (CanSetMode initial_mode par_A);
  assert (CanSetMode initial_mode par_B);
  assert (CanSetMode initial_mode sec_AB)

val test: unit -> Wys unit
                      (Requires (fun m => m=={p_or_s=Par; prins=(Union (Singleton A) (Singleton B))}))
                      (Ensures  (fun m0 res m1 => True))
let test _ =
  let par_A = {p_or_s=Par; prins=Singleton A} in
  let par_B = {p_or_s=Par; prins=Singleton B} in
  let sec_AB = {p_or_s=Sec; prins=Union (Singleton A) (Singleton B)} in
  let x = with_mode par_A (mk_box 2) in
  let y = with_mode par_B (mk_box 3) in
  let z = concat_wires (mk_wire par_A x) (mk_wire par_B y) in
  assert (Box.v x == 2);
  assert (Box.v y == 3);
  assert (z == Concat (ConstMap (Singleton A) 2) (ConstMap (Singleton B) 3));
  assert (Sel z A == 2);
  assert (Sel z B == 3);
  assert (InDom A z);
  let x = Sel z A > Sel z B in
  assert (x == false);
  assert (proj_ok int z A sec_AB)

  
logic type req_check (z:wire int) (h:heap) = 
          (z == Concat (ConstMap (Singleton A) 2) (ConstMap (Singleton B) 3)) /\
            proj_ok int z A (SelHeap h moderef) /\ 
            proj_ok int z B (SelHeap h moderef)
logic type ens_check (h0:heap) (b:bool) (h1:heap) = b==false

(* This is the main client of Wysteria *)
val is_A_richer_than_B : unit -> Wys bool
                                     (Requires (fun m => m=={p_or_s=Par; prins=(Union (Singleton A) (Singleton B))}))
                                     (Ensures  (fun m0 res m1 => res == false))
let is_A_richer_than_B _ =
  let par_A = {p_or_s=Par; prins=Singleton A} in
  let par_B = {p_or_s=Par; prins=Singleton B} in
  let sec_AB = {p_or_s=Sec; prins=Union (Singleton A) (Singleton B)} in
  let x = with_mode par_A (mk_box 2) in
  let y = with_mode par_B (mk_box 3) in
  let z = concat_wires (mk_wire par_A x) (mk_wire par_B y) in
  let check : unit -> ST bool (req_check z) ens_check = fun () -> (* XXX TODO, should infer an ST type automatically *)
    project_wire z A > project_wire z B in
  with_mode sec_AB check
