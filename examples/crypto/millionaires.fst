module Wysteria
open Prims.STATE
open Set

type prin = string 
type prins = set prin 
type p_or_s = 
  | Par 
  | Sec
type mode = { 
  p_or_s: p_or_s; 
  prins: prins 
}
assume (* TODO: private *) logic val moderef : ref mode

(* TODO: private *)  let get_mode (x:unit) = ST.read moderef
(* TODO: private *)  let set_mode (m:mode) = ST.write moderef m

opaque logic type CanSetMode (cur:mode) (m:mode) = 
                 (if b2t (is_Sec cur.p_or_s)
                  then cur.prins==m.prins 
                  else Set.Subset m.prins cur.prins)
val with_mode:  a:Type
             -> req_f:(heap -> Type)
             -> ens_f:(heap -> a -> heap -> Type)
             -> m:mode
             -> =f:(unit -> ST a req_f ens_f)
             -> ST a 
                   (requires (fun h0 -> 
                          req_f (Heap.upd h0 moderef m) 
                          /\ CanSetMode (Heap.sel h0 moderef) m))
                   (ensures (fun h0 a h1 -> 
                          (Heap.sel h0 moderef == Heap.sel h1 moderef)
                          /\ (exists h1'. ens_f (Heap.upd h0 moderef m) a h1' /\ h1==Heap.upd h1' moderef (Heap.sel h0 moderef))))
let with_mode m f =
  let cur = get_mode () in
  (match cur.p_or_s with
   | Sec -> assert (cur.prins == m.prins)
   | Par   -> assert (Subset m.prins cur.prins));
  set_mode m;
  let res = f () in
  set_mode cur;
  res
    
type box (a:Type) =
  | Box : v:a -> m:mode -> box a

(* No need to annotate, except for testing the result of inference *)
val mk_box : a:Type -> x:a -> unit -> ST (box a)
                                         (requires \h0 -> True)
                                         (ensures  \h0 b h1 -> h0==h1 /\ b==Box x (Heap.sel h0 moderef))
let mk_box x u = Box x (get_mode())


logic type CanUnbox (a:Type) (m:mode) (x:box a) = Subset m.prins (Box.m x).prins
(* No need to annotate, except for testing the result of inference *)
val unbox: a:Type -> x:box a -> unit -> ST a
                                           (requires \h0 -> CanUnbox a (Heap.sel h0 moderef) x)
                                           (ensures  \h0 a h1 -> h0==h1 /\ Box.v x==a)
let unbox x u =
  let cur = get_mode () in
  assert (CanUnbox _ cur x);
  Box.v x

type wire (a:Type) = Map.t prin a
open Map

logic type req_f (a:Type) (x:box a) (h0:heap) = CanUnbox a (Heap.sel h0 moderef) x
logic type ens_f (a:Type) (m:mode) (x:box a) (h0:heap) (w:wire a) (h1:heap) = 
    Heap.equal h0 h1 /\ w==Map.const_on m.prins (Box.v x)

(* No need to annotate, except for testing the result of inference *)
val mk_wire : a:Type -> m:mode -> x:box a -> ST (wire a)
                                        (requires \h0 -> (if is_Par m.p_or_s
                                                          then (CanSetMode (Heap.sel h0 moderef) m /\ CanUnbox a m x)
                                                          else CanUnbox a (Heap.sel h0 moderef) x))
                                        (ensures  \h0 w h1 -> Heap.sel h0 moderef==Heap.sel h1 moderef (* HeapEq h0 h1 *) (* TODO: Need to sort our extensional equality on heaps *) 
                                                             /\ w==Map.const_on m.prins (Box.v x))
let mk_wire (a:Type) m x =
  let f : unit -> ST (wire a) (req_f a x) (ens_f a m x) = (* TODO, should infer an ST type automatically *)
    fun () -> Map.const_on m.prins (unbox x ()) in   
  match m.p_or_s with 
    | Par -> with_mode m f
    | Sec -> f ()

val concat_wires: a:Type -> w1:wire a -> w2:wire a 
                  -> Pure (wire a) 
                          (requires (DisjointDom prin a w1 w2)) 
                          (ensures \r -> r = Map.concat w1 w2)
let concat_wires (a:Type) (w1:wire a) (w2:wire a) =
  assert (DisjointDom prin a w1 w2);
  Map.concat w1 w2

logic type proj_ok (a:Type) (w:wire a) (p:prin) (cur:mode) = 
    Map.contains w p /\ 
    (if is_Sec cur.p_or_s
     then Set.mem p cur.prins
     else Set.Equal cur.prins (Set.singleton p))

kind Pre = mode -> Type
kind Post (a:Type) = mode -> a -> mode -> Type
effect Wys (a:Type) (pre:Pre) (post:Post a) =
      STATE a 
         (fun 'p h0 -> pre (Heap.sel h0 moderef) /\ (forall x h1. post (Heap.sel h0 moderef) x (Heap.sel h1 moderef) ==> 'p x h1))
         (fun 'p h0 -> (forall x h1. (pre (Heap.sel h0 moderef) /\ post (Heap.sel h0 moderef) x (Heap.sel h1 moderef)) ==> 'p x h1))

val project_wire: a:Type -> w:wire a -> p:prin -> Wys a (proj_ok a w p)
                                                        (fun m1 a m2 -> a==Map.sel w p /\ m1==m2) 
let project_wire (a:Type) (w:wire a) (p:prin) =
  assert (Map.contains w p);
  let cur = get_mode () in
  (match cur.p_or_s with
   | Sec -> assert (Set.mem p cur.prins)
   | _ -> assert (Set.Equal cur.prins (Set.singleton p)));
  Map.sel w p


                                
(*--------------------------------------------------------------------------------*)

module Millionaires
open Wysteria
open PartialMap

let pA = "A"
let pB = "B"
let setAB = Set.union (Set.singleton pB) (Set.singleton pA) 
let initial_mode = {p_or_s=Par; prins=setAB}
let par_A = {p_or_s=Par; prins=Set.singleton pA} 
let par_B = {p_or_s=Par; prins=Set.singleton pB} 
let sec_AB = {p_or_s=Sec; prins=setAB}

(* SOME BORING TESTS *)
val test2 : unit -> Tot unit
let test2 u = 
  assert (Set.Subset (Set.empty prin) initial_mode.prins);
  assert (Set.Subset (Set.empty prin) par_A.prins);
  assert (Set.Subset (Set.singleton pA) setAB);
  assert (CanSetMode initial_mode par_A);
  assert (CanSetMode initial_mode par_B);
  assert (CanSetMode initial_mode sec_AB)

val test: unit -> Wys unit
                      (requires \m -> m=={p_or_s=Par; prins=setAB})
                      (ensures  \m0 res m1 -> True)
let test _ =
  let x = with_mode par_A (mk_box 2) in
  let y = with_mode par_B (mk_box 3) in
  let z = concat_wires (mk_wire par_A x) (mk_wire par_B y) in 
  assert (Box.v x == 2);
  assert (Box.v y == 3);
  assert (z == Map.concat (Map.const_on (Set.singleton pA) 2) (Map.const_on (Set.singleton pB) 3));
  assert (Map.sel z pA == 2);
  assert (Map.sel z pB == 3);
  assert (Map.contains z pA);
  let x = Map.sel z pA > Map.sel z pB in
  assert (x == false);
  assert (proj_ok int z pA sec_AB)

let wire_ab = Map.concat (Map.const_on (Set.singleton pA) 2)
                         (Map.const_on (Set.singleton pB) 3)
  
logic type req_check (z:wire int) (h:heap) =
          (Map.equal z wire_ab /\
            proj_ok int z pA (Heap.sel h moderef) /\
            proj_ok int z pB (Heap.sel h moderef))
logic type ens_check (h0:heap) (b:bool) (h1:heap) = b==false

(* This is the main client of Wysteria *)
val is_A_richer_than_B : unit -> Wys bool
                                     (requires \m -> m==initial_mode)
                                     (ensures  \m0 res m1 -> res == false)
let is_A_richer_than_B _ =
  let x = with_mode par_A (mk_box 2) in
  let y = with_mode par_B (mk_box 3) in
  let z = concat_wires (mk_wire par_A x) (mk_wire par_B y) in
  let check : unit -> ST bool (req_check z) ens_check = fun () -> (* XXX TODO, should infer an ST type automatically *)
    project_wire z pA > project_wire z pB in
  with_mode sec_AB check
