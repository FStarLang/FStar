(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(* This example is a quick sketch of how to code up linear maps in F*. 

   It differs from the example provided in the ICFP '11 paper
   primarily in its use of logic functions, which have since been
   added to F*. 
   
   Logic functions are uninterpreted function symbols, whose behavior
   is axiomatized using a first-order equational theory. F* (using Z3)
   uses the equational theory to rewrite terms that contain
   applications of these logic functions.
*)
module Lin 

(* An abstract type of references, ref 'a *)
type ref :: * => *

(* An abstract type for sets of memory locations (i.e., references) *)
type locations::*

(* The type locations is used in the axiomatization of linear maps.
   These sets are modeled using the term algebra defined by the
   four constructors below. *)
logic val Empty     : locations
logic val Singleton : ref 'a -> locations
logic val Union     : locations -> locations -> locations
logic val SetMinus  : locations -> locations -> locations

(* We define a function for set membership, according to the equations below. *)
logic val Mem : ref 'a -> locations -> bool
assume forall (r:ref 'a). (Mem r Empty) = false
assume forall (r:ref 'a). (Mem r (Singleton r)) = true
assume forall (l1:locations) (l2:locations) (r:ref 'a). Mem r (Union l1 l2) = ((Mem r l1) || (Mem r l2))
assume forall (l1:locations) (l2:locations) (r:ref 'a). Mem r (SetMinus l1 l2) = ((Mem r l1) && (not (Mem r l2)))

(* Abstract type of maps from ref 'a to 'a, together with a select/update theory *)
type heap :: *
logic val Select : ref 'a -> heap -> 'a
logic val Update : ref 'a -> 'a -> heap -> heap 
assume forall (h:heap) (x:ref 'a) (v:'a). (Select x (Update x v h)) = v
assume forall (h:heap) (x:ref 'a) (y:ref 'b) (v:'a). (not (Eq2 x y)) => (Select y (Update x v h)) = (Select y h)

(* A linear map is a map plus a set of locations *)
type lin :: A = {map:heap; domain:locations}

(* Making a new empty lin map *)
val newlin: unit -> m:lin{m.domain=Empty}

(* In the type below, EqA is the equality relation on affine values *)
val read: x:ref 'a -> m1:lin{(Mem x m1.domain)=true}
      -> (y:'a * (m2:lin{EqA m2 m1 && (y=(Select x m1.map))}))

val write: x:ref 'a -> y:'a -> m1:lin{(Mem x (m1.domain))=true}
       -> (u:unit * (m2:lin{(m2.domain=m1.domain) &&
                            (m2.map=(Update x y m1.map))}))

(* transfer, a function omitted in the short description in the ICFP '11 paper, 
   is a part of the linear maps formulation provided by Lahiri et al. in PLPV'11. 
   It serves to move a reference from one map to another. It is easily coded up 
   as shown below. *)
val transfer: m1:lin -> m2:lin -> x:ref 'a{(Mem x m1.domain)=true}
           -> (m1':lin * 
               m2':lin{(m1'.map=m1.map && 
                        m1'.domain=(SetMinus m1.domain (Singleton x)) &&
                        m2'.map=(Update x (Select x m1.map) m2.map) && 
                        m2'.domain=(Union m2.domain (Singleton x)))})
end

module Client
open Lin

(* Spec and implementation of a simple swap function.
   May be called with x1 and x2 aliased, or not *)
val swap :  x1:ref 'a 
         -> x2:ref 'a 
         -> m1:lin{(Mem x1 m1.domain)=true && (Mem x2 m1.domain)=true}
         -> (u:unit * (m2:lin{(m2.domain = m1.domain) &&
                              (m2.map = (Update x2 (Select x1 m1.map) (Update x1 (Select x2 m1.map) m1.map)))}))
let swap x1 x2 m1 =
  let y1, m1 = read x1 m1 in
  let y2, m1 = read x2 m1 in
  let _, m2 = write x1 y2 m1 in
  let _, m3 = write x2 y1 m2 in
    (), m3

end
