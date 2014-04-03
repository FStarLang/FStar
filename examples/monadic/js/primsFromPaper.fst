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
module Prims

type int :: *
type string :: *
type object
type loc
type heap

type undef :: *
logic type EqTyp :: E => E => E
logic type TypeOf ('a::*) :: 'a => E
type dyn = 
  | Int   : int -> d:dyn{EqTyp (TypeOf d) int}
  | Str   : string -> d:dyn{EqTyp (TypeOf d) string}
  | Obj   : loc -> d:dyn{EqTyp (TypeOf d) object}
  | Undef : d:dyn{EqTyp (TypeOf d) undef}
  | Fun   : 'TxF::dyn => dyn => (dyn => heap => E) => heap => E
         -> (this:dyn -> args:dyn -> PST dyn ('TxF args this))
         -> d:dyn{EqTyp (TypeOf d) (Function 'TxF)}
and Function :: (dyn => dyn => (dyn => heap => E) => heap => E) => E


type heapcell = Cell : 'a::E -> d:dyn{EqTyp (TypeOf d) 'a} -> heapcell
(* Selecting and updating all the fields of an object *) 
logic type fields                                  
logic val SelObj : heap -> dyn -> option fields     
logic val UpdObj : heap -> dyn -> fields -> heap   
logic val Emp : fields
(* Selecting a single field *)                     
type fn = string (* field names *)
logic val SelCell : heap -> dyn -> fn -> option heapcell
private val selcell : h:heap -> o:dyn{EqTyp (TypeOf o) object} -> f:fn 
       -> c: (option heapcell){c=(SelCell h o f)}
(* Updating a single field *)
logic val UpdCell : 'a::E -> heap -> dyn -> fn -> dyn -> heap

private val updcell : 'a::E -> h:heap -> o:dyn{EqTyp (TypeOf o) object} 
-> f:fn -> d:dyn{EqTyp (TypeOf d) 'a} -> h':heap{h'= (UpdCell h o f d)}


(* Derived constructs *)
(* Selecting the value in a heap cell *)
logic val Select : heap -> loc -> fn -> dyn
 
assume forall h l f v. (((SelCell h l f) = (Some (Cell v))) => ((Select h l f) = v))

assume forall h l f. (SelCell h l f=None) => (Select h l f = Undef)
(* Selecting the type in a heap cell *)
logic type SelectT :: heap => loc => fn => E
assume forall ('P::E) h l f . ((SelCell h l f) =(Some (Cell<'P> v))) => (EqTyp (SelectT h l f) 'P)
assume forall h l f. (SelCell h l f=None) => ((SelectT h l f) = undef)
(* Checking if a heap cell is allocated *)
type HasField = fun h l f => ((SelCell h l f)=(Some v))
(* Checking if an object is present in the heap *)
type InDom = fun h d => ((SelObj h d) <> None)
(* Allocating a new object *)
logic val New : heap -> dyn -> option fields -> heap 
assume forall h d f. not (InDom h d) => (New h d (Some f))=(UpdObj h d f)
val alloc: proto:dyn{EqTyp (TypeOf proto) object && InDom h proto}  
      -> h:heap -> (x:dyn * h':heap{h'=(New h d (SelectObj h proto))})


type SelTX :: _ = fun o f ('Post::dyn=>heap=>E) h =>                                 
(EqTyp (TypeOf o) object && (HasField h o f) &&               
 (EqTyp (TypeOf (Select h o f)) (SelectT h o f)  => 'Post (Select h o f) h))
val select: o:dyn -> f:fn -> PST dyn (SelTX o f)       

let select o f 'Post h = match o with 
| Undef -> assert False
| Str _ -> assert False
| Int _  -> assert False
| Fun _ -> assert False
| Obj _ -> (match (selcell h o f) with Some(Cell 'a v) -> v,h 
                                | None -> assert False)

type UpdTX :: _ = fun o f v ('Post::dyn=>heap=>E) h =>
 (EqTyp (TypeOf o) object && (InDom h o) &&                  
 'Post Undef (Update (TypeOf v) h o f v))            
val update: o:dyn -> f:fn -> v:dyn -> PST dyn (UpdTx o f v) 

let update o f v 'Post h = match v with 
| Undef -> (Undef, updcell undef h o f v)
| Str _ -> (Undef, updcell string h o f v)
| Int _ -> (Undef, updcell int h o f v)
| Obj _ -> (Undef, updcell obj h o f v)
| Fun 'Pre _ -> (Undef, updcell<(Function 'Pre)> h o f v)
logic type Unfun :: E=>dyn=>dyn=>(dyn=>heap=>E)=>heap=>E  
assume forall 'Tx. (EqTyp (Unfun (Function 'Tx)) 'Tx  )
assume forall ('a::E) ('Pre::dyn => dyn => (dyn => heap => E) => heap => E). 
  ((not (EqTyp 'a (Function 'Pre))) => (EqTyp (Unfun 'a) (fun args this ('Post::dyn=>heap=>E) h => False)))
val apply:  f:dyn -> this:dyn -> args:dyn -> PST dyn (Unfun (TypeOf f) args this) 

let apply f this args 'Post h = match f with 
| Undef -> assert False
| Str _ -> assert False
| Int _  -> assert False
| Obj _ -> assert False
| Fun 'Tx fn -> fn this args h

