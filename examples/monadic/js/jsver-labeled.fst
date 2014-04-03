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
#monadic(DST, returnTX, bindTX)
module JSVerify

type fn = string (* fieldname *)

(* Objects in JSExec are represented as a list (fn * property), 
   Modeled here using the Select/Update theory *)
logic array(AssocObj, ConsObj, NilObj, InObj) type obj (* = list (fn * property) *) 

(* -------------------------------------------------------------------------------- *)
(* A refinement of type dynamic                                                     *)
(* The heap model: heap is a (map (ref obj) obj)                                    *)
(*                 obj is a (map fn property)                                       *)
(* -------------------------------------------------------------------------------- *)
type ProtoObj :: obj => E (* an object that has only its @proto field set *)
type OEAsE  :: (obj => E) => E
type InObj :: obj => fn => E

(* loc: just a reference to an object *)
type loc = ref obj

logic data type dyn = 
  | Undef : d:dyn{EqTyp (AsE d) undef}
  | Null  : d:dyn{EqTyp (AsE d) nul}
  | Bool  : bool -> d:dyn{EqTyp (AsE d) bool}
  | Num   : float -> d:dyn{EqTyp (AsE d) float}
  | Str   : string -> d:dyn{EqTyp (AsE d) string}
  | Obj   : t:loc 
         -> d:dyn{EqTyp (AsE d) object}
  | Fun   : 'Tx::(dyn => dyn => (result dyn => heap => E) => heap => E)
         -> o:dyn{Obj_is o}
         -> (this:dyn -> args:dyn -> DST dyn ('Tx args this)) 
         -> d:dyn{EqTyp (AsE d) (TxAsE 'Tx)}

(* property: the contents of an object's fields *)
and property = 
  | Data      : d:dyn -> p:property{EqTyp (AsE p) (AsE d)}
  | Accessor  : getter:dyn{Fun_is getter}
             -> setter:dyn{Fun_is setter}
             -> property 

(* and some type-level coercions to make up for the absence of kind polymorphism *)
and TxAsE  :: (dyn => dyn => (result dyn => heap => E) => heap => E) => E

(* Three interpreted functions from the select/update theory for objects *)
logic val AssocObj : obj -> fn -> property
logic val ConsObj : obj -> fn -> property -> obj
logic val NilObj : obj 

(* Admitting correspondence between object maps and assoc lists *)
val inFields : o:obj -> f:fn -> b:bool{(b=true || b=false) && (b=true <==> InObj o f)}
(* let inFields = List.exists (fun (g,_) -> f=g) o *)
val objNil: o:obj{o=NilObj}
(* let objNil = [] *)
val objUpd: o:obj -> f:fn -> p:property -> o':obj{o' = ConsObj o f p}
(* let objUpd o f p = (f,p)::o *)

(* A distinguished object.prototype *)
val obj_proto : dyn
val global : loc
    
(* -------------------------------------------------------------------------------- *)    
(* Some convenient type and value abbreviations *)
(* -------------------------------------------------------------------------------- *)    
type TruePred :: _ = (fun (o:obj) => True)

(* A (dfun 'Tx) is a type abbreviation for primitive JS function *)
type dfun ('Tx::dyn => dyn => (result dyn => heap => E) => heap => E) =
    this:dyn -> args:dyn -> DST dyn ('Tx args this)

(* Projecting a location from an object or function *)
logic val GetLoc : dyn -> loc
assume GetLoc_Obj_def: forall l. (Obj_is l) ==> GetLoc l = Obj_proj_0 l
assume GetLoc_Fun_def: forall l. (Fun_is l && Obj_is (Fun_proj_1 l)) ==> GetLoc l = (Obj_proj_0 (Fun_proj_1 l))

(* -------------------------------------------------------------------------------- *)
(* Derived forms *)
(* -------------------------------------------------------------------------------- *)
logic val SelHeapObj : heap -> dyn -> obj
define SelHeapObj_def:forall h l. SelHeapObj h l = (SelHeap<obj> h (GetLoc l))

logic val SelectProperty : heap -> dyn -> fn -> property
assume SelectProperty_def1:forall h l f. InObj (SelHeapObj h l) f 
        ==> (SelectProperty h l f = AssocObj (SelHeapObj h l) f)
assume SelectProperty_def2:forall h l f. not (InObj (SelHeapObj h l) f)
        ==> (SelectProperty h l f = Data Undef)

logic val AssocObjVal : obj -> fn -> dyn
define AssocObjVal_def:forall o f. AssocObjVal o f = (Data_proj_0 (AssocObj o f))

logic val SelectField : heap -> dyn -> fn -> dyn
define SelectField_def:forall h l f. SelectField h l f = AssocObjVal (SelHeapObj h l) f

logic val UpdateField : heap -> dyn -> fn -> property -> heap 
define UpdateField_def: forall (h:heap) (l:dyn) (f:fn) (v:property). 
        UpdateField h l f v = UpdHeap h (GetLoc l) (ConsObj (SelHeapObj h l) f v)
        
logic val ArgCell : dyn -> obj
define ArgCell_def: forall (d:dyn). ArgCell d = (ConsObj NilObj "0" (Data d))

type HasDataField :: _ = fun (h:heap) (l:dyn) (f:fn) => 
    (InHeap h (GetLoc l) && InObj (SelHeapObj h l) f && Data_is (SelectProperty h l f))
(* -------------------------------------------------------------------------------- *)
(* Defining ProtoObj *)        
(* -------------------------------------------------------------------------------- *)
logic val emptyObj : obj
define emptyObj_def: emptyObj = (ConsObj NilObj "@proto" (Data obj_proto))
assume ProtoObj_def: forall p. ProtoObj (ConsObj NilObj "@proto" p)
assume ProtoObj_inv: forall p.{:pattern (ProtoObj p)} ProtoObj p ==> (exists q. p = (ConsObj NilObj "@proto" q))
type IsInternalField :: _ = fun (f:fn) => 
    (f="@proto" || f="@code" || f="@toString" || f="@class" || f="@set" || f="@declassified")

type IsFreshFunObj :: _ = fun (o:dyn) (h:heap) =>
    (forall f. InObj (SelHeapObj h o) f
      ==> (IsInternalField f || f="prototype" || f="constructor"))

(* Useful for generating patterns *)
assume SelHeapObj_typing: forall h l. EqTyp (TypeOf (SelHeapObj h l)) obj 

(* No invariants *)
assume HeapInv_saturate: forall h. HeapInv h
assume DeltaHeap_saturate: forall h1 h2. DeltaHeap h1 h2

(* -------------------------------------------------------------------------------- *)
(* Internal helper functions *)
(* -------------------------------------------------------------------------------- *)
private val __getLocation__:
     o:dyn
  -> DST (option loc) (fun ('Post::result (option loc) => heap => E) h =>
      (((Obj_is o || Fun_is o) ==> 'Post (V (Some (GetLoc o))) h)
       && ((not (Obj_is o) && not (Fun_is o)) ==> 'Post (V None) h)))
let __getLocation__ o = match o with
  | Obj l -> Some l
  | Fun 'Tx o _ ->
      (match o with
         | Obj l -> Some l
         | Undef ->  unreachable ()
         | Null ->   unreachable ()
         | Bool _ -> unreachable ()
         | Num _ ->  unreachable ()
         | Str _ ->  unreachable ()
         | Fun 'Tx1 _ _ -> unreachable ())
  | Undef ->  None
  | Null ->   None
  | Bool _ -> None
  | Num _ ->  None
  | Str _ ->  None

private val __selectField__:
     o:obj
  -> f:fn
  -> DST (option property) (fun ('Post::result (option property) => heap => E) h =>
      (forall (r:option property).
         ((InObj o f <==> (exists x. r = Some x))
          && (InObj o f ==> (r=Some (AssocObj o f))))
       ==> 'Post (V r) h))
let __selectField__ o f =
  if inFields o f 
  then let p = AssocObj o f in Some p
  else None

private val __select__:
     l:dyn{LBL "__select__ Obj_is or Fun_is" (Obj_is l || Fun_is l)}
  -> f:fn
  -> DST property (fun ('Post::result property => heap => E) h =>
      ('Post (V (SelectProperty h l f)) h))
let __select__ l f = 
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some m -> 
        let flds = !m in 
          if inFields flds f
          then AssocObj flds f
          else Data Undef

val __updateProperty__:
     caller:dyn 
  -> o:dyn{LBL "__updateProperty__ Obj_is or Fun_is" (Obj_is o || Fun_is o)}
  -> f:fn
  -> v:property
  -> DST dyn (fun ('Post::result dyn => heap => E) h =>
      ('Post (V Undef) (UpdateField h o f v)))
let __updateProperty__ caller l f v =
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some l -> 
        let flds = !l in 
        let _ = l := (ConsObj flds f v) in 
          Undef

(* -------------------------------------------------------------------------------- *)
(* Core JS* API *)
(* -------------------------------------------------------------------------------- *)
val alloc:
     unit
  -> DST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (l:loc) (o:obj).  (not(InHeap h l) && ProtoObj o)
       ==> 'Post (V (Obj l)) (UpdHeap h l o)))
let allocAbs (u:unit) = 
  let o = objUpd objNil "@proto" (Data obj_proto) in
  let loc = ref<obj> o in
    Obj loc

val newObj: dyn -> list dyn -> dyn

val update: 
     l:dyn{LBL "update Obj_is or Fun_is" (Obj_is l || Fun_is l)}
  -> f:fn
  -> v:dyn
  -> DST dyn (fun ('Post::result dyn => heap => E) h =>
      ('Post (V Undef) (UpdateField h l f (Data v))))
let update l f v = __updateProperty__ Undef l f (Data v)

val select: 
     l:dyn{LBL "select Obj_is or Fun_is" (Obj_is l || Fun_is l)}
  -> f:fn
  -> DST dyn (fun ('Post::result dyn => heap => E) h =>
      (LBL "select HasDataField" (HasDataField h l f)
       && 'Post (V (SelectField h l f)) h))
let select l f =
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some r -> 
        match __selectField__ (!r) f with
          | None -> unreachable ()
          | Some (Accessor _ _) -> unreachable ()
          | Some (Data v) -> v

type existsTx :: ((dyn => dyn => (result dyn => heap => E) => heap => E) => E) => E
val apply:  f:dyn
         -> this:dyn 
         -> args:dyn 
         -> DST dyn (fun ('Post::result dyn => heap => E) h => 
             (existsTx (fun ('Tx::(dyn => dyn => (result dyn => heap => E) => heap => E)) => 
                  (EqTyp (AsE f) (TxAsE 'Tx) && ('Tx args this 'Post h)))))


val apply_hint: 'Tx::(dyn => dyn => (result dyn => heap => E) => heap => E)
         -> f:dyn
         -> this:dyn 
         -> args:dyn 
         -> DST dyn (fun ('Post::result dyn => heap => E) h => 
             (LBL "apply EqTyp" (EqTyp (AsE f) (TxAsE 'Tx))
              && 'Tx args this 'Post h))

type Unname::(dyn => dyn => (result dyn => heap => E) => heap => E) => (dyn => dyn => (result dyn => heap => E) => heap => E)

val apply_hint_ex_witness': 
            'TxArg::(dyn => dyn => (result dyn => heap => E) => heap => E)
         -> 'ExTx::dyn => dyn => (result dyn => heap => E) => heap => (dyn => dyn => (result dyn => heap => E) => heap => E) => E
         -> 'TxWitness::(dyn => dyn => (result dyn => heap => E) => heap => E)
         -> f:dyn 
         -> this:dyn
         -> args:dyn 
         -> DST dyn (fun ('Post::result dyn => heap => E) (h:heap) => 
             (LBL "apply_hint_ex_witness EqTyp 1" (EqTyp (AsE f) (TxAsE 'TxArg))
              && LBL "apply_hint_ex_witness EqTyp 2" (EqTyp (TxAsE (Unname 'TxArg)) 
                                                            (TxAsE (fun args_ this_ ('Post_::result dyn => heap => E) h_ => (existsTx ('ExTx args_ this_ 'Post_ h_)))))
              && ('ExTx args this 'Post h 'TxWitness)))


val apply_hint_ex_witness: 
            'ExTx::dyn => dyn => (result dyn => heap => E) => heap => (dyn => dyn => (result dyn => heap => E) => heap => E) => E
         -> 'TxWitness::(dyn => dyn => (result dyn => heap => E) => heap => E)
         -> f:dyn 
         -> this:dyn
         -> args:dyn 
         -> DST dyn (fun ('Post::result dyn => heap => E) (h:heap) => 
             (EqTyp (AsE f) (TxAsE (fun args_ this_ ('Post_::result dyn => heap => E) h_ => (existsTx ('ExTx args_ this_ 'Post_ h_))))
              && ('ExTx args this 'Post h 'TxWitness)))

(* val apply_hint: 'Tx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E) *)
(*          -> f:dyn *)
(*          -> this:dyn  *)
(*          -> args:dyn  *)
(*          -> DST dyn (fun ('Post::result dyn => heap => E) h =>  *)
(*              (EqTyp (AsE f) (TxAsE 'Tx)  *)
(*               && (forall h'. (h'=UpdateField h args "callee" (Data f)) *)
(*                   ==> ('Tx (Fun_proj_1 f) args this 'Post h')))) *)

val mkFun: 'Tx::(dyn => dyn => (result dyn => heap => E) => heap => E)
  -> s:string
  -> code:(this:dyn -> args:dyn -> DST dyn ('Tx args this))
  -> DST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (o:(o:dyn{Obj_is o})) (x:dyn) (h':heap) (flds:obj).
         (not (InHeap h (GetLoc o))
          && (h' = (UpdHeap h (GetLoc o) flds))
          && IsFreshFunObj o h'
          && (x=(Fun<'Tx> o code))
          && EqTyp (AsE x) (TxAsE 'Tx)
          ==> 'Post (V x) h')))
let mkFun
    ('Tx::(dyn => dyn => (result dyn => heap => E) => heap => E)) 
    (s:string) 
    (code: (this:dyn -> args:dyn -> DST dyn ('Tx args this))) =
  let o = alloc () in 
  let x = Fun<'Tx> o code in 
    x

val _while:  'Inv :: heap => E
          -> 'TxGuard::unit => (result bool => heap => E) => heap => E
          -> 'TxBody::unit => (result dyn => heap => E) => heap => E
          -> (x:unit -> DST bool ('TxGuard x))
          -> (x:unit -> DST dyn ('TxBody x))
          -> DST dyn (fun ('Post::result dyn => heap => E) h => 
              (LBL "While Inv initial" ('Inv h)           
               && LBL "While Inv inductive" (forall h1. 'Inv h1 ==> ('TxGuard ()            
                                                                       (fun v h2 => 
                                                 (v=(V true) ==> ('TxBody () (fun (u:result dyn) => 'Inv) h2)) &&  
                                                 (v=(V false) ==> 'Inv h2)) h1))
               && LBL "While final" (forall h'. 'Inv h' ==> 'Post (V Undef) h'))) 

(* -------------------------------------------------------------------------------- *)
(* Coercions *)
(* -------------------------------------------------------------------------------- *)
type Falsy :: _ = fun (d:dyn) => 
    ((d=Undef) || (d=(Num 0.0)) || (d=Undef) || (d=(Str "")) || (d=(Bool false)))
type Truthy :: _ = (fun (d:dyn) => ((d=d) && not (Falsy d)))
type IsString :: _ = fun o => EqTyp (AsE o) string

val instOf: dyn -> dyn -> dyn
val inExp: dyn -> dyn -> dyn
val opAddition: dyn -> dyn -> dyn
val opToString: dyn -> dyn
val lt: dyn -> dyn -> dyn
val lteq: dyn -> dyn -> dyn
val gt: dyn -> dyn -> dyn
val gteq: dyn -> dyn -> dyn
val sub: dyn -> dyn -> dyn
val refEq: d1:dyn -> d2:dyn -> DST dyn (fun ('Post::result dyn => heap => E) h => 
                                        (forall (b:dyn). (((b=(Bool true)) <=> (d1=d2)) || (b=(Bool false)))
                                                      =>  'Post (V b) h))
val refEqBool: d1:dyn -> d2:dyn -> DST bool (fun ('Post::result bool => heap => E) h => 
                                              (forall (b:bool). (((b=true) <=> (d1=d2)) || (b=false))
                                                           =>  'Post (V b) h))

val absEq: d1:dyn -> d2:dyn -> DST dyn (fun ('Post::result dyn => heap => E) h => 
                                        (forall (b:dyn). (((b=(Bool true)) <=> (d1=d2)) || (b=(Bool false)))
                                                      =>  'Post (V b) h))
val absEqBool: d1:dyn -> d2:dyn -> DST bool (fun ('Post::result bool => heap => E) h => 
                                              (forall (b:bool). (((b=true) <=> (d1=d2)) || (b=false))
                                                           =>  'Post (V b) h))
val unStr: dyn -> string
val unInt: dyn -> int
val unBool: dyn -> bool
val unFloat: dyn -> float
val unObj: dyn -> obj
val unFun: dyn -> dyn -> dyn -> dyn (* has "this" *)

val coerceBool  : d:dyn -> DST bool (fun ('Post::result bool => heap => E) h => 
                                         (forall b. (((Falsy d) <=> (b=false)) && ((b=true) || (b=false)))
                                                  => 'Post (V b) h))
val dummyBool : dyn -> bool
val coerceInt   : dyn -> int
val coerceString: dyn -> string
val forin: dyn -> ('a -> dyn) -> dyn
val opDelete: dyn -> dyn -> unit

val checkField : d:dyn -> f:string -> DST dyn (fun ('Post::result dyn => heap => E) h => ((HasDataField h d f) && 'Post (V Undef) h))
val land       : x:dyn -> y:dyn -> z:bool { z=true => Truthy x && Truthy y }
val lor        : x:dyn -> y:dyn -> z:bool { z=false => Falsy x && Falsy y }

val negate     : x:bool -> DST bool (fun ('Post::result bool => heap => E) h => 
    (forall (y:bool). (y=true || y=false) && 
       ((y=true => x=false) && 
          (y=false => x=true)) => 'Post (V y) h))

val conj       : x:bool -> y:bool -> DST bool (fun ('Post::result bool => heap => E) h => 
    (forall (z:bool). ((z=true || z=false) && 
                         ((z=true <=> (x=true && y=true)) && 
                            (z=false <=> (x=false || y=false)))) => 'Post (V z) h))



