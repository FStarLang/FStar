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
(* A refinement of type dynamic with 4 heap partitions                              *)
(* The heap model: heap is a (map (ref tagged_obj) tagged_obj)                      *)
(*                 tagged_obj is a triple (O 'P tag obj)                            *)
(*                 obj is a (map fn property)                                       *)
(*                 and tag in {Inv, Ref, Abs, Un}                                   *)
(* -------------------------------------------------------------------------------- *)
logic data type tag = Inv : tag | Ref : tag | Abs : tag | Stub : tag | Un : tag
type ProtoObj :: obj => E (* an object that has only its @proto field set *)
type TagAsE :: (obj => E) => tag => E
type OEAsE  :: (obj => E) => E
type InObj :: obj => fn => E

(* objects are tagged with their heap compartment and an invariant *)
logic data type tagged_obj = 
  | TO : 'P::(obj => E) 
    -> t:tag
    -> o:obj{(t=Inv ==> ('P o || ProtoObj o)) && (t=Ref ==> (InObj o "ref" && 'P o))}
    -> v:tagged_obj{EqTyp (AsE v) (TagAsE 'P t)}

(* loc: just a reference to tagged objects *)
logic data type loc = 
  | TL : 'P::(obj => E)
    -> t:tag 
    -> ref (v:tagged_obj{EqTyp (AsE v) (TagAsE 'P t)}) 
    -> v:loc{EqTyp (AsE v) (TagAsE 'P t)}

logic data type dyn = 
  | Undef : d:dyn{EqTyp (AsE d) undef}
  | Null  : d:dyn{EqTyp (AsE d) nul}
  | Bool  : bool -> d:dyn{EqTyp (AsE d) bool}
  | Num   : float -> d:dyn{EqTyp (AsE d) float}
  | Str   : string -> d:dyn{EqTyp (AsE d) string}
  | Obj   : t:loc 
         -> d:dyn{EqTyp (AsE d) (AsE t)}
  | Fun   : 'Tx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E)
         -> o:dyn{Obj_is o && ((Un = TL_proj_1 (Obj_proj_0 o)) ==> EqTyp (TxAsE un2un) (TxAsE 'Tx))}
         -> (this:dyn -> args:dyn -> iDST dyn ('Tx o args this)) 
         -> d:dyn{EqTyp (AsE d) (TxAsE 'Tx)}

(* property: the contents of an object's fields *)
and property = 
  | Data      : d:dyn -> p:property{EqTyp (AsE p) (AsE d)}
  | Accessor  : getter:dyn{(EqTyp (AsE getter) (TxAsE un2un)) && Fun_is getter}
             -> setter:dyn{(EqTyp (AsE setter) (TxAsE un2un)) && Fun_is setter}
             -> property 

(* abstract predicates, to be instantiated below *)
and IsUn :: dyn => E (* an untrusted dyn value *)
and un2un :: _ =  (* an un -> un function *)
   fun (o:dyn) (args:dyn) (this:dyn) ('Post::result dyn => heap => E) (h:heap) =>
               (IsUn args 
                && forall (r:result dyn) (h':heap). (ResultIs r IsUn) ==> 'Post r h')
(* and some type-level coercions to make up for the absence of kind polymorphism *)
and TxAsE  :: (dyn => dyn => dyn => (result dyn => heap => E) => heap => E) => E

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

(* A distinguishing object.prototype, under control of the adversary *)
val obj_proto : dyn
assume Obj_proto_un: IsUn obj_proto

(* An admissibility condition for object invariants, 
   i.e., they should be stable w.r.t. internal properties *)
type Admissible :: _ = (fun ('P::obj => E) =>
    (forall (o:obj) (c:property). ('P o || ProtoObj o)
     ==> ('P (ConsObj o "callee" c) && 'P (ConsObj o "@proto" c))))
    
(* -------------------------------------------------------------------------------- *)    
(* Some convenient type and value abbreviations *)
(* -------------------------------------------------------------------------------- *)    
type TruePred :: _ = (fun (o:obj) => True)

(* A (dfun 'Tx) is a type abbreviation for primitive JS function *)
type dfun ('Tx::dyn => dyn => (result dyn => heap => E) => heap => E) =
    this:dyn -> args:dyn -> iDST dyn ('Tx args this)

(* (tloc 'P t) is a t-tagged location with 'P invariant *)
type tobj :: _ = fun ('P::obj => E) (t:tag) => (v:tagged_obj{EqTyp (AsE v) (TagAsE 'P t)})

type tloc :: _ = fun ('P::obj=>E) (t:tag) => (r:loc{TL_is r 
                                                    && EqTyp (AsE r) (TagAsE 'P t)
                                                    && EqTyp (OEAsE (TL_proj_0 r)) (OEAsE 'P)
                                                    && TL_proj_1 r=t})

(* (pre_lobj l) is the type of the referent of a l:loc *)
type pre_lobj :: _ = fun (l:loc) => (o:tagged_obj{EqTyp (AsE o) (TagAsE (TL_proj_0 l) (TL_proj_1 l))})

(* (lobj l) is a further refined (pre_lobj l) (additional equalities) *)
type lobj :: _ = fun (l:loc) => (o:tagged_obj{TO_is o 
                                              && EqTyp (AsE o) (TagAsE (TL_proj_0 l) (TL_proj_1 l)) 
                                              && EqTyp (OEAsE (TL_proj_0 l)) (OEAsE (TO_proj_0 o))
                                              && TL_proj_1 l = TO_proj_1 o})

(* Projecting a location from an object or function *)
logic val GetLoc : dyn -> loc
assume GetLoc_Obj_def: forall l. (Obj_is l) ==> GetLoc l = Obj_proj_0 l
assume GetLoc_Fun_def: forall l. (Fun_is l && Obj_is (Fun_proj_1 l)) ==> GetLoc l = (Obj_proj_0 (Fun_proj_1 l))

(* Projecting a reference from a loc *)
logic val LocRef : l:loc -> ref (v:tagged_obj{EqTyp (AsE v) (TagAsE (TL_proj_0 l) (TL_proj_1 l))})
define LocRef_def: forall l. LocRef l = TL_proj_2 l

(* Projecting a tag from a (loc) object *)
logic val LocTag : dyn -> tag
define LocTag_def: forall (d:dyn). LocTag d = TL_proj_1 (GetLoc d)

(* -------------------------------------------------------------------------------- *)
(* Derived forms *)
(* -------------------------------------------------------------------------------- *)
logic val SelHeapObj : heap -> dyn -> obj
define SelHeapObj_def:forall h l. SelHeapObj h l = TO_proj_2 (SelHeap<pre_lobj (GetLoc l)> h (LocRef (GetLoc l)))

logic val SelectProperty : heap -> dyn -> fn -> property
assume SelectProperty_def1:forall h l f.{:pattern (SelectProperty h l f)} InObj (SelHeapObj h l) f 
        ==> (SelectProperty h l f = AssocObj (SelHeapObj h l) f)
assume SelectProperty_def2:forall h l f.{:pattern (SelectProperty h l f)} not (InObj (SelHeapObj h l) f)
        ==> (SelectProperty h l f = Data Undef)

logic val AssocObjVal : obj -> fn -> dyn
define AssocObjVal_def:forall o f. AssocObjVal o f = (Data_proj_0 (AssocObj o f))

logic val SelectField : heap -> dyn -> fn -> dyn
define SelectField_def:forall h l f. SelectField h l f = AssocObjVal (SelHeapObj h l) f

(* Abbreviations for predicates on the tag of an object *)
type Tagged :: _ = fun (d:dyn) (t:tag) => ((Obj_is d || Fun_is d) && LocTag d = t)
type IsSet :: _ = fun (h:heap) (o:dyn) => (InObj (SelHeapObj h o) "@set")
type ObjTagged :: _ = fun (o:dyn) (h:heap) (t:tag) => (t=TO_proj_1 (SelHeap<pre_lobj (GetLoc o)> h (LocRef (GetLoc o))))
type TaggedAndSet :: _ = fun (o:dyn) (t:tag) (h:heap) => (IsSet h o && (* ObjTagged o h t && *) Tagged o t)
type ITagged :: _ = fun (d:dyn) ('I::obj => E) (t:tag) => (Obj_is d 
                                                           && (t=TL_proj_1 (Obj_proj_0 d)) 
                                                           && (EqTyp (OEAsE (TL_proj_0 (Obj_proj_0 d))) (OEAsE 'I))
                                                           && (EqTyp (AsE d) (TagAsE 'I t)))

logic val UpdateAbsUnStubField : heap -> l:dyn{Tagged l Abs || Tagged l Un || Tagged l Stub} -> fn -> property -> heap 
define UpdateAbsUnStubField_def: forall (h:heap) (l:(l:dyn{Tagged l Abs || Tagged l Un})) (f:fn) (v:property). 
        (UpdateAbsUnStubField h l f v = 
            (UpdHeap h 
               (LocRef (GetLoc l)) 
               (TO<TL_proj_0 (GetLoc l)>
                  (TL_proj_1 (GetLoc l))
                  (ConsObj (SelHeapObj h l) f v))))

logic val UpdateInvCallee: heap -> l:dyn{Tagged l Inv} -> property -> heap
define UpdateInvCallee_def: forall (h:heap) (l:(l:dyn{Tagged l Inv
                                                      && SPEC_ONLY (False)
                                                      (* && SPEC_ONLY (Admissible (TL_proj_0 (GetLoc l))) *)
                                                      && SPEC_ONLY (TL_proj_0 (GetLoc l) (SelHeapObj h l))})) (p:property).
        (Eq (UpdateInvCallee h l p)
            (UpdHeap h (LocRef (GetLoc l))
               (TO<TL_proj_0 (GetLoc l)> (TL_proj_1 (GetLoc l)) (ConsObj (SelHeapObj h l) "callee" p))))
        
logic val ArgCell : 'T::(obj => E) -> d:dyn{'T (ConsObj NilObj "0" (Data d))} -> tagged_obj
define ArgCell_d1ef: forall ('T::obj => E) (d:(d:dyn{SPEC_ONLY ('T (ConsObj NilObj "0" (Data d)))})). 
        Eq (ArgCell<'T> d) (TO<'T> Inv (ConsObj NilObj "0" (Data d)))

logic val RefCellProto : 'T::(obj => E) -> proto:obj{ProtoObj proto} -> d:dyn{'T (ConsObj proto  "ref" (Data d))} -> tagged_obj
define RefCellProto_def:forall ('T::obj => E) (proto:(o:obj{ProtoObj o})) (d:(d:dyn{SPEC_ONLY ('T (ConsObj proto "ref" (Data d)))})). 
        Eq (RefCellProto<'T> proto d) (TO<'T> Ref (ConsObj proto "ref" (Data d)))

logic val SetRef: 'T::(obj => E) -> h:heap -> l:dyn -> v:dyn{forall o. 'T (ConsObj o "ref" (Data v))} -> tagged_obj
define SetRef_def: forall ('T::obj=>E) h l v. Eq (SetRef<'T> h l v) (TO<'T> Ref (ConsObj (SelHeapObj h l) "ref" (Data v)))

(* -------------------------------------------------------------------------------- *)
(* Defining ProtoObj *)        
(* -------------------------------------------------------------------------------- *)
assume ProtoObj_def: forall p.{:pattern  (ProtoObj (ConsObj NilObj "@proto" p))} ProtoObj (ConsObj NilObj "@proto" p)
assume ProtoObj_inv: forall p.{:pattern (ProtoObj p)} ProtoObj p ==> (exists q. p = (ConsObj NilObj "@proto" q))
type ProtoTObj :: _ = fun (o:tagged_obj) => (ProtoObj (TO_proj_2 o))
type IsInternalField :: _ = fun (f:fn) => 
    (f="@proto" || f="@code" || f="@toString" || f="@class" || f="@set" || f="@declassified")

type IsFreshFunObj :: _ = fun (o:dyn) (h:heap) =>
    (forall f. InObj (SelHeapObj h o) f
      ==> (IsInternalField f || f="prototype" || f="constructor"))

(* Useful for generating patterns *)
assume SelHeapObj_typing: forall h l.{:pattern (TypeOf (SelHeapObj h l))} EqTyp (TypeOf (SelHeapObj h l)) obj 

(* -------------------------------------------------------------------------------- *)
(* Stubs and declassified stubs *)
(* -------------------------------------------------------------------------------- *)
type Declassified :: property => E

type CleanStub :: _ = fun (l:dyn) (h:heap) => 
    (Tagged l Stub
     && (forall o f p. ((o=SelHeapObj h l)
                        && InObj o f 
                        && p=SelectField h l f)
         ==> (IsInternalField f || p=Undef)))

type DeclassifiedStub :: _ = fun (l:dyn) (h:heap) => 
    (CleanStub l h
     && Declassified (Data l)
     && (Eq (SelectField h l "@declassified") (Bool true)))

(* ------------------------------- Heap invariants -----------------------------------
 *    Note, we split the invariant into introduction and elimination forms of the 
 *    invariant. This is to facilitate automated proving by Z3. 
 *
 *    So, rather than use a bidirectional implication to define (HeapInv h), we
 *    use several implications of the form (P1 h => HeapInv h), (P2 h => HeapInv h), ...
 *    to introduce the invariant, and set it up so that the invariant is inductive.
 *
 *    To make use of the invariant, rather than providing a global assumption 
 *    (HeapInv h) ==> (P1 h) || (P2 h) || ..., which causes Z3 to become much 
 *    more inefficient, we provide a function, elimHeapInvariant, which eliminates the 
 *    HeapInv in a particular scope. 
 ------------------------------------------------------------------------------------ *)

(* -------------------- Definition of Un, i.e., untrusted values -------------------- *)
assume Un_def: forall (x:dyn).{:pattern (IsUn x)}
    IsUn x <=>  ((EqTyp (AsE x) bool) 
                  || (EqTyp (AsE x) undef) 
                  || (EqTyp (AsE x) string)
                  || (EqTyp (AsE x) int)
                  || (Un = LocTag x)
                  || (Stub = LocTag x && Declassified (Data x)))

(* ------------------------ (Intro) Invariant on the Un Heap ------------------------ *)
type IsUnProperty :: _ = fun (p:property) =>
    ((Data_is p && IsUn (Data_proj_0 p))
     || (Accessor_is p && Tagged (Accessor_proj_0 p) Un && Tagged (Accessor_proj_1 p) Un))

(* Every field in an (IsUnObj o) has an (IsUnProperty p) *)
type IsUnObj :: obj => E 
assume IsUnObj_proto: forall o. ProtoObj o ==> IsUnObj o 
assume IsUnObj_emp: IsUnObj NilObj
assume IsUnObj_upd: forall o f p. (IsUnObj o && IsUnProperty p) ==> IsUnObj (ConsObj o f p)
assume Heap_invariant_un: forall h x o. (HeapInv h 
                                         && (TO_proj_1 o=Un) 
                                         && IsUnObj (TO_proj_2 o))
                      ==> HeapInv (UpdHeap h x o)

(* --------------------------- (Intro) Invariant on the Abs heap -------------------- *)
assume Heap_invariant_abs: forall h x o.  (* anything goes in the Abs heap *)
                     (HeapInv h && (TO_proj_1 o=Abs)) 
                  ==> HeapInv (UpdHeap h x o)

(* --------------------------- (Intro) Invariant on the Stub heap -------------------- *)
assume Heap_invariant_stub: forall h (o:(o:dyn{Tagged o Stub})) f v.  
                     (HeapInv h && (Tagged o Stub) && (IsFreshFunObj o h || IsUnProperty v))
                  ==> HeapInv (UpdateAbsUnStubField h o f v)

assume Heap_invariant_stub_new: forall h x o.
                     (HeapInv h && (TO_proj_1 o = Stub) && (ProtoTObj o))
                  ==> HeapInv (UpdHeap h x o)

(* --------------------------- (Intro) Invariant on the Inv heap -------------------- *)
(* All Inv/Ref fields reachable from an Inv/Ref object (except callee)
   are tagged and set *)
type ReachableFieldOK :: _ = fun (f:dyn) (h:heap) => 
    ((Tagged f Inv ==> IsSet h f) && (Tagged f Ref ==> IsSet h f))
type ReachableOK :: obj => heap => E
assume ReachableOK_def: forall (flds:obj) (h:heap). 
     (ReachableOK flds h ==>
        (forall (f:fn). (InObj flds f 
                         && (f <> "callee") 
                         && not (IsInternalField f))
         ==> (Data_is (AssocObj flds f) && ReachableFieldOK (AssocObjVal flds f) h)))
assume ReachableOK_cons: forall (flds:obj) (h:heap) (f:fn) (p:property). 
    (ReachableOK flds h 
     && (IsInternalField f || (f="callee") || (Data_is p && ReachableFieldOK (Data_proj_0 p) h)))
    ==> ReachableOK (ConsObj flds f p) h
assume ReachableOK_emp: forall (h:heap). ReachableOK NilObj h

assume Heap_invariant_inv: forall h x o. (HeapInv h 
                                          && (TO_proj_1 o=Inv) 
                                          && ReachableOK (TO_proj_2 o) h)
                      ==> HeapInv (UpdHeap h x o)

(* --------------------------- (Intro) Invariant on the Ref heap -------------------- *)
assume Heap_invariant_ref: forall h x o. (HeapInv h 
                                          && (TO_proj_1 o=Ref) 
                                          && ReachableOK (TO_proj_2 o) h)
                      ==> HeapInv (UpdHeap h x o)

(* ------------------------------ Eliminating HeapInv ------------------------------- *)
type ElimUnObj :: _ = fun (o:obj) => 
    (IsUnObj o && (forall f.{:pattern (AssocObj o f)} IsUnProperty (AssocObj o f)))
type ElimHeapInv :: _ = fun (h:heap) => 
    ((forall x.{:pattern (LocRef (GetLoc x))} (ObjTagged x h Un || (ObjTagged x h Stub && Declassified (Data x))) ==> ElimUnObj (SelHeapObj h x))
     && (forall x.{:pattern (LocRef (GetLoc x))} (TaggedAndSet x Inv h && ObjTagged x h Inv) ==> ReachableOK (SelHeapObj h x) h)
     && (forall x.{:pattern (LocRef (GetLoc x))} (Tagged x Ref && ObjTagged x h Ref) ==> ReachableOK (SelHeapObj h x) h))
val elimHeapInv: unit -> iDST unit (fun ('Post::result unit => heap => E) (h:heap) => 
    (ElimHeapInv h ==> 'Post (V ()) h))

(* ------------------------------- DeltaHeap -----------------------------------
 *    Unlike HeapInv, we provide global definitions of both the intro and elim 
 *    forms for DeltaHeap. Z3 does just fine with this, although one lemma is useful.
 *
 *    (DeltaHeap h0 h1) states that all Inv locations that have been set in h0
 *    have the same value in h1 (except, perhaps, for their internal/callee fields)
 ------------------------------------------------------------------------------------ *)
assume Delta_heap_def: forall (h0:heap) (h1:heap).
  DeltaHeap h0 h1 <==> 
  (forall l f. (InHeap h0 (LocRef (GetLoc l))
                && TaggedAndSet l Inv h0
                && Eq Inv (TO_proj_1 (SelHeap<pre_lobj (GetLoc l)> h0 (LocRef (GetLoc l))))
                && InObj (SelHeapObj h0 l) f
                && not(IsInternalField f)
                && (f<>"callee"))
   ==> (SelectField h0 l f = SelectField h1 l f))

(* lemma *)
assume Delta_heap_def_hint: forall (h:heap) (l:dyn) (o:pre_lobj (GetLoc l)).
   ((Inv <> TO_proj_1 o)
    && (Eq (TO_proj_1 o) (TO_proj_1 (SelHeap<pre_lobj (GetLoc l)> h (LocRef (GetLoc l))))))
  ==> DeltaHeap h (UpdHeap h (LocRef (GetLoc l)) o)

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

private val __selectAbs__:
     l:dyn{Tagged l Abs}
  -> f:fn
  -> iDST property (fun ('Post::result property => heap => E) h =>
      ('Post (V (SelectProperty h l f)) h))
let __selectAbs__ l f = 
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some (TL 'P _ m) -> 
        match !m with 
          | TO 'Q _ flds -> 
              if inFields flds f
              then AssocObj flds f
              else Data Undef

private val __selectStub__:
     l:dyn{Tagged l Stub}
  -> f:fn
  -> iDST property (fun ('Post::result property => heap => E) h =>
      (IsFreshFunObj l h
       && (not(IsInternalField f))
       && (f <> "prototype")
       && (f <> "constructor")
       && (forall (x:property). 
             ((x=(SelectProperty h l f)) && IsUnProperty x)
           ==> 'Post (V x) h)))
let __selectStub__ l f = 
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some (TL 'P _ m) -> 
        match !m with 
          | TO 'Q _ flds -> 
              if inFields flds f
              then AssocObj flds f
              else Data Undef

private val __updateAbs__:
     caller:dyn 
  -> o:dyn{Tagged o Abs}
  -> f:fn
  -> v:property
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      ('Post (V Undef) (UpdateAbsUnStubField h o f v)))
let __updateAbs__ caller l f v =
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some (TL 'P _ l) -> 
        match !l with 
          | TO 'Q t flds -> 
              let _ = l := (TO<'Q> t (ConsObj flds f v)) in 
                Undef

private val __updateStub__:
     caller:dyn 
  -> o:dyn{Tagged o Stub}
  -> f:fn
  -> v:property
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      ((IsFreshFunObj o h || IsUnProperty v)
       && 'Post (V Undef) (UpdateAbsUnStubField h o f v)))
let __updateStub__ caller l f v =
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some (TL 'P _ l) -> 
        match !l with 
          | TO 'Q t flds -> 
              let _ = l := (TO<'Q> t (ConsObj flds f v)) in 
                Undef

private val __internalSelectUn__:
     l:dyn{Tagged l Un}
  -> f:fn
  -> iDST property (fun ('Post::result property => heap => E) h =>
      (forall (x:property). 
         ((x=(SelectProperty h l f)) 
          && IsUnProperty x)
       ==> 'Post (V x) h))
let __internalSelectUn__ l f = 
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some (TL 'P _ m) -> 
        match !m with 
          | TO 'Q _ flds -> 
              if inFields flds f 
              then 
                let _ = elimHeapInv () in 
                let x = AssocObj flds f in 
                  x
              else Data Undef

private val __internalUpdateUn__:
     o:dyn{Tagged o Un}
  -> f:fn
  -> v:property{IsUnProperty v}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      ((IsUnProperty v || (Data_is v && DeclassifiedStub (Data_proj_0 v) h && Declassified v))
       && 'Post (V Undef) (UpdateAbsUnStubField h o f v)))
let __internalUpdateUn__ o f v =
  match __getLocation__ o with
    | None -> unreachable ()
    | Some (TL 'P _ l) ->
        match !l with
          | TO 'Q _ flds ->
              let _ = elimHeapInv () in 
              let _ = l := (TO<'Q> Un (ConsObj flds f v)) in
                Undef
(* -------------------------------------------------------------------------------- *)
(* Abs partition *)
(* -------------------------------------------------------------------------------- *)
val allocAbs:
     unit
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (l:tloc TruePred Abs) (o:lobj l).  (not(InHeap h (LocRef l)) && ProtoTObj o)
       ==> 'Post (V (Obj l)) (UpdHeap h (LocRef l) o)))
let allocAbs (u:unit) = 
  let o = objUpd objNil "@proto" (Data obj_proto) in
  let o_tag : tobj TruePred Abs = TO<TruePred> Abs o in
  let x = ref<tobj TruePred Abs> o_tag in
  let loc = TL<TruePred> Abs x in 
    Obj loc

(* -------------------------------------------------------------------------------- *)
(* Inv partition *)
(* -------------------------------------------------------------------------------- *)
val allocInv: 'T::(obj => E)
  -> unit
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (Admissible 'T
       && (forall (l:tloc 'T Inv) (o:lobj l). (not(InHeap h (LocRef l)) && ProtoTObj o)
           ==> 'Post (V (Obj l)) (UpdHeap h (LocRef l) o))))
let allocInv ('T::obj => E) (u:unit) =
  let o = objUpd objNil "@proto" (Data obj_proto) in
  let o_tag : tobj 'T Inv = TO<'T> Inv o in
  let x = ref<tobj 'T Inv> o_tag in
  let loc = TL<'T> Inv x in
    Obj loc
  
val setInv: 'T::(obj => E)
  -> l:dyn
  -> flds:obj
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (ITagged l 'T Inv
       && ProtoObj (SelHeapObj h l)
       && ReachableOK flds h
       && InObj flds "@set"
       && (forall p. 'T (ConsObj flds "@proto" p))
       && (forall p. 'T (ConsObj flds "@callee" p))
       && (forall (o:lobj (GetLoc l)).
             (Eq (TO_proj_2 o) (ConsObj flds "@proto" (AssocObj (SelHeapObj h l) "@proto")))
           ==> 'Post (V Undef) (UpdHeap h (LocRef (GetLoc l)) o))))
let setInv ('T::obj => E) l flds =
  match l with
    | Obj t ->
        (match t with
           | TL 'T1 _ r ->
               match !r with
                 | TO 'T2 tt o ->
                     let proto = AssocObj o "@proto" in
                     let h0 = get () in 
                     let _ = assert_lemma<ReachableOK (ConsObj flds "@proto" proto) h0> () in 
                     let _ = r := (TO<'T1> Inv (ConsObj flds "@proto" proto)) in
                     let h1 = get () in 
                     let _ = assert_lemma<HeapInv h1> () in 
                       Undef)
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()
    | Fun 'Tx _ _ -> unreachable ()

val selectInv: 'T::(obj => E)
  -> l:dyn{ITagged l 'T Inv}
  -> f:fn
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (TaggedAndSet l Inv h
       && (forall flds. 'T flds ==> InObj flds f)
       && not (IsInternalField f)
       && (f <> "callee")
       && ('T (SelHeapObj h l)
           ==> 'Post (V (SelectField h l f)) h)))
let selectInv ('T::obj => E) l f =
  match l with
    | Obj t ->
        (match t with
           | TL 'T1 _ r ->
               match !r with
                 | TO 'T2 tt o -> 
                     let _ = elimHeapInv () in
                       (match AssocObj o f with 
                          | Data v -> v
                          | Accessor _ _ -> unreachable ()))
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()
    | Fun 'Tx _ _ -> unreachable ()

val updateInvCallee: 'T::(obj => E)
  -> l:dyn{ITagged l 'T Inv}
  -> f:fn
  -> v:dyn
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      ((f="callee")
       && TaggedAndSet l Inv h
       && Admissible 'T
       && 'Post (V Undef) (UpdateInvCallee h l (Data v))))
let updateInvCallee ('T::obj => E) l f v = 
  match l with 
    | Obj t ->
        (match t with
           | TL 'T1 _ r ->
               match !r with
                 | TO 'T2 tt o ->
                     let _ = elimHeapInv () in 
                     let _ = r := (TO<'T1> Inv (ConsObj o "callee" (Data v))) in
                       Undef)
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()
    | Fun 'Tx _ _ -> unreachable ()


(* -------------------------------------------------------------------------------- *)
(* Stub partition *)
(* -------------------------------------------------------------------------------- *)
val allocStub:
     unit
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (l:tloc TruePred Stub) (o:lobj l).  (not(InHeap h (LocRef l)) && ProtoTObj o)
       ==> 'Post (V (Obj l)) (UpdHeap h (LocRef l) o)))
let allocStub (u:unit) = 
  let o = objUpd objNil "@proto" (Data obj_proto) in
  let o_tag : tobj TruePred Stub = TO<TruePred> Stub o in
  let x = ref<tobj TruePred Stub> o_tag in
  let loc = TL<TruePred> Stub x in 
    Obj loc

val updateStub:
     caller:dyn
  -> o:dyn{Tagged o Stub}
  -> f:fn
  -> v:property{IsUnProperty v}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (InObj (SelHeapObj h o) f
       && Data_is (SelectProperty h o f)
       && 'Post (V Undef) (UpdateAbsUnStubField h o f v)))
let updateStub caller l f v =
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some (TL 'P _ l) -> 
        match !l with 
          | TO 'Q _ flds -> 
              match __selectField__ flds f with 
                | Some (Data _) -> 
                    let _ = l := (TO<'Q> Stub (ConsObj flds f v)) in 
                      Undef
                | Some (Accessor _ _) -> unreachable ()
                | None -> unreachable ()
    
val declassify:
     l:dyn{Tagged l Stub}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (CleanStub l h
       && (Declassified (Data l) ==> 'Post (V l) (UpdateAbsUnStubField h l "@declassified" (Data (Bool true))))))
let declassify l = 
  match __getLocation__ l with 
    | None -> unreachable ()
    | Some (TL 'P _ r) -> 
        match !r with 
          | TO 'Q _ flds -> 
              let _ = r := (TO<'Q> Stub (ConsObj flds "@declassified" (Data (Bool true)))) in 
              let _ = assume_lemma<Declassified (Data l)> () in
                l  
(* -------------------------------------------------------------------------------- *)
(* Function application *)
(* -------------------------------------------------------------------------------- *)
type RestoreCallerArgsTX :: _ = (fun (callee:(callee:dyn{Tagged callee Abs || Tagged callee Un || Tagged callee Stub})) 
                                   (caller0:property) (args0:property) 
                                   ('Post::result unit => heap => E)
                                   (h:heap) =>
    ('Post (V ()) 
       (UpdateAbsUnStubField  (* but finally reset its caller and args fields *)
          (UpdateAbsUnStubField h callee "caller" caller0)
          callee
          "arguments"
          args0)))

type MkRestoreCallerArgsTX :: _ = (fun (hbefore:heap) (callee:(callee:dyn{Tagged callee Abs || Tagged callee Un || Tagged callee Stub})) => 
    (RestoreCallerArgsTX callee 
       (SelectProperty hbefore callee "caller")
       (SelectProperty hbefore callee "arguments")))

type applyTX :: _ = fun (callee:(callee:dyn{Tagged callee Abs || Tagged callee Un || Tagged callee Stub})) (hbefore:heap) (this:dyn) (args:dyn)
  ('CalleeTx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E))
  ('Post::(result dyn => heap => E)) 
  (hpre:heap) =>
    (HeapInv hpre ==> 
       (TryFinally dyn 
          (WithInv dyn ('CalleeTx (Fun_proj_1 callee) args this))
          (MkRestoreCallerArgsTX hbefore callee) 
          'Post 
          hpre))
          
val applyAnyAbs: 'CalleeTx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E)
  -> 'T::(obj => E)
  -> caller:dyn  (* No restriction on caller when calling an abs function *)
  -> callee:dyn{Tagged callee Abs}
  -> this:dyn
  -> args:dyn{ITagged args 'T Inv}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (EqTyp (AsE callee) (TxAsE 'CalleeTx)
       && TaggedAndSet args Inv h
       && Admissible 'T
       && (applyTX callee h this args 'CalleeTx
             'Post 
             (UpdateInvCallee (* Wire up all the callee/caller stuff before the call *)
                (UpdateAbsUnStubField
                   (UpdateAbsUnStubField h callee "caller" (Data caller))
                   callee
                   "arguments"
                   (Data args))
                args
                (Data callee)))))
let applyAnyAbs
    ('CalleeTx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E))
    ('T::obj => E)
    caller (callee:(callee:dyn{Tagged callee Abs})) this args =
  match callee with
    | Fun 'Tx o f ->
        let hbefore : (h:heap{HeapInv h}) = witness () in
        let caller0 : (v:property{Eq v (SelectProperty hbefore callee "caller")})   = __selectAbs__ callee "caller" in
        let args0 : (v:property{Eq v (SelectProperty hbefore callee "arguments")})  = __selectAbs__ callee "arguments" in
        let restore: u:unit -> DST unit (MkRestoreCallerArgsTX hbefore callee) = 
          (fun (u:unit) -> 
             let h = get () in 
             let _ = assume_lemma<HeapInv h> () in 
             let _ = __updateAbs__ Undef callee "caller" caller0 in
             let _ = __updateAbs__ Undef callee "arguments" args0 in
               ()) in 
          try_finally
            (fun () ->
               let _ = __updateAbs__ Undef callee "caller" (Data caller) in
               let _ = __updateAbs__ Undef callee "arguments" (Data args) in
               let _ = updateInvCallee<'T> args "callee" callee in
                 f this args)
            restore
    | Obj (TL 'Q _ _) ->  unreachable ()
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()
    
private val call: 'Tx1::dyn => dyn => dyn => (result dyn => heap => E) => heap => E
  -> 'Tx2::dyn => dyn => dyn => (result dyn => heap => E) => heap => E
  -> o:dyn 
  -> a:dyn
  -> t:dyn 
  -> f:(this:dyn -> args:dyn -> iDST dyn ('Tx1 o args this))
  -> iDST dyn (fun ('Post::result dyn => heap => E) (h:heap) => 
      (EqTyp (TxAsE 'Tx1) (TxAsE 'Tx2)
       && 'Tx2 o a t 'Post h))
let call ('Tx1::dyn => dyn => dyn => (result dyn => heap => E) => heap => E)
         ('Tx2::dyn => dyn => dyn => (result dyn => heap => E) => heap => E)
         (o:dyn) (a:dyn) (t:dyn) (f:(this:dyn -> args:dyn -> iDST dyn ('Tx1 o args this))) = f t a

val applyUnUn:
     caller:dyn{IsUn caller}  (* Caller is Un, Callee in Un *)
  -> callee:dyn{Tagged callee Un}
  -> this:dyn{IsUn this}
  -> args:dyn{Tagged args Un}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h => forall o. un2un o args this 'Post h)
let applyUnUn caller (callee:(callee:dyn{Tagged callee Un})) this args =
  match callee with
    | Fun 'Tx o f ->
        let hbefore : (h:heap{HeapInv h}) = witness () in
        let caller0 : (v:property{IsUnProperty v && Eq v (SelectProperty hbefore callee "caller")}) =
          __internalSelectUn__ callee "caller" in
        let args0 : (v:property{IsUnProperty v && Eq v (SelectProperty hbefore callee "arguments")}) =
          __internalSelectUn__ callee "arguments" in
        let restore: u:unit -> DST unit (MkRestoreCallerArgsTX hbefore callee) = 
          (fun (u:unit) -> 
             let h = get () in 
             let _ = assume_lemma<HeapInv h> () in 
             let _ = __internalUpdateUn__ callee "caller" caller0 in
             let _ = __internalUpdateUn__ callee "arguments" args0 in
               ()) in 
          try_finally
            (fun () ->
               let _ = __internalUpdateUn__ callee "caller" (Data caller) in
               let _ = __internalUpdateUn__ callee "arguments" (Data args) in
               let _ = __internalUpdateUn__ args "callee" (Data callee) in
                 call<'Tx,un2un> o args this f)
            restore
    | _ ->  fatal_error ()


val applyAbsStub: 'CalleeTx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E)
  -> caller:dyn  (* No restriction on caller when calling a clean stub function *)
  -> callee:dyn{ITagged callee TruePred Stub}
  -> this:dyn{IsUn this}
  -> args:dyn{ITagged args TruePred Stub}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (EqTyp (AsE callee) (TxAsE 'CalleeTx)
       && IsFreshFunObj callee h
       && (not (InObj (SelHeapObj h callee) "@declassified"))
       && ProtoObj (SelHeapObj h args)
       && (not (Eq2 (LocRef (GetLoc callee)) (LocRef (GetLoc args))))
       && (applyTX callee h this args 'CalleeTx 'Post
             (UpdateAbsUnStubField (* Wire up all the callee/caller stuff before the call *)
                (UpdateAbsUnStubField
                   (UpdateAbsUnStubField h callee "caller" (Data caller))
                   callee
                   "arguments"
                   (Data args))
                args
                "callee"
                (Data callee)))))
let applyAbsStub
    ('CalleeTx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E))
    caller (callee:(callee:dyn{Tagged callee Stub})) this args =
  match callee with
    | Fun 'Tx o f ->
        let hbefore : (h:heap{HeapInv h}) = witness () in
        let caller0 : (v:property{IsUnProperty v && Eq v (SelectProperty hbefore callee "caller")})   =
          __selectStub__ callee "caller" in
        let args0 : (v:property{IsUnProperty v && Eq v (SelectProperty hbefore callee "arguments")})  = 
          __selectStub__ callee "arguments" in
        let restore: u:unit -> DST unit (MkRestoreCallerArgsTX hbefore callee) = 
          (fun (u:unit) -> 
             let h = get () in 
             let _ = assume_lemma<HeapInv h> () in 
             let _ = __updateStub__ Undef callee "caller" caller0 in
             let _ = __updateStub__ Undef callee "arguments" args0 in
               ()) in 
          try_finally
            (fun () ->
               let _ = __updateStub__ Undef callee "caller" (Data caller) in
               let _ = __updateStub__ Undef callee "arguments" (Data args) in
               let _ = __updateStub__ Undef args "callee" (Data callee) in
                 f this args)
            restore
    | Obj (TL 'Q _ _) ->  unreachable ()
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()

val applyStubUn:
     caller:dyn{Tagged caller Stub}  (* Caller is a declassified Stub, Callee in Un *)
  -> callee:dyn{Tagged callee Un}
  -> this:dyn{IsUn this}
  -> args:dyn{Tagged args Un}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (DeclassifiedStub caller h 
       && forall o. un2un o args this 'Post h))
let applyStubUn (caller:(caller:dyn{Tagged caller Stub})) (callee:(callee:dyn{Tagged callee Un})) this args =
  match callee with
    | Fun 'Tx o f ->
        let hbefore : (h:heap{HeapInv h}) = witness () in
        let caller0 : (v:property{IsUnProperty v && Eq v (SelectProperty hbefore callee "caller")}) =
          __internalSelectUn__ callee "caller" in
        let args0 : (v:property{IsUnProperty v && Eq v (SelectProperty hbefore callee "arguments")}) =
          __internalSelectUn__ callee "arguments" in
        let restore: u:unit -> DST unit (MkRestoreCallerArgsTX hbefore callee) = 
          (fun (u:unit) -> 
             let h = get () in 
             let _ = assume_lemma<HeapInv h> () in 
             let _ = __internalUpdateUn__ callee "caller" caller0 in
             let _ = __internalUpdateUn__ callee "arguments" args0 in
               ()) in 
          try_finally
            (fun () ->
               let _ = __internalUpdateUn__ callee "caller" (Data caller) in
               let _ = __internalUpdateUn__ callee "arguments" (Data args) in
               let _ = __internalUpdateUn__ args "callee" (Data callee) in
                 call<'Tx,un2un> o args this f)
            restore
    | Obj _ ->  fatal_error ()
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()


(* -------------------------------------------------------------------------------- *)
(* Un partition *)
(* -------------------------------------------------------------------------------- *)
val allocUn:
     unit
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (l:tloc TruePred Un) (o:lobj l). (not(InHeap h (LocRef l)) && ProtoTObj o)
       ==> 'Post (V (Obj l)) (UpdHeap h (LocRef l) o)))
let allocUn (u:unit) = 
  let o = objUpd objNil "@proto" (Data obj_proto) in 
  let o_tag : tobj TruePred Un = TO<TruePred> Un o in
  let x = ref<tobj TruePred Un> o_tag in
  let loc = TL<TruePred> Un x in 
    Obj loc
    
                         
(* Selecting or updating an Un object havocs the Un heap,
   may throw exception, etc. since it may trigger a getter/setter *)
private val __selectUn__:
     caller:dyn
  -> orig:dyn
  -> o:dyn
  -> f:string
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (IsUn o
       && IsUn orig
       && Tagged caller Un
       && forall (r:result dyn) (h':heap). ResultIs r IsUn ==> 'Post r h'))
let rec __selectUn__ caller orig o f =
  match __getLocation__ o with
    | None -> Undef
    | Some (TL 'P _ l) ->
        match !l with 
          | TO 'Q _ oo -> 
              let _ = elimHeapInv () in 
                (match __selectField__ oo f with
                   | Some (Data v) -> v (* IsUn v, from heap invariant *)
                   | Some (Accessor getter _) ->
                       let args = allocUn () in
                         applyUnUn caller getter orig args
                   | None ->
                       match __selectField__ oo "@proto" with  (* IsUn v, from heap invariant *)
                         | Some (Data v) ->
                             (* let _ = assert_lemma<IsUn v> () in *)
                             __selectUn__ caller orig v f
                         | _ -> Undef)
                  
val selectUn:
     caller:dyn
  -> o:dyn
  -> f:string
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (IsUn o
       && Tagged caller Un
       && forall (r:result dyn) (h':heap). ResultIs r IsUn ==> 'Post r h'))
let selectUn caller o f = __selectUn__ caller o o f

private val __setUnField__:
     o:dyn{IsUn o}
  -> f:fn
  -> v:dyn{IsUn v}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h => 
      ((forall h'. (Obj_is o || Fun_is o) ==> 'Post (V Undef) h')
       && ((not (Obj_is o) && not (Fun_is o)) ==> 'Post Err h)))
let __setUnField__ o f v = 
  match __getLocation__ o with 
    | Some (TL 'P tl l) -> 
        (match !l with 
           | TO 'Q tl' flds -> 
               let _ = elimHeapInv () in
               let _ = l := (TO<'Q> tl' (ConsObj flds f (Data v))) in
                 Undef)
    | None -> fatal_error ()
                     
private val __updateUn__:
     caller:dyn
  -> orig:dyn
  -> o:dyn
  -> f:string
  -> v:dyn
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (IsUn o
       && IsUn orig 
       && Tagged caller Un
       && IsUn v (* Can only store Un values in the Un heap *)
       && forall r h'. ResultIs r IsUn ==> 'Post r h'))
let rec __updateUn__ caller orig o f v =
  match __getLocation__ o with
    | None -> fatal_error ()
    | Some (TL 'P _ l) ->
        match !l with 
          | TO 'Q _ oo -> 
                (match __selectField__ oo f with
                   | Some (Data _) -> __setUnField__ orig f v
                   | Some (Accessor _ setter) -> 
                       let _ = elimHeapInv () in
                       let args = allocUn () in
                       let _ = __setUnField__ args "0" v in
                       let _ = assert_lemma<Tagged setter Un> () in 
                         applyUnUn caller setter orig args
                   | None -> 
                        match __selectField__ oo "@proto" with  (* IsUn v, from heap invariant *)
                         | Some (Data proto) ->
                             let _ = elimHeapInv () in
                               __updateUn__ caller orig proto f v
                         | _ -> __setUnField__ orig f v)

val updateUn:
     caller:dyn
  -> o:dyn
  -> f:string
  -> v:dyn
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (IsUn o
       && Tagged caller Un
       && IsUn v (* Can only store Un values in the Un heap *)
       && forall r h'. ResultIs r IsUn ==> 'Post r h'))
let updateUn caller o f v = __updateUn__ caller o o f v

(* -------------------------------------------------------------------------------- *)
(* Ref partition *)
(* -------------------------------------------------------------------------------- *)
val allocRef: 'T::(obj => E)
 -> init:dyn{forall (o:obj). 'T (ConsObj o "ref" (Data init))}
 -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
     (ReachableFieldOK init h
      && (forall (l:tloc 'T Ref) (o:lobj l). (not(InHeap h (LocRef l))
                                              && (exists (proto:(o':obj{ProtoObj o'})). Eq (RefCellProto<'T> proto init) o))
          ==> 'Post (V (Obj l)) (UpdHeap h (LocRef l) o))))
let allocRef ('T::obj => E) init = 
  let proto = objUpd objNil "@proto" (Data obj_proto) in
  let o = objUpd proto "ref" (Data init) in 
  let o_tag : tobj 'T Ref = TO<'T> Ref o in
  let x = ref<tobj 'T Ref> o_tag in
  let loc = TL<'T> Ref x in
    Obj loc
  
val updateRef: 'T::(obj => E)
  -> l:dyn{ITagged l 'T Ref}
  -> f:fn
  -> v:dyn{forall o. 'T (ConsObj o "ref" (Data v))}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (ReachableFieldOK v h
       && (f="ref")
       && TaggedAndSet l Ref h
       && 'Post (V Undef) (UpdHeap h (LocRef (GetLoc l)) (SetRef<'T> h l v))))
let updateRef ('T::obj => E) l f v = 
  match l with 
    | Obj t ->
        (match t with
           | TL 'T1 _ r ->
               match !r with
                 | TO 'T2 tt o ->
                     let h = get () in
                     let _ = assert_lemma<ObjTagged l h Ref> () in 
                     let _ = elimHeapInv () in (* use the invariant *)
                     let _ = assert_lemma<ReachableOK o h> () in 

                     let _ = r := (TO<'T1> Ref (ConsObj o "ref" (Data v))) in
                       Undef)
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()
    | Fun 'Tx _ _ -> unreachable ()
        
val selectRef: 'T::(obj => E)
  -> l:dyn{ITagged l 'T Ref}
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      ((forall r. ((r=(SelectField h l "ref"))
                      && 'T (SelHeapObj h l))
           ==> 'Post (V r) h)))
let selectRef ('T::obj => E) l =
  match l with
    | Obj t ->
        (match t with
           | TL 'T1 _ r ->
               match !r with
                 | TO 'T2 tt o -> 
                     let _ = elimHeapInv () in
                       match AssocObj o "ref" with 
                         | Data v -> v 
                         | Accessor _ _ -> unreachable ())
    | Undef ->  unreachable ()
    | Null ->   unreachable ()
    | Bool _ -> unreachable ()
    | Num _ ->  unreachable ()
    | Str _ ->  unreachable ()
    | Fun 'Tx _ _ -> unreachable ()
(* -------------------------------------------------------------------------------- *)
(* Function allocation *)
(* -------------------------------------------------------------------------------- *)
val mkFunAbs : 'Tx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E)
  -> s:string
  -> (o:dyn
      -> iDST (this:dyn -> args:dyn -> iDST dyn ('Tx o args this))
              (fun ('Post::result (dfun ('Tx o)) => heap => E) h =>
                  forall (x:dfun ('Tx o)). 'Post (V x) h))
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (o:(o:dyn{Obj_is o && Tagged o Abs})) (code:dfun ('Tx o)) (x:dyn) (h':heap) (flds:lobj (GetLoc o)).
         (not (InHeap h (LocRef (GetLoc o)))
          && (h' = (UpdHeap h (LocRef (GetLoc o)) flds))
          && IsFreshFunObj o h'
          && (x=(Fun<'Tx> o code))
          && EqTyp (AsE x) (TxAsE 'Tx)
          ==> 'Post (V x) h')))
let mkFunAbs 
    ('Tx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E)) 
    (s:string) 
    (mkF:(o:dyn
          -> iDST (this:dyn -> args:dyn -> iDST dyn ('Tx o args this))
           (fun ('Post::result (dfun ('Tx o)) => heap => E) h =>
               forall (x:dfun ('Tx o)). 'Post (V x) h))) =
  let o = allocAbs () in 
  let code = mkF o in 
  let x = Fun<'Tx> o code in 
    x


val mkFunStub : 'Tx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E)
  -> s:string
  -> (o:dyn
      -> iDST (this:dyn -> args:dyn -> iDST dyn ('Tx o args this))
              (fun ('Post::result (dfun ('Tx o)) => heap => E) h =>
                  forall (x:dfun ('Tx o)). 'Post (V x) h))
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (o:(o:dyn{Obj_is o && Tagged o Stub})) (code:dfun ('Tx o)) (x:dyn) (h':heap) (flds:lobj (GetLoc o)).
         (not (InHeap h (LocRef (GetLoc o)))
          && (h' = (UpdHeap h (LocRef (GetLoc o)) flds))
          && IsFreshFunObj o h'
          && (x=(Fun<'Tx> o code))
          && EqTyp (AsE x) (TxAsE 'Tx)
          ==> 'Post (V x) h')))
let mkFunStub
    ('Tx::(dyn => dyn => dyn => (result dyn => heap => E) => heap => E)) 
    (s:string) 
    (mkF:(o:dyn
          -> iDST (this:dyn -> args:dyn -> iDST dyn ('Tx o args this))
           (fun ('Post::result (dfun ('Tx o)) => heap => E) h =>
               forall (x:dfun ('Tx o)). 'Post (V x) h))) =
  let o = allocStub () in 
  let code = mkF o in 
  let x = Fun<'Tx> o code in 
    x
    

val mkFunUn : 
      s:string
  -> (o:dyn
      -> iDST (this:dyn -> args:dyn -> iDST dyn (un2un o args this))
             (fun ('Post::result (dfun (un2un o)) => heap => E) h =>
                 forall (x:dfun (un2un o)). 'Post (V x) h))
  -> iDST dyn (fun ('Post::result dyn => heap => E) h =>
      (forall (o:(o:dyn{Obj_is o && Tagged o Un})) (code:dfun (un2un o)) (x:dyn) (h':heap) (flds:lobj (GetLoc o)).
         (not(InHeap h (LocRef (GetLoc o)))
          && (h' = UpdHeap h (LocRef (GetLoc o)) flds)
          && (x=(Fun<un2un> o code))
          && EqTyp (AsE x) (TxAsE un2un)
          ==> 'Post (V x) h')))
let mkFunUn 
    (s:string) 
    (mkF:(o:dyn
          -> iDST (this:dyn -> args:dyn -> iDST dyn (un2un o args this))
           (fun ('Post::result (dfun (un2un o)) => heap => E) h =>
               forall (x:dfun (un2un o)). 'Post (V x) h))) =
  let o = allocUn () in 
  let code = mkF o in 
  let x = Fun<un2un> o code in 
    x
