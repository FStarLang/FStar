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
module JSPrims


type fieldname = string
type obj = ref int
type undef 

(*
  datatype object = Term term
                  | Object (Array fieldname Term)

  datatype heap = (Array Term (Pair object type) * 
                  Array Term (Array fieldname Bool))
*)

(*type fieldnameVt :: * = string * vt
and obj_fieldnameVt :: * = obj * list fieldnameVt*)

and heap :: * (* = list obj_fieldnameVt *) (*(obj * list(string * vt)) *)

and vt = MkVt : 'a::E -> d:dyn{EqTyp (GetType d) 'a} -> vt

and ST :: _ =
         (fun ('Pre::heap => E) ('a::*) ('Post::'a => heap => E) => h:heap{'Pre h} -> (x:'a * (h':heap{'Post x h'})))

and PST :: _ = fun ('a::*) ('Tx::('a => heap => E) => heap => E) => ('Post::('a => heap => E) -> ST ('Tx 'Post) 'a 'Post)

and dyn = 
  | Null : dyn

  | Undef : d:dyn{EqTyp (GetType d) undef}

  | Str   : string -> d:dyn{EqTyp (GetType d) string}

  | Int   : int -> d:dyn{EqTyp (GetType d) int}

  | Float : float -> d:dyn{EqTyp (GetType d) float}

  | Bool  : bool -> d:dyn{EqTyp (GetType d) bool}

  | Obj   : obj -> d:dyn{EqTyp (GetType d) object}

  | Fun   : 'Pre::(dyn => dyn => (dyn => heap => E) => heap => E)
         -> (this:dyn -> args:dyn -> PST dyn ('Pre args this))
         -> d:dyn{EqTyp (GetType d) (Function 'Pre)}

  | Return : d:dyn -> d':dyn{EqTyp (GetType d) (GetType d')}

  | Break  : dyn

and Function :: (dyn => dyn => (dyn => heap => E) => heap => E) => *

and GetType :: dyn => *

type returnTX :: _ = 
    fun ('a::*) (x:'a) ('Post:: 'a => heap => E) => 'Post (x)

type bindTX :: _ = 
    fun ('a::*) ('b::*) 
      ('Tx1::('a => heap => E) => heap => E)
      ('Tx2::'a => ('b => heap => E) => heap => E)
      ('Post::'b => heap => E) => 
      ('Tx1 (fun (x:'a) (h:heap) =>
           (* (forall (e:exn). (x=E e) ==> 'Post (E e) h) &&  *)
           (* ((x=Err) ==> 'Post Err h) &&                    *)
           (forall (v:'a). (x= v) ==> 'Tx2 v 'Post h)))  (* Tx1 returns normally *)


val global : obj

val mkInt : i:int -> d:dyn{(EqTyp (GetType d) int) && (d=(Int i))}

val bind_st : 'Pre::(heap => E) 
           -> 'a::* 
           -> 'Post1::('a => heap => E) 
           -> 'b::* 
           -> 'Post::('b => heap => E) 
           -> ST 'Pre 'a 'Post1
           -> (x:'a -> ST ('Post1 x) 'b 'Post)
           -> ST 'Pre 'b 'Post
let bind_st c1 c2 = fun heap ->
  let x, heap' = c1 heap in
    c2 x heap'

val return_refined_st : 'a::*
             -> 'R::('a => E)
             -> 'Post::('a => heap => E)
             -> x:'a{'R x}
             -> ST (fun (h:heap) => ((Forall 'a (fun x => (('R x) => ('Post x h)))))) 'a 'Post
(* let return_refined_st x = fun h -> (x, h) *)

val return_st : 'a::*
             -> 'Post::('a => heap => E)
             -> x:'a
             -> ST ('Post x) 'a 'Post
(* let return_st x = fun h -> (x, h) *)

(*********** ported from jsprelude.fst *)

type map = list (string * vt)
val mkMap : list (string * dyn) -> map 

val newObj: dyn -> list dyn -> dyn
val instOf: dyn -> dyn -> dyn
val inExp: dyn -> dyn -> dyn
val opAddition: dyn -> dyn -> dyn
val opToString: dyn -> dyn
val lt: dyn -> dyn -> dyn
val lteq: dyn -> dyn -> dyn
val gt: dyn -> dyn -> dyn
val gteq: dyn -> dyn -> dyn
val sub: dyn -> dyn -> dyn
type IsFalse :: _ = (fun (d:dyn) => 
    ((d=Undef) || (d=(Int 0)) || (d=Undef) || (d=(Str "")) || (d=(Bool false))))
type IsTrue :: _ = (fun (d:dyn) => ((d=d) && not (IsFalse d)))

val refEq: d1:dyn -> d2:dyn -> PST dyn (fun ('Post::dyn => heap => E) h => 
                                        (forall (b:dyn). (((b=(Bool true)) <=> (d1=d2)) || (b=(Bool false)))
                                                      =>  'Post b h))
val refEqBool: d1:dyn -> d2:dyn -> PST bool (fun ('Post::bool => heap => E) h => 
                                              (forall (b:bool). (((b=true) <=> (d1=d2)) || (b=false))
                                                           =>  'Post b h))

(*
 * TODO right now this is just a copy of refEq. Needs to be changed for proper
 * semantics of abstract equality.
 *)
val absEq: d1:dyn -> d2:dyn -> PST dyn (fun ('Post::dyn => heap => E) h => 
                                        (forall (b:dyn). (((b=(Bool true)) <=> (d1=d2)) || (b=(Bool false)))
                                                      =>  'Post b h))
val absEqBool: d1:dyn -> d2:dyn -> PST bool (fun ('Post::bool => heap => E) h => 
                                              (forall (b:bool). (((b=true) <=> (d1=d2)) || (b=false))
                                                           =>  'Post b h))

val unStr: dyn -> string
val unInt: dyn -> int
val unBool: dyn -> bool
val unFloat: dyn -> float
val unObj: dyn -> obj
val unFun: dyn -> dyn -> dyn -> dyn (* has "this" *)

(* val coerceBool  : d:dyn -> b:bool{((IsFalse d) <=> (b=false)) && ((b=true) || (b=false))} *)
val coerceBool  : d:dyn -> PST bool (fun ('Post::bool => heap => E) h => 
                                         (forall b. (((IsFalse d) <=> (b=false)) && ((b=true) || (b=false)))
                                                  => 'Post b h))
val dummyBool : dyn -> bool
val coerceInt   : dyn -> int
val coerceString: dyn -> string

val res2dyn : dyn -> dyn
let res2dyn = function 
  | Return d -> d
  | Break -> Undef
  | x -> x

val seq : dyn -> (unit -> dyn) -> dyn
let seq x y = match x with
  | Return _ -> x
  | Break -> Undef
  | _ -> y ()

(* type InvGlobal :: _ =  (fun h h' => (SelectObj h' global) = (SelectObj h global)) *)

val get: unit -> PST heap (fun ('Post::heap => heap => E) h => 'Post h h)
val _while:  'Inv :: heap => E
          -> 'TxGuard::unit => (bool => heap => E) => heap => E
          -> 'TxBody::unit => (dyn => heap => E) => heap => E
          -> (x:unit -> PST bool ('TxGuard x))
          -> (x:unit -> PST dyn ('TxBody x))
          -> PST dyn (fun ('Post::dyn => heap => E) h => 
                        ( ('Inv h)  &&                                             (* inv is initial  *)
                          (forall h1. ('Inv h1) => ('TxGuard ()                    (* inv is inductive *)
                                                      (fun v h2 => (((v=true) => ('TxBody () (fun (u:dyn) => 'Inv) h2)) &&  
                                                                    ((v=false) => ('Inv h2)))) h1)) && 
                          (forall h'. 'Inv h' => 'Post Undef h') ))                  (* inv sufficient for post-condition of guard *)
(* let rec _while guard body h0 = *)
(*   bind (guard ()) (fun v ->  *)
(*      if coerceBool v *)
(*      then (bind (body ()) (fun _ ->  *)
(*            _while guard body h0)) *)
(*      else return_st Undef) *)


(* Intended usage:
    let h0 = get () in
     _while<(fun h0 h1 => SelectTyp h0 local x = SelectTyp h1 local x && ... )> guard body h0
   
*)

val forin: dyn -> ('a -> dyn) -> dyn
val opDelete: dyn -> dyn -> unit
val selectDyn: dyn -> dyn -> dyn
val updateDyn: dyn -> dyn -> dyn -> unit
(*********************************)
type fieldmap

logic val SelectObj : heap -> dyn -> fieldmap
logic val Select : heap -> dyn -> fieldname -> dyn 
logic val Allocd : heap -> dyn -> fieldname -> bool 
logic val Update : 'a::E -> heap -> dyn -> fieldname -> dyn -> heap
logic val Alloc : heap -> dyn -> heap
type SelectTyp :: heap => dyn => fieldname => *
type InDomain :: heap => dyn => E

type HasField :: _ = (fun h d f => ((Allocd h d f)=true))
type Typed :: _ = (fun o ('a::*) => (EqTyp (GetType o) 'a))
type IsObject :: _ = (fun h o => ((Typed o object) && InDomain h o))
type NewObj :: _ = (fun h1 h2 v => ((Typed v object) && 
                                    (not(InDomain h1 v)) &&
                                    (h2=(Alloc h1 v))))
type IsString :: _ = (fun h o => ((Typed o string) && InDomain h o)) (* NS: Why do strings have to be in the domain of the heap? *)

val allocObject: unit -> PST dyn (fun ('Post::dyn => heap => E) h => (forall v h'. NewObj h h' v => 'Post v h'))
val update: o:dyn
         -> f:string 
         -> v:dyn
         -> PST dyn (fun ('Post::dyn => heap => E) h => ((IsObject h o) && 
                                                         (forall h'. (h'=(Update<(GetType v)> h o f v)) => 'Post Undef h')))
(* let update o f v =  
   let rec updateMap field_tv_map =
     match field_tv_map with
       | [] -> []
       | (f', vt) :: rest ->
          if f = f' then (f, MkVt v)::rest
          else (f', vt) :: (updateMap rest) in
   let rec updateHeap h obj = 
     match h with
       | [] -> []
       | (o', field_tv_map) :: rest ->
          if (obj = o') then (o', updateMap field_tv_map) :: rest
          else (o', field_tv_map) :: (updateHeap rest) in
   let impl<'Post> h =  
     match o with  
       | Obj obj -> (Undef, updateHeap h obj)         
       | _ -> assert False 
   in  
     impl *)
  

val select: o:dyn
         -> f:string 
         -> PST dyn (fun ('Post::dyn => heap => E) h => 
                         ((Typed o object) &&
                          (HasField h o f) &&                                                           
                          (forall r. ((r=(Select h o f)) && (Typed r (SelectTyp h o f))) => 'Post r h)))
(*
let select o f =
  let impl<'Post> h =
    let rec lookupMap field_vt_map =
      match field_vt_map with
        | [] -> assert False
        | (f', vt) :: rest -> if (f = f') then (match vt with | MkVt d -> d) else lookupMap rest in
    let rec lookupHeap h obj =
      match h with
        | [] -> assert False
        | (o', map) :: rest -> if (obj = o') then lookupMap map else lookupHeap rest in
    match o with
      | Obj obj -> (lookupHeap h obj, h)
      | _ -> assert False
  in
    impl
*)

val checkUndef: arg:dyn -> PST bool (fun ('Post::bool => heap => E) h => 
                       (((arg=Undef) => 'Post false h) &&
                        ((arg<>(Undef)) => 'Post true h)))

type existsTx :: ((dyn => dyn => (dyn => heap => E) => heap => E) => E) => E
val apply:  f:dyn
         -> this:dyn 
         -> args:dyn 
         -> PST dyn (fun ('Post::dyn => heap => E) h => 
             (existsTx (fun ('Tx::(dyn => dyn => (dyn => heap => E) => heap => E)) => 
                  (Typed f (Function 'Tx) && ('Tx args this 'Post h)))))

val apply_hint: 'Tx::(dyn => dyn => (dyn => heap => E) => heap => E)
         -> f:dyn
         -> this:dyn 
         -> args:dyn 
         -> PST dyn (fun ('Post::dyn => heap => E) h => 
             (Typed f (Function 'Tx) && ('Tx args this 'Post h)))

type Guess :: string => E
val gapply:  f:dyn
         -> this:dyn 
         -> args:dyn 
         -> hint:string
         -> PST dyn (fun ('Post::dyn => heap => E) h => 
             (existsTx (fun ('Tx::(dyn => dyn => (dyn => heap => E) => heap => E)) => 
                  (Typed f (Function 'Tx) && (Guess hint) && ('Tx args this 'Post h)))))

(*
let apply f this args =
  let impl<'Post> h =
    match f with
      | Fun func -> (func this args, h)
      | _ -> assert False
  in 
    impl
*)


(************************ DOM APIs / initial heap ************)
type CanReadSelection :: dyn => E
type CanReadAttr :: dyn => dyn => E
type CanWriteAttr :: dyn => dyn => dyn => E
type CanEdit :: dyn => E
type CanAppend :: dyn => E
type CanCallLocation :: E
assume CanCallLocation

logic val EltAttr : heap -> dyn -> dyn -> dyn
logic val EltTagName : heap -> dyn -> dyn
logic val EltDoc : heap -> dyn -> dyn
logic val EltTextValue : heap -> dyn -> dyn
logic val EltParent : heap -> dyn -> dyn  (* EltParent h child = parent, Dom.f9 has EltParent parent child *)

type FieldTypeInt :: _ = (fun h (o:dyn) (f:fieldname)  => Typed (Select h o f) int)

type FieldTypeString :: _ = (fun h (o:dyn) (f:fieldname)  => Typed (Select h o f) string)

(* "args" has a string "0" field *)
type Singleton :: _ = (fun h (args:dyn) =>
    (IsObject h args &&
     HasField h args "0"))

type SingletonString :: _ = (fun h (args:dyn) =>
    (IsObject h args &&
     HasField h args "0" &&
     FieldTypeString h args "0"))

type SingletonInt :: _ = (fun h (args:dyn) =>
    (IsObject h args &&
     HasField h args "0" &&
     FieldTypeInt h args "0"))

type LocTyping :: _ = (fun h (loc:dyn) => 
    (Typed loc
       (Function (fun args this ('Post::dyn => heap => E) h' => 
            (CanCallLocation && (forall (x:dyn). IsObject h' x => 'Post x h'))))))

type Enumerable :: _ =
    (fun ('P :: heap => dyn => E) (h:heap) (d:dyn) => 
     (IsObject h d &&
      HasField h d "Next" &&
      (Typed (Select h d "Next")
        (Function (fun args this ('Post::dyn => heap => E) h' => 
                   ((this = d) &&
                    (forall (x:dyn). (((x=Undef) || 'P h' x) => 'Post x h'))))))))

type StyleTyping :: _ = (fun h (style:dyn) =>
    (IsObject h style &&
     HasField h style "left" && FieldTypeInt h style "left" &&
     HasField h style "top" && FieldTypeInt h style "top" &&
     HasField h style "position" && FieldTypeString h style "position" &&
     HasField h style "backgroundColor" && FieldTypeString h style "backgroundColor" &&
     HasField h style "borderStyle" && FieldTypeString h style "borderStyle" &&
     HasField h style "borderWidth" && FieldTypeString h style "borderWidth" &&
     HasField h style "borderColor" && FieldTypeString h style "borderColor" &&
     HasField h style "fontSize" && FieldTypeString h style "fontSize"))

(* getAttr: e:elt -> k:string {CanReadAttr e k} -> r:string{ EltAttr e k r} *)
type GetAttributeTyping :: _ = (fun h (elt:dyn) (getAttr:dyn) =>
    (Typed getAttr
       (Function (fun args this ('Post::dyn => heap => E) h' =>
        ((* (this = elt) && *)
         (IsObject h' args) &&
         (HasField h' args "0") && (FieldTypeString h' args "0") &&
         (* CanReadAttr this (Select h' args "0") && *)
        (forall (x:dyn). (((IsObject h' x) && ((EltAttr h' this (Select h' args "0")) = x)) => 'Post x h')))))))
          
(* setAttribute: e:elt -> k:string -> v:string{CanWriteAttr e k v} -> unit*)
type SetAttributeTyping :: _ = (fun h (elt:dyn) (setAttr:dyn) =>
    (Typed setAttr
       (Function (fun args this ('Post::dyn => heap => E) h' =>
        ((HasField h' args "0") && (FieldTypeString h' args "0") &&
         (HasField h' args "1") && (FieldTypeString h' args "1") &&
         (forall (x:dyn). IsObject h' x => 'Post x h'))))))

(* type DomElement :: dyn => E *)
(* type IsElt :: _ = (fun h d => (DomElement d && IsObject h d)) *)
type IsElt2 :: heap => dyn => E
type Unfold :: E => E
type IsElt :: _ = (fun h x => Unfold (IsElt2 h x))

(* appendChild: cp:elt{CanAppend cp} -> ce:elt -> undef{EltParent ce = cp } *)
type AppendChildTyping :: _ = (fun h (elt:dyn) (appendChild:dyn) =>
    (Typed appendChild
       (Function (fun args this ('Post::dyn => heap => E) h' =>
        ((HasField h' args "0") && (IsElt h' (Select h' args "0")) &&
         (forall (cd:dyn). (cd=Undef) (* && ((EltParent h' (Select h' args "0")) = elt) *) => 'Post cd h'))))))

(* removeChild: elt -> elt -> undef *)
type RemoveChildTyping :: _ = (fun h (elt:dyn) (removeChild:dyn) =>
    (Typed removeChild
       (Function (fun args this ('Post::dyn => heap => E) h' =>
            ((HasField h' args "0") && (IsElt h' (Select h' args "0")) &&
             (forall (cd:dyn). (cd=Undef) => 'Post cd h'))))))

 type GetChildrenTyping :: _ = (fun h (elt:dyn) (getChildren:dyn) =>  
     (Typed getChildren 
       (Function (fun args this ('Post::dyn => heap => E) h' => 
        ((* (this = elt) &&  *)
         (forall (child:dyn). Enumerable (fun h'' (e:dyn) => (IsElt h'' e)) h' child => 'Post child h'))))))

type GetChildTX :: _ = (fun args this ('Post::dyn => heap => E) h' =>
    ((SingletonInt h' args) &&
     (forall (child:dyn). ((child=Undef) || (IsElt h' child)) => 'Post child h')))

type GetChild :: _ = (fun h (elt:dyn) (getChild:dyn) =>
    (Typed getChild (Function GetChildTX)))

type GetParent :: _ = (fun h (elt:dyn) (getParent:dyn) =>
    (Typed getParent
      (Function (fun args this ('Post::dyn => heap => E) h' =>
       ((* (this = elt) && *)
        (forall (parent:dyn). (IsElt h' parent) => 'Post parent h'))))))

type EltTyping :: _ = (fun h (elt:dyn) =>
    (IsObject h elt &&
     HasField h elt "getAttribute" && GetAttributeTyping h elt (Select h elt "getAttribute") &&
     HasField h elt "setAttribute" && SetAttributeTyping h elt (Select h elt "setAttribute") &&
     HasField h elt "appendChild" && AppendChildTyping h elt (Select h elt "appendChild") &&
     HasField h elt "removeChild" && RemoveChildTyping h elt (Select h elt "removeChild") &&
     HasField h elt "getChildren" && GetChildrenTyping h elt (Select h elt "getChildren") && 
     HasField h elt "getChild" && GetChild h elt (Select h elt "getChild") &&
     HasField h elt "getParent" && GetParent h elt (Select h elt "getParent") &&
     (***** fields *****)
     HasField h elt "nodeType" && Typed (Select h elt "nodeType") int &&
     HasField h elt "nodeValue" && Typed (Select h elt "nodeValue") string &&
     HasField h elt "tagName" && FieldTypeString h elt "tagName" &&
     HasField h elt "text" && FieldTypeString h elt "text" &&
     HasField h elt "value" && FieldTypeString h elt "value" &&   (* to a function ?? *)
     HasField h elt "style" && StyleTyping h (Select h elt "style")))

assume __Unfold_IsElt: (forall h x. (EqTyp (Unfold (IsElt2 h x)) (EltTyping h x)))

(* getElementsByTagName: doc -> string -> list elt *)
type GetElementsByTagNameTyping :: _ = (fun h (doc:dyn) (loc:dyn) =>
    (Typed loc
      (Function (fun args this ('Post::dyn => heap => E) h' =>
       ((this = doc) &&
        (SingletonString h' args) &&        
        (forall (x:dyn). Enumerable (fun h'' (e:dyn) => (IsElt h'' e && ((EltTagName h'' e) = (Select h' args "0")) && ((EltDoc h'' e) = doc))) h' x => 'Post x h'))))))

(* getElementsByTagName: doc -> string -> list elt *)
type GetElementsByClassNameTyping :: _ = (fun h (doc:dyn) (loc:dyn) =>
    (Typed loc
      (Function (fun args this ('Post::dyn => heap => E) h' =>
       ((this = doc) &&
        (SingletonString h' args) &&
        (forall (x:dyn). Enumerable (fun h'' (e:dyn) => (IsElt h'' e && ((EltAttr h'' e (Str "className")) = (Select h args "0")) && ((EltDoc h'' e) = doc))) h' x => 'Post x h'))))))

(* createElement: d:doc -> t:string -> e:elt{EltDoc e d && EltTagName e t && CanEdit e} *)
type CreateElementTyping :: _ = (fun h (doc:dyn) (f:dyn) =>
    (Typed f
	 (Function (fun args this ('Post::dyn => heap => E) h' =>
	  ((this = doc) &&
	   (SingletonString h args) &&
	   (forall (e:dyn). (IsElt h' e && ((EltDoc h' e) = doc) && ((EltTagName h' e) = (Select h args "0")) && CanEdit e => 'Post e h')))))))
	 
(* createTextNode: d:doc -> s:string -> e:elt{ EltDoc e d && EltTextValue e s } *)
type CreateTextNodeTyping ::_ = (fun h (doc:dyn) (f:dyn) =>
    (Typed f
        (Function (fun args this ('Post::dyn => heap => E) h' =>
         ((this = doc) &&
          (SingletonString h args) &&
          (forall (e:dyn). (IsElt h' e && ((EltDoc h' e) = doc) && ((EltTextValue h' e) = (Select h args "0")) => 'Post e h')))))))

type EventTyping :: _ = (fun h (ev:dyn) => 
    (IsObject h ev &&
     HasField h ev "target" && 
     EltTyping h (Select h ev "target")))

type DocTyping :: _ = (fun h (doc:dyn) => 
     (IsObject h doc &&
      HasField h doc "getElementsByTagName" && GetElementsByTagNameTyping h doc (Select h doc "getElementsByTagName") &&
      HasField h doc "getElementsByClassName" && GetElementsByClassNameTyping h doc (Select h doc "getElementsByClassName") &&
      HasField h doc "createElement" && CreateElementTyping h doc (Select h doc "createElement") &&
      HasField h doc "createTextNode" && CreateTextNodeTyping h doc (Select h doc "createTextNode") &&
      HasField h doc "getLocation" && LocTyping h (Select h doc "getLocation") &&
      (**** fields *****)
      HasField h doc "activeElement" && IsObject h (Select h doc "activeElement") &&
      IsElt h (Select h doc "activeElement") &&
      HasField h doc "body" && IsElt h (Select h doc "body") && 
      HasField h doc "domain" && FieldTypeString h doc "domain" ))

(* toString: selection -> string *)
type SelectionToStringTyping :: _ = (fun h (selection:dyn) (toString:dyn) =>
  (Typed toString 
    (Function (fun args this ('Post::dyn => heap => E) h' =>
       (this = selection &&
       (forall (x:dyn). IsString h' x => 'Post x h'))))))

(* selection: {toString: ...} *)
type SelectionTyping :: _ = (fun h (selection:dyn) =>
  (IsObject h selection &&
   HasField h selection "toString" && SelectionToStringTyping h selection (Select h selection "toString")))
  
(* getSelection: w:window{CanReadSelection w}  -> selection *)
type GetSelectionTyping :: _ = (fun h (window:dyn) (getSelection:dyn) =>
    (Typed getSelection
       (Function (fun args this ('Post::dyn => heap => E) h' =>
          (this = window &&
           IsObject h args && 
           CanReadSelection this && 
           (forall (x:dyn). SelectionTyping h' x => 'Post x h'))))))

(* window: {"getSelection" } *)
type WindowTyping :: _ = (fun h (window:dyn) =>
    (IsObject h window &&
     HasField h window "getSelection" && GetSelectionTyping h window (Select h window "getSelection")))

type CheckUndefTyping :: _ = (fun (cu:dyn) => 
    (Typed cu
       (Function (fun args this ('Post::dyn => heap => E) h' => 
            (((Select h' args "0")=(Undef)) => 'Post (Bool false) h') &&
            (((Select h' args "0")<>(Undef)) => 'Post (Bool true) h')))))

type IsObjectTyping :: _ = (fun (isobj:dyn) => 
    (Typed isobj
       (Function (fun args this ('Post::dyn => heap => E) h' => 
            ( 'Post (Bool false) h' &&
              (IsObject h' (Select h' args "0")) => 'Post (Bool true) h')))))

type XMLHttpRequestTyping :: _ = (fun (sendxml:dyn) => 
    (Typed sendxml
       (Function (fun args this ('Post::dyn => heap => E) h' => 
            'Post Undef h'))))

type ConsoleTyping :: _ = (fun (console:dyn) =>
    (Typed console
       (Function (fun args this ('Post::dyn => heap => E) h' =>
            ((Singleton h' args) && 'Post Undef h')))))

type ChromeTyping :: _ = (fun h (chrome:dyn) => 
    ( (IsObject h chrome) &&
        (HasField h chrome "addListener") &&
        (Typed (Select h chrome "addListener")
           (Function (fun args this ('Post::dyn => heap => E) h' => 
                (existsTx (fun ('Tx::(dyn => dyn => (dyn => heap => E) => heap => E)) => 
                     ((Typed (Select h' args "0") (Function 'Tx)) &&
                        (forall (args':dyn) (r:dyn) (cb:dyn) (h'':heap).
                           (((NewObj h' h'' args') &&
                               (IsObject h'' args') &&
                               (HasField h'' args "0") &&
                               (HasField h'' args "1") &&
                               (HasField h'' args "2") &&
                               ((Select h'' args "0")=r) &&
                               ((Select h'' args "2")=cb) &&
                               (IsObject h'' r) &&
                               (HasField h'' r "command") &&
                               (HasField h'' r "text") &&
                               (Typed cb (Function (fun (_args:dyn) (_this:dyn) ('Postcb::dyn => heap => E) (hcb:heap) => ('Postcb Undef hcb)))))
                            => 'Tx args Undef 'Post h''))))))))))

(* global: {"document": document, "window": window *)
type InitialHeap :: _ = (fun (h:heap) =>
    (IsObject h (Obj global) &&
     HasField h (Obj global) "checkUndef" && CheckUndefTyping (Select h (Obj global) "checkUndef") &&
     HasField h (Obj global) "isObject" && IsObjectTyping (Select h (Obj global) "isObject") &&
     HasField h (Obj global) "sendXMLHttpRequest" && XMLHttpRequestTyping (Select h (Obj global) "sendXMLHttpRequest") &&
     HasField h (Obj global) "consoleLog" && ConsoleTyping (Select h (Obj global) "consoleLog") &&
     HasField h (Obj global) "element" && IsElt h (Select h (Obj global) "element") &&
     HasField h (Obj global) "dummyEvent" && EventTyping h (Select h (Obj global) "dummyEvent") &&
     HasField h (Obj global) "chrome" && ChromeTyping h (Select h (Obj global) "chrome") &&
     (**** fields *****)
     HasField h (Obj global) "document" && DocTyping h (Select h (Obj global) "document") &&
     HasField h (Obj global) "window" && WindowTyping h (Select h (Obj global) "window")))

type initial_heap = h:heap{InitialHeap h}
val checkField : d:dyn -> f:string -> PST dyn (fun ('Post::dyn => heap => E) h => ((HasField h d f) && 'Post Undef h))
val assertF : 'P::heap => E -> d:dyn -> PST dyn (fun ('Post::dyn => heap => E) h => ('P h && ('P h => 'Post Undef h)))
val _dummy_op_AmpAmp             : x:bool -> y:bool -> z:bool { z=true => x=true &&  y=true}
val land       : x:dyn -> y:dyn -> z:bool { z=true => IsTrue(x) && IsTrue(y) }
val lor        : x:dyn -> y:dyn -> z:bool { z=false => IsFalse(x) && IsFalse(y) }
val _dummy_op_BarBar             : x:bool -> y:bool -> z:bool { (z=true => x=true ||  y=true) && 
                                                                 (z=false => x=false && y=false)}
val _dummy_op_Negation           : x:bool -> y:bool { (y=true => x=false) && (y=false => x=true)}

val negate           : x:bool -> PST bool (fun ('Post::bool => heap => E) h => 
                                             (forall (y:bool). (y=true || y=false) && 
                                                              ((y=true => x=false) && 
                                                               (y=false => x=true)) => 'Post y h))

val conj           : x:bool -> y:bool -> PST bool (fun ('Post::bool => heap => E) h => 
                                                      (forall (z:bool). ((z=true || z=false) && 
                                                                        ((z=true <=> (x=true && y=true)) && 
                                                                         (z=false <=> (x=false || y=false)))) => 'Post z h))


end


(* 

 G |-  v : x:dyn{Typed v (Function 'Pre)}   => 
       v=x  \/
       v=Fun v' /\  G |- v':(this:dyn -> args:dyn -> PST dyn ('Pre args this))

*)


