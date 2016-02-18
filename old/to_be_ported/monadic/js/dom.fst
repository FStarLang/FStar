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
module DOM
open JSVerify

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

logic val Select : heap -> dyn -> fn -> dyn 
define Select_def: forall h d f. Select h d f = SelectField h d f

type Typed :: _ = fun (o:dyn) ('a::E) => (EqTyp (AsE o) 'a)
type FieldTypeInt :: _ = fun h (o:dyn) (f:fn) => Typed (SelectField h o f) int
type FieldTypeString :: _ = fun h (o:dyn) (f:fn) => Typed (SelectField h o f) string
type IsObject :: _ = fun (h:heap) (o:dyn) => Obj_is o
type HasField :: _ = fun h o f => HasDataField h o f

(* "args" has a string "0" field *)
type Singleton :: _ = fun h (args:dyn) =>
    (Obj_is args 
     && HasDataField h args "0")
    
type SingletonString :: _ = fun h (args:dyn) =>
    (Obj_is args 
     && HasDataField h args "0" 
     && FieldTypeString h args "0")

type SingletonInt :: _ = fun h (args:dyn) =>
    (Obj_is args 
     && HasDataField h args "0" 
     && FieldTypeInt h args "0")

type LocTyping :: _ = (fun h (l:dyn) => 
    (Typed l
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' => 
            (CanCallLocation && (forall (x:dyn). Obj_is x ==> 'Post (V x) h'))))))

type NextTX :: _ = fun ('P::heap => dyn => E) args this ('Post::result dyn => heap => E) h => 
    ((* (this = d) && *)
     (forall (x:dyn). (((x=Undef) || 'P h x) => 'Post (V x) h)))

type Enumerable :: _ = fun ('P :: heap => dyn => E) (h:heap) (d:dyn) => 
    (IsObject h d &&
     HasDataField h d "Next" &&
     (Typed (SelectField h d "Next") (TxAsE (NextTX 'P))))
 
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

type GetAttributeTX :: _ = fun args this ('Post::result dyn => heap => E) h =>
    (IsObject h args 
     && HasField h args "0"
     && FieldTypeString h args "0" 
     && (forall (x:dyn). (IsObject h x 
                          && ((EltAttr h this (Select h args "0")) = x)) 
         ==> 'Post (V x) h))
    
(* getAttr: e:elt -> k:string {CanReadAttr e k} -> r:string{ EltAttr e k r} *)
type GetAttributeTyping :: _ = fun h (elt:dyn) (getAttr:dyn) =>
    (Typed getAttr (TxAsE (Meta_named "getAttribute" GetAttributeTX)))
    
(* setAttribute: e:elt -> k:string -> v:string{CanWriteAttr e k v} -> unit*)
type SetAttributeTyping :: _ = fun h (elt:dyn) (setAttr:dyn) =>
    (Typed setAttr
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' =>
            (HasField h' args "0" 
             && FieldTypeString h' args "0" 
             && HasField h' args "1" 
             && FieldTypeString h' args "1" 
             && (forall (x:dyn). IsObject h' x ==> 'Post (V x) h')))))
    
(* type DomElement :: dyn => E *)
(* type IsElt :: _ = (fun h d => (DomElement d && IsObject h d)) *)
type IsElt2 :: heap => dyn => E
type IsElt :: _ = (fun h x => Unfold (IsElt2 h x))

(* appendChild: cp:elt{CanAppend cp} -> ce:elt -> undef{EltParent ce = cp } *)
type AppendChildTyping :: _ = (fun h (elt:dyn) (appendChild:dyn) =>
    (Typed appendChild
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' =>
            (HasField h' args "0" 
             && IsElt h' (Select h' args "0")
             && (* && ((EltParent h' (Select h' args "0")) = elt) *) 'Post (V Undef) h')))))

(* removeChild: elt -> elt -> undef *)
type RemoveChildTyping :: _ = (fun h (elt:dyn) (removeChild:dyn) =>
    (Typed removeChild
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' =>
            (HasField h' args "0" 
             && IsElt h' (Select h' args "0") 
             && 'Post (V Undef) h')))))

type GetChildrenTyping :: _ = (fun h (elt:dyn) (getChildren:dyn) =>  
    (Typed getChildren 
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' => 
            ((* (this = elt) &&  *)
              (forall (child:dyn). Enumerable (fun h'' (e:dyn) => (IsElt h'' e)) h' child 
               ==> 'Post (V child) h'))))))

type GetChildTX :: _ = fun args this ('Post::result dyn => heap => E) h =>
    (SingletonInt h args
     && (forall (child:dyn). ((child=Undef) || (IsElt h child)) => 'Post (V child) h))

type GetChild :: _ = (fun h (elt:dyn) (getChild:dyn) =>
    (Typed getChild 
       (TxAsE (Meta_named "getChild" GetChildTX))))

type GetParentTX :: _ = fun args this ('Post::result dyn => heap => E) h =>
    (forall (parent:dyn). (IsElt h parent) => 'Post (V parent) h)

type GetParent :: _ = (fun h (elt:dyn) (getParent:dyn) =>
    (Typed getParent (TxAsE (Meta_named "getParent" GetParentTX))))
    
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

type HasTag :: _ = fun (tag:dyn) (h:heap) (e:dyn) => 
    (IsElt h e && ((EltTagName h e) = tag))
    
type GetElementsByTagNameTX :: _ = 
    (fun args this ('Post::result dyn => heap => E) h =>
        ((* (this = doc) && *)
          (SingletonString h args) &&        
            (forall (x:dyn). Enumerable (HasTag (Select h args "0")) h x 
             ==> 'Post (V x) h)))
      
(* getElementsByTagName: doc -> string -> list elt *)
type GetElementsByTagNameTyping :: _ = (fun h (doc:dyn) (dloc:dyn) =>
    (Typed dloc (TxAsE (Meta_named "getElementsByTagName" GetElementsByTagNameTX))))

type HasClass :: _ = fun (cn:dyn) (h:heap) (e:dyn) => 
    (IsElt h e && (EltAttr h e (Str "className") = cn))

type GetElementsByClassNameTX :: _ = 
    (fun args this ('Post::result dyn => heap => E) h =>
        ((* (this = doc) && *)
          (SingletonString h args) &&
            (forall (x:dyn). (Enumerable (HasClass (Select h args "0")) h x)
             ==> 'Post (V x) h)))
      
(* getElementsByTagName: doc -> string -> list elt *)
type GetElementsByClassNameTyping :: _ = (fun h (doc:dyn) (dloc:dyn) =>
    (Typed dloc (TxAsE (Meta_named "getElementsByClassName" GetElementsByClassNameTX))))

type GetElementByIdTX :: _ = 
    (fun args this ('Post::result dyn => heap => E) h =>
        ((SingletonString h args) &&
            (forall (x:dyn). (Enumerable (HasClass (Select h args "0")) h x)
             ==> 'Post (V x) h)))

(* getElementById: doc -> string -> list elt *)
type GetElementByIdTyping :: _ = (fun h (doc:dyn) (dloc:dyn) =>
    (Typed dloc (TxAsE (Meta_named "getElementById" GetElementByIdTX))))

(* createElement: d:doc -> t:string -> e:elt{EltDoc e d && EltTagName e t && CanEdit e} *)
type CreateElementTyping :: _ = (fun h (doc:dyn) (f:dyn) =>
    (Typed f
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' =>
	    ((this = doc) &&
	       (SingletonString h args) &&
	       (forall (e:dyn). (IsElt h' e && ((EltDoc h' e) = doc) && ((EltTagName h' e) = (Select h args "0")) && CanEdit e => 'Post (V e) h')))))))
	 
(* createTextNode: d:doc -> s:string -> e:elt{ EltDoc e d && EltTextValue e s } *)
type CreateTextNodeTyping ::_ = (fun h (doc:dyn) (f:dyn) =>
    (Typed f
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' =>
            ((this = doc) &&
               (SingletonString h args) &&
               (forall (e:dyn). (IsElt h' e && ((EltDoc h' e) = doc) && ((EltTextValue h' e) = (Select h args "0")) => 'Post (V e) h')))))))
    
type EventTyping :: _ = (fun h (ev:dyn) => 
    (IsObject h ev &&
       HasField h ev "target" && 
       EltTyping h (Select h ev "target")))

type DocTyping :: _ = (fun h (doc:dyn) => 
     (IsObject h doc &&
      HasField h doc "getElementsByTagName" && GetElementsByTagNameTyping h doc (Select h doc "getElementsByTagName") &&
      HasField h doc "getElementsByClassName" && GetElementsByClassNameTyping h doc (Select h doc "getElementsByClassName") &&
	  HasField h doc "getElementById" && GetElementByIdTyping h doc (Select h doc "getElementById") &&
      HasField h doc "createElement" && CreateElementTyping h doc (Select h doc "createElement") &&
      HasField h doc "createTextNode" && CreateTextNodeTyping h doc (Select h doc "createTextNode") &&
      HasField h doc "getLocation" && LocTyping h (Select h doc "getLocation") &&
      (**** fields *****)
      HasField h doc "activeElement" && IsObject h (Select h doc "activeElement") &&
      IsElt h (Select h doc "activeElement") &&
      HasField h doc "body" && IsElt h (Select h doc "body") && 
      HasField h doc "domain" && FieldTypeString h doc "domain" ))

type windowSelectionToStringTx :: _ = 
  (fun args this ('Post::result dyn => heap => E) h' =>
       ((*this = selection &&*)
       (forall (x:dyn). IsString x => 'Post (V x) h')))

(* toString: selection -> string *)
type SelectionToStringTyping :: _ = (fun h (selection:dyn) (toString:dyn) =>
  (Typed toString 
    (TxAsE (Meta_named "toString" windowSelectionToStringTx))))

(* selection: {toString: ...} *)
type SelectionTyping :: _ = (fun h (selection:dyn) =>
    (IsObject h selection &&
       HasField h selection "toString" && SelectionToStringTyping h selection (Select h selection "toString")))
  
type GetSelectionTx :: _ = 
(fun args this ('Post::result dyn => heap => E) h' =>
            ((*this = window &&
                IsObject h args && 
                CanReadSelection this && *)
                (forall (x:dyn). SelectionTyping h' x => 'Post (V x) h')))

(* getSelection: w:window{CanReadSelection w}  -> selection *)
type GetSelectionTyping :: _ = (fun h (window:dyn) (getSelection:dyn) =>
    (Typed getSelection
       (TxAsE (Meta_named "getSelection" GetSelectionTx))))
    
(* window: {"getSelection" } *)
type WindowTyping :: _ = (fun h (window:dyn) =>
    (IsObject h window &&
     HasField h window "getSelection" && GetSelectionTyping h window (Select h window "getSelection")))

type CheckUndefTyping :: _ = (fun (cu:dyn) => 
    (Typed cu
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' => 
            (((Select h' args "0")=(Undef)) => 'Post (V (Bool false)) h') &&
            (((Select h' args "0")<>(Undef)) => 'Post (V (Bool true)) h')))))

type IsObjectTyping :: _ = (fun (isobj:dyn) => 
    (Typed isobj
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' => 
            ( ((not (IsObject h' (SelectField h' args "0"))) ==> 'Post (V (Bool false)) h') 
              && (IsObject h' (Select h' args "0")) ==> 'Post (V (Bool true)) h')))))
    
type XMLHttpRequestTyping :: _ = (fun (sendxml:dyn) => 
    (Typed sendxml
       (TxAsE (fun args this ('Post::result dyn => heap => E) h' => 
            'Post (V Undef) h'))))

type ConsoleLogTX :: _ = fun (args:dyn) (this:dyn) ('Post::result dyn => heap => E) h' =>
    ((Singleton h' args) && 'Post (V Undef) h')
    
type ConsoleTyping :: _ = (fun h (console:dyn) =>
  ((IsObject h console) &&
    (HasField h console "log") &&
    (Typed (Select h console "log") (TxAsE (Meta_named "log" ConsoleLogTX)))))

type NewObj :: _ = (fun h1 h2 v => ((Typed v object) && 
                                      (not(InHeap h1 (GetLoc v))) &&
                                      (h2=(UpdHeap h1 (GetLoc v) emptyObj))))

type NewObjInit :: _ = (fun h1 h2 v o => ((Typed v object) && 
                                            (not(InHeap h1 (GetLoc v))) &&
                                            (h2=(UpdHeap h1 (GetLoc v) o))))

type addListenerCBTx :: _ = (fun (_args:dyn) (_this:dyn) ('Postcb::result dyn => heap => E) (hcb:heap) => 
    ('Postcb (V Undef) hcb))

type addListenerExTx :: _ = (fun args this ('Post::result dyn => heap => E) h ('Tx::(dyn => dyn => (result dyn => heap => E) => heap => E)) => 
    ((Typed (Select h args "0") (TxAsE 'Tx)) &&
       (forall (args':dyn) (r:dyn) (s:dyn) (cb:dyn) (h':heap) (o:obj).
          (((NewObjInit h h' args' o) &&
              (IsObject h' args') &&
              (HasField h' args' "0") &&
              (HasField h' args' "1") &&
              (HasField h' args' "2") &&
              ((Select h' args' "0")=r) &&
			  ((Select h' args' "1")=s) &&
              ((Select h' args' "2")=cb) &&
              (IsObject h' r) &&
			  (IsObject h' s) &&
              (HasField h' r "command") &&
              (HasField h' r "text") &&
			  (HasField h' r "id") &&
			  (HasField h' r "action") &&
			  (HasField h' s "tab") &&
              (Typed cb (TxAsE (Meta_named "addListenerCB" addListenerCBTx))))
           ==> 'Tx args' Undef 'Post h'))))

type addListenerTx :: _ = (fun args this ('Post::result dyn => heap => E) h => 
    (existsTx (addListenerExTx args this 'Post h)))
    
type sendRequestTx1 :: _ = fun args this ('Post::result dyn => heap => E) h =>
  ((Singleton h args) && ('Post (V Undef) h)) 

type sendRequestExTx2 :: _ = (fun args this ('Post::result dyn => heap => E) h ('Tx::(dyn => dyn => (result dyn => heap => E) => heap => E)) => 
    ((Typed (Select h args "1") (TxAsE 'Tx)) &&
       (forall (args':dyn) (r:dyn) (h':heap) (o:obj).
          (((NewObjInit h h' args' o) &&
              (IsObject h' args') &&
              (HasField h' args' "0") &&
              ((Select h' args' "0")=r) &&
              (IsObject h' r) &&
              (HasField h' r "password"))
           ==> 'Tx args' Undef 'Post h'))))

type sendRequestTx2 :: _ = fun args this ('Post::result dyn => heap => E) h =>
  (existsTx (sendRequestExTx2 args this 'Post h))

type ChromeTyping :: _ = (fun h (chrome:dyn) => 
    ((IsObject h chrome) &&
	   (HasField h chrome "sendRequest1") &&
	   (Typed (Select h chrome "sendRequest1") 
	          (TxAsE (Meta_named "sendRequest1" sendRequestTx1))) &&
	   (HasField h chrome "sendRequest2") &&
	   (Typed (Select h chrome "sendRequest2")
	          (TxAsE (Meta_named "sendRequest2" sendRequestTx2))) &&
       (HasField h chrome "addListener") &&
       (Typed (Select h chrome "addListener") (TxAsE (Meta_named "addListener" addListenerTx)))))
    
(* global: {"document": document, "window": window *)
type InitialHeap :: _ = (fun (h:heap) =>
    (IsObject h (Obj global) &&
     HasField h (Obj global) "checkUndef" && CheckUndefTyping (Select h (Obj global) "checkUndef") &&
     HasField h (Obj global) "isObject" && IsObjectTyping (Select h (Obj global) "isObject") &&
     HasField h (Obj global) "sendXMLHttpRequest" && XMLHttpRequestTyping (Select h (Obj global) "sendXMLHttpRequest") &&
	 HasField h (Obj global) "console" && ConsoleTyping h (Select h (Obj global) "console") &&
     HasField h (Obj global) "element" && IsElt h (Select h (Obj global) "element") &&
     HasField h (Obj global) "dummyEvent" && EventTyping h (Select h (Obj global) "dummyEvent") &&
     HasField h (Obj global) "chrome" && ChromeTyping h (Select h (Obj global) "chrome") &&
     (**** fields *****)
     HasField h (Obj global) "document" && DocTyping h (Select h (Obj global) "document") &&
     HasField h (Obj global) "window" && WindowTyping h (Select h (Obj global) "window")))

type initial_heap = h:heap{InitialHeap h}

end
