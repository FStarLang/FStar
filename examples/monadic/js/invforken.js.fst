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
#monadic 

module Test

(*

  function getPath(elt: Elt, path (list int) ) {
      var cur = elt;
      while (path <> Undef && cur <> Undef) {
         cur = elt.getChild(path.hd);
         path = path.tl;
      }
      return cur;
  }
  
*)

type IsList :: heap => dyn => E
type CutIsList :: _ = (fun h d => ((d=Undef) || ((IsObject h d) && ((IsObject h d) => (IsList h d)))))
type ListTyping :: _ = (fun h l =>
    ((l=Undef) ||
    ((IsObject h l) &&
     (HasField h l "hd") && (Typed (Select h l "hd") int) &&
     (HasField h l "tl") &&
     (IsList h (Select h l "tl")))))
assume IsList_Undef:(forall h. IsList h Undef)
assume IsList_Typing1:(forall h d.{:pattern (IsList h d)}
                        IsList h d <=> ListTyping h d)
assume IsList_trans:(forall h1 h2 d.{:pattern (SelectObj h2 d); (IsList h1 d)}
                        ((IsList h1 d) && (((Select h1 d "hd")=(Select h2 d "hd")) && 
                                           ((Select h1 d "tl")=(Select h2 d "tl"))) => IsList h2 d))

type Inv :: dyn => heap => heap => E
(* type Inv :: _ = (fun locals h0 h1 => *)
(*     (((SelectObj h0 (Obj global))=(SelectObj h1 (Obj global))) && *)
(*      (IsObject h1 locals) && *)
(*      (HasField h1 locals "path") && *)
(*      (HasField h1 locals "cur") && *)
(*      (IsList h1 (Select h1 locals "path")) && *)
(*      ((Select h1 locals "cur")=Undef) || *)
(*       (IsElt h1 (Select h1 locals "cur")))) *)

let main = (fun (x_1:initial_heap) -> 
              let getPath =
                (fun (x_5:dyn) (x_5_1:dyn) ->
                   let locals = allocObject () in
                   let x_5_4 = update locals "cur" Undef in
                   let x_5_6 = update locals "path" Undef in
                       
                   let _ = update locals "cur" (select x_5_1 "0") in
                   let _ = update locals "path" (select x_5_1 "1") in
                     
                   let h0 = get () in
                   let _ =  _while<(Inv locals h0),_,_> (* (Inv locals h0) is the loop invariant that would be great to infer *)
                     (fun () -> (conj 
                                   (negate ((select locals "path") = Undef))
                                   (negate ((select locals "cur") = Undef))))
                     (fun () -> 
                        let x_9_1 = allocObject () in
                        let hd = select (select locals "path") "hd" in 
                        let _ = (update locals "path" (select (select locals "path") "tl")) in
                        let _ = update x_9_1 "0" hd in
                        let tmp = select locals "cur" in
                        let _ = update locals "cur" (apply_hint<GetChildTX> (select tmp "getChild") tmp x_9_1) in 
                          Undef) in 
                     (select locals "cur")) in 
                
              let x_79 = allocObject () in
              let tmp = (select (Obj global) "element") in
              let x_79_2 = update x_79 "0" tmp in
              let path = allocObject() in
              let _ = update path "hd" (Int 0) in
              let _ = update path "tl" Undef in
              let x_79_2 = update x_79 "1" path in
                getPath (Obj global) x_79)
