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
(*
  Source JS program: 

  function foo(x) {
        x.f = 17; 
        return 42;
  }

  var x = document.getLocation();
  foo(x)

*)

module Test

type CanCallLocation :: E
(* Try commenting out the next line and the verification should fail *)
assume CanCallLocation

type LocTyping :: _ = (fun h (loc:dyn) => 
    (Typed loc
       (Function (fun this args ('Post::dyn => heap => E) h' => 
            (CanCallLocation && (forall (x:dyn). IsObject h' x => 'Post x h'))))))

type DocTyping :: _ = (fun h (doc:dyn) => 
     (IsObject h doc &&
      HasField h doc "getLocation" &&
      LocTyping h (Select h doc "getLocation")))
    
type InitialHeap :: _ = (fun (h:heap) => 
     (IsObject h (Obj global) &&
      HasField h (Obj global) "document" &&
      DocTyping h (Select h (Obj global) "document")))


let main (h:initial_heap) = 

  let foo = fun (this:dyn) (x:dyn) -> 
    let y = (Int 17) in 
    update x "f" y;
    select x "f";
    Undef in
    (* Int 42 in *)

    update (Obj global) "foo" (Fun foo);
    
    
    let doc = select (Obj global) "document" in
      
    (* let loc = select doc "getLocation" in *)
      
    (* let x = apply loc (Obj global) Undef in *)
      
    (* let foo = (\* \h. HasType (Obj global) object && *)
    (*                        HasField h (Obj global) "foo" && *)
    (*                        \foo. \h. HasType foo (Function 'Prefoo) && 'Prefoo (Obj global) x True h *)
    (*                        (SelectObj h (Obj global) "foo") h *)
    (*                 *\) *)
    let foo' = select (Obj global) "foo" in
      
    (*   (\* \h. HasType foo (Function 'Prefoo) && 'Prefoo (Obj global) x True h *\) *)
      
    let _ = apply foo' doc doc in 
      Undef
        (* let bar = select (Obj global) "bar" in *)
        (*   apply bar (Obj global) Undef *)
        

 (* {True} *)
      
end
