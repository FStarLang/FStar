(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.DM4F.Reader

(**********************************************************
 * Dijkstra Monads for Free : Simple reader monad
 **********************************************************)

(* The underlying representation type *)
let reader (s:Type) (a:Type) = s -> M a

(* Monad definition *)
let return_reader (s:Type) (a:Type) (x:a) : reader s a = fun e -> x

let bind_reader (s:Type) (a:Type) (b:Type) (f:reader s a) (g:a -> reader s b) : reader s b
  = fun (e:s) -> let x = f e in g x e

(* Actions *)
let _read (s:Type) () : reader s s = fun e -> e

(*
 * Do the DM4F work. Note that the environment type is a parameter
 * of the resulting effect.
 *)
total reifiable reflectable new_effect {
  READER_h (e:Type0) : a:Type -> Effect
  with repr     = reader e
     ; bind     = bind_reader e
     ; return   = return_reader e
     ; read     = _read e
}

new_effect READER_int = READER_h int

let read = READER_int?.read

let test1 () : READER_int int (fun e p -> p (e + 2)) =
  read () + 2
  
let test2 () : READER_int int (fun e p -> p (e + e)) =
  read () + read ()

let test3 () : READER_int int (fun e p -> e > 0 /\ (forall x. x > 0 ==> p x)) =
  let x = read () in
  assert (x >= 0);
  x + 42
