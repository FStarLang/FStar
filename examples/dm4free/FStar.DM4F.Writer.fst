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
module FStar.DM4F.Writer

open FStar.List.Tot

(**********************************************************
 * Dijkstra Monads for Free : Simple writer monad. The log
 * is a list of some type s, i.e. the free monoid over s.
 **********************************************************)

(* The underlying representation type *)
let writer (s:Type) (a:Type) = unit -> M (a * list s)

(* Monad definition *)
let return_writer (s:Type) (a:Type) (x:a) : writer s a = fun () -> x, []

let bind_writer (s:Type) (a:Type) (b:Type) (f:writer s a) (g:a -> writer s b) : writer s b
  = fun () ->
    let x, l1 = f () in
    let y, l2 = g x () in
    y, l1 @ l2

(* Actions *)
let _write (s:Type) (v:s) : writer s unit = fun () -> (), [v]

(*
 * Do the DM4F work. Note that the environment type is a parameter
 * of the resulting effect.
 *)
total reifiable reflectable new_effect {
  WRITER_h (e:Type0) : a:Type -> Effect
  with repr     = writer e
     ; bind     = bind_writer e
     ; return   = return_writer e
     ; write    = _write e
}

new_effect WRITER_int = WRITER_h int

let write = WRITER_int?.write

let test1 () : WRITER_int int (fun () p -> p (2, [5])) =
  write 5;
  2
  
let test2 () : WRITER_int int (fun () p -> p (2, [5;3])) =
  write 5;
  write 3;
  2

let test3 (x:nat) : WRITER_int int (fun () p -> forall x. p (x, [x;x])) =
  write x;
  write x;
  x
