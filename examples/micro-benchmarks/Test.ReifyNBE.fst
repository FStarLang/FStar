(*
   Copyright 2008-2018 Microsoft Research

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
module Test.ReifyNBE

/// This is a copy of FStar.DM4F.Id

let id (a:Type) = unit -> M a
let return_id (a:Type) (x:a) : id a = fun () -> x
let bind_id (a:Type) (b:Type) (x:id a) (f:(a -> id b)) : id b =
  fun () ->
    let x = x () in
    f x ()
total reifiable reflectable new_effect {
  ID : a:Type -> Effect
  with repr   = id
     ; bind   = bind_id
     ; return = return_id
  }

////////////////////////////////////////////////////////////////////////////////
#reset-options

let test1 (a:Type) (y:a) =
    assert (norm [nbe; delta] (reify (ID?.reflect (return_id a y)) ()) == y)

open FStar.Tactics

let test2 (a:Type) (x:a) =
    assert True by (fun () -> let t0 = quote (reify (ID?.reflect (return_id a x)) ()) in
                              (* print ("t0 = " ^ term_to_string t0); *)
                              let t1 = norm_term [nbe; delta] t0 in
                              if term_eq t1 (quote x)
                              then ()
                              else fail ("The reify was not normalized!: " ^ term_to_string t1))
