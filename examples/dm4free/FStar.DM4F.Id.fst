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
module FStar.DM4F.Id

let id (a:Type) = unit -> M a
let return_id (a:Type) (x:a) : id a = fun () -> x

// TODO : elaborate f (x ()) to let __x = x () in f __x ?
// TODO : Not exactly sure why let x = x () in f x fails...
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

// Paranoid check that dm4f didn't mess up something
[@expect_failure]
let _ = assert False

// Checking that we can access the generated combinators
let _ = ID?.lift1
let _ = ID?.lift2
let _ = ID?.pure
let _ = ID?.app
let _ = ID?.push
let _ = ID?.wp_if_then_else
let _ = ID?.wp_assert
let _ = ID?.wp_assume
let _ = ID?.wp_close
let _ = ID?.stronger
let _ = ID?.ite_wp
let _ = ID?.null_wp
let _ = ID?.wp_trivial
let _ = ID?.ctx
let _ = ID?.gctx
let _ = ID?.lift_from_pure
let _ = ID?.return_wp
let _ = ID?.return_elab
let _ = ID?.bind_wp
let _ = ID?.bind_elab
let _ = ID?.repr
let _ = ID?.post
let _ = ID?.pre
let _ = ID?.wp
