(*
   Copyright 2026 Microsoft Research
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
module Pulse.Extrinsic.HeapLang.Notation

(** Typed notation for constructing the existing deeply embedded syntax.

    [let! x = e in body] constructs [Let e body], binding [x] to [Var Here].
    The callback is evaluated while building the AST; the resulting program
    contains no host-language function. Inside that binder, [weaken outer]
    transports an outer expression into the extended typing context. Rebind
    outer references once near the top of a nested body to keep them readable.

    All operations below are transparent constructor aliases. Thus proofs can
    use the existing rules, and [assert_norm] can check their expansion against
    raw syntax. [>>] sequences a unit-returning expression; parentheses make
    nested sequencing explicit. Ordinary F* [let] names syntax without executing
    it, whereas [let!] introduces a source-language evaluation and binding. *)

open Pulse.Extrinsic.HeapLang

let weaken (#g:list ty) (#a #t:ty) (e:expr g t) : expr (a :: g) t =
  rename (fun _ x -> There x) e

let ( let! ) (#g:list ty) (#a #b:ty) (bound:expr g a)
  (body:expr (a :: g) a -> Tot (expr (a :: g) b)) : expr g b =
  Let bound (body (Var Here))

let ( >> ) (#g:list ty) (#t:ty) (first:expr g TUnit) (rest:expr g t) : expr g t =
  Seq first rest

let int_ (#g:list ty) (n:Prims.int) : expr g TInt = Val n
let bool_ (#g:list ty) (b:Prims.bool) : expr g TBool = Val b
let unit_ (#g:list ty) : expr g TUnit = Val ()
let ref_ (#g:list ty) (r:PulseCore.Heap.core_ref) : expr g TRef = Val r
let null (#g:list ty) : expr g TRef = Val PulseCore.Heap.core_ref_null
let alloc (#g:list ty) (v:expr g TInt) = Alloc v
let load (#g:list ty) (r:expr g TRef) = Load r
let store (#g:list ty) (r:expr g TRef) (v:expr g TInt) = Store r v
let cas (#g:list ty) (r:expr g TRef) (old next:expr g TInt) = Cas r old next
let add (#g:list ty) (x y:expr g TInt) = Add x y
let eq (#g:list ty) (x y:expr g TInt) = Eq x y
let if_ (#g:list ty) (#t:ty) (c:expr g TBool) (yes no:expr g t) = If c yes no
let fork (#g:list ty) (child:expr g TUnit) = Fork child
let while_ (#g:list ty) (condition:expr g TBool) (body:expr g TUnit) = While condition body
let node (#g:list ty) (data:expr g TInt) (next:expr g TRef) = NewNode data next
let data (#g:list ty) (r:expr g TRef) = ReadData r
let next (#g:list ty) (r:expr g TRef) = ReadNext r
let link (#g:list ty) (r target:expr g TRef) = WriteNext r target
