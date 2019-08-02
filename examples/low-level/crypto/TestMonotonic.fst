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
module TestMonotonic

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef

type t = option bool

let rel (a:t) (b:t) =
  match a, b with
  | None, None -> True
  | None, Some false -> True
  | None, Some true -> True
  | Some false, Some false -> True
  | Some false, Some true -> True
  | Some true,  Some true -> True
  | _, _ -> False

val root_has_color_zero': u:unit ->
  Lemma (requires True) (ensures (color root = 0)) [SMTPat (has_type u unit)]
let root_has_color_zero' _ = root_has_color_zero ()

val rel_transitive: a:t -> b:t -> c:t -> Lemma
  (requires True)
  (ensures (a `rel` b /\ b `rel` c ==> a `rel` c))
let rel_transitive a b c = ()


val init: unit -> ST (m_rref root t rel)
  (requires (fun m0 -> True))
  (ensures  (fun m0 r m1 -> witnessed (fun m -> Some? (m_sel m r))))
let init _ =
  let r = m_alloc #t #rel root (Some false) in
  witness r (fun m -> Some? (m_sel m r));
  r

val set: mr:m_rref root t rel -> STL unit
  (requires (fun m0 -> witnessed (fun m -> Some? (m_sel m mr))))
  (ensures  (fun _ _ _ -> witnessed (fun m -> m_sel m mr = Some true)))
let set mr =
  m_recall mr;
  testify (fun m -> Some? (m_sel m mr));
  let v = m_read mr in
  begin
  match v with
  | Some true -> ()
  | Some false -> m_write mr (Some true)
  | _ -> assert False
  end;
  witness mr (fun m -> m_sel m mr = Some true)

val test: unit -> ST bool
  (requires (fun _ -> True))
  (ensures  (fun m0 b m1 -> b = true))
let test _ =
  let mr = init () in
  set mr;
  testify (fun m -> m_sel m mr = Some true);
  m_recall mr;
  match m_read mr with
  | Some b -> b
  | None   -> false
