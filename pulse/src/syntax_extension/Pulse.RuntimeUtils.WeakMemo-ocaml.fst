(*
   Copyright 2023 Microsoft Research

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

module Pulse.RuntimeUtils.WeakMemo

(* Ephemeron.K1.Make is a functor, so the table is built inside a local
   module and handed out as its two operations. *)
[@@custard_extern "(fun () -> let module M = Stdlib.Ephemeron.K1.Make (struct type t = Stdlib.Obj.t let equal (a:t) (b:t) = a == b || Stdlib.compare a b = 0 let hash (c:t) = Stdlib.Hashtbl.hash c end) in let tbl = M.create 1024 in ((fun k -> M.find_opt tbl (Stdlib.Obj.repr k)), (fun k v -> M.replace tbl (Stdlib.Obj.repr k) v)))"]
let create _ = admit ()
