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
module Raise

open FStar.Tactics

exception Ex1
exception Ex2

let _ =
  assert True by begin
    let i =
      match catch (fun () -> raise #int Ex1) with
      | Inr x -> 1
      | Inl Ex1 -> 2
      | Inl e -> raise e
    in ()
  end

[@@(expect_failure [228])]
let x =
  assert True by begin
    let i =
      match catch (fun () -> raise #int Ex2) with
      | Inr x -> 1
      | Inl Ex1 -> 2
      | Inl e -> raise e
    in ()
  end

let f =
  assert True by begin
    let i =
      try raise Ex1; 1 with
      | Ex1 -> 2
      | e -> raise e
    in
    if i <> 2 then fail ""
  end

[@@(expect_failure [228])]
let _ =
  assert True by begin
    let i =
      try raise Ex2; 1 with
      | Ex1 -> 2
      | e -> raise e
    in ()
  end
