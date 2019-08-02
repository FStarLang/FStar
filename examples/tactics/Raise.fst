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

exception Wat
exception Wut

let _ =
  assert True by begin
    let i =
      match catch (fun () -> raise #int Wat) with
      | Inr x -> 1
      | Inl e -> begin match e with
                | Wat -> 2
                | e -> raise e
                end
    in ()
  end

[@(expect_failure [228])]
let _ =
  assert True by begin
    let i =
      match catch (fun () -> raise #int Wut) with
      | Inr x -> 1
      | Inl e -> begin match e with
                | Wat -> 2
                | e -> raise e
                end
    in ()
  end

let _ =
  assert True by begin
    let i =
      try raise Wat; 1
      with
      | e -> begin match e with
            | Wat -> 2
            | e -> raise e
            end
    in ()
  end

[@(expect_failure [228])]
let _ =
  assert True by begin
    let i =
      try raise Wut; 1
      with
      | e -> begin match e with
            | Wat -> 2
            | e -> raise e
            end
    in ()
  end
