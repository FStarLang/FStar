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
module ErrorMsg

(* Works *)
let rec factorial (x:nat) : nat =
  match x with
    | 0 -> 1
    | _ -> x + factorial (x - 1)

//(Error) Subtyping check failed; expected type x:nat{x << x}; got type int
[@expect_failure]
let rec factorial2 (x:nat) : nat =
  match x with
    | 0 -> 1
    | _ -> x + factorial2 (x - 2)

//(Error) Could not prove termination of this recursive call
[@expect_failure]
let rec factorial3 (x:nat) : Tot nat =
  match x with
    | 0 -> 1
    | _ -> x + factorial3 x
