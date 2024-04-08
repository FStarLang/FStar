(*
   Copyright 2024 Microsoft Research

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

module PulseCore.Observability
(*
obs > unobs >----.
                 |
                 v
      ghost > neutral > ghost non_info

ghost info    , neutral info     |> ghost info
ghost non_info, neutral info     |> neutral info
ghost info    , neutral non_info |> ghost non_info
ghost non_info, neutral non_info |> ghost non_info

neutral _, ghost a |> ghost a
*)
type observability =
  | Neutral
  | Observable

let at_most_one_observable o1 o2 =
  match o1, o2 with
  | Observable, Observable -> false
  | _ -> true

let join_obs o1 o2 =
  match o1, o2 with
  | Neutral, Neutral -> Neutral
  | _ -> Observable
