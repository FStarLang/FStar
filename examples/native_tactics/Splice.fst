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
module Splice

open FStar.Tactics

let make_x_42 () : Tac unit =
    (* The let binds are needed due to the Tac effect *)
    (* TODO: make the "A" prefix unneeded, it doesn't make sense to use another module *)
    let sv : sigelt_view = Sg_Let false (pack_fv ["A"; "x"]) [] (`nat) (`42) in
    let ses : list sigelt = [pack_sigelt sv] in
    exact (quote ses)

%splice (make_x_42 ())
