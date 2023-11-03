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
module LN

(* Making sure that LN violations don't explode the engine *)

open FStar.Tactics.V2

let badtm () : Tac term =
    pack (Tv_BVar (pack_bv ({ index  = 0;
                              sort = seal (pack Tv_Unknown);
                              ppname = seal "ouch"})))

(* We do get a warning about the normalizer failing though, so
silence it. *)
#push-options "--warn_error -264"

let _ =
    assert True 
        by (let _ = trytac (fun () -> exact (badtm ())) in
             trivial ())

#pop-options
