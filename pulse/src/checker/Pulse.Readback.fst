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

module Pulse.Readback
module R = FStar.Reflection.V2
open Pulse.Syntax.Base
open Pulse.Reflection.Util
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2
let debug_log (f: unit -> T.Tac unit) : T.Tac unit = if RU.debug_at_level_no_module "readback" then f()

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x

let readback_observability (t:R.term)
: option (obs:observability { elab_observability obs == t })
= let open R in
  match inspect_ln t with
  | R.Tv_FVar fv ->
    let fv_lid = inspect_fv fv in
    if fv_lid = observable_lid
    then Some Observable
    else if fv_lid = neutral_lid
    then Some Neutral
    else None
  | _ -> None

#push-options "--z3rlimit_factor 20"
// TODO: FIXME: may be mark as opaque_to_smt
let try_readback_st_comp (t:R.term)
  : option (c:comp{elab_comp c == t}) =

  let open R in
  let hd, args = collect_app_ln t in
  match inspect_ln hd with
  | Tv_UInst fv [u] ->
    let fv_lid = inspect_fv fv in
    if fv_lid = stt_lid
    then match args with
         | [res; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs; sort=sort } =
                  inspect_binder b
              in    
              assume (fv == stt_fv);
              assume (aq == Q_Explicit           /\
                      attrs == []                /\
                      sort == fst res /\
                      snd res == Q_Explicit      /\
                      snd pre == Q_Explicit      /\
                      snd post == Q_Explicit);

              assume (t == mk_stt_comp u (fst res) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let res' = fst res in
              let pre' = fst pre in
              let post' = body in
              let c = C_ST {u; res=res'; pre=pre';post=post'} in
              Some (c <: c:Pulse.Syntax.Base.comp{ elab_comp c == t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_atomic_lid
    then match args with
         | [res; obs; opened; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs }
                  = inspect_binder b
              in    
              let res' = fst res in
              let? obs' = readback_observability (fst obs) in
              let opened' = fst opened in
              let pre' = fst pre in
              let post' = body in
              assume (t == mk_stt_atomic_comp (fst obs) u (fst res) (fst opened) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let c = C_STAtomic opened' obs' ({u; res=res'; pre=pre';post=post'}) in
              Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_ghost_lid
    then match args with
         | [res; inames; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs }
                  = inspect_binder b
              in    
              let res' = fst res in
              let inames' = fst inames in
              let pre' = fst pre in
              let post' = body in
              assume (t == mk_stt_ghost_comp u (fst res) inames' (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let c = C_STGhost inames' ({u; res=res'; pre=pre';post=post'}) in
              Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
            | _ -> None)
         | _ -> None    
    else None  
  | _ -> None
#pop-options

let readback_comp (t:R.term)
  : option (c:comp { elab_comp c == t }) =

  let ropt = try_readback_st_comp t in
  match ropt with
  | Some c ->
    // debug_log (fun _ -> T.print (Printf.sprintf "readback_comp: %s as\n%s\n" (T.term_to_string t) (P.comp_to_string c)));
    ropt
  | _ ->
    let t' = t in
    Some (C_Tot t' <: c:comp{ elab_comp c == t })
