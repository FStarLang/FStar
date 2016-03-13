(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"

(* F# implementation of extern calls from F*
   F* signatures from externs shown here in comments *)
module LFS

(* extern FS val check_pwd: string -> string -> bool *)
let check_pwd (s:string) (r:string) = false

(* extern FS val ext_get_inbox : unit -> list email *)
let ext_get_inbox (x:bool) = 
  new Prims.Nil<DataModel.email>() :> Prims.list<DataModel.email>

(* extern FS val ext_mk_appt: appt -> unit *)
let ext_mk_appt (x:DataModel.appt) = false

(* extern FS val ext_send_email: prin -> string -> unit *)
let ext_send_email (x:Authentication.prin) (y:string) = false

(* extern FS val ext_store_cookie : cookierec -> unit *)
let ext_store_cookie (x:Externs.cookierec) = false

(*********************************************************************************)
(* Call from F# to F* for apptmaker *)Examples of calls from F# into F* *)
(*********************************************************************************)
exception Cred_failure

(* extern FS val get_credential: unit -> (p:prin * cred p) *)
let get_credential (b:bool) = 
  let plugin = new Authentication.U("Alice") :> Authentication.prin in
  let oc = Authentication.login plugin "hello" in
    match oc with 
      | :? Prims.Some<Authentication.cred> -> 
        let oc = oc :?> Prims.Some<Authentication.cred> in
        let c = oc.field_1 in
          new Prims.Tuple_UU<Authentication.prin, Authentication.cred>(plugin, c) :> 
              Prims.DepTuple2SS<Authentication.prin, Authentication.cred>
      | _ -> raise Cred_failure

(* extern FS val detect_appt_from: prin -> string -> option appt *)
let detect_appt_from (p:Authentication.prin) : string -> Prims.option<DataModel.appt> = 
  fun (s:string) -> (new Prims.None<DataModel.appt>() :> Prims.option<DataModel.appt>)

(* extern FS val appt_as_string: appt -> string *)
let appt_as_string (a:DataModel.appt) = ""

(* -------------------------------------------------------------------------------- *)
(* Unused *)
(* -------------------------------------------------------------------------------- *)
(* let ext_get_cookie (owner:Authentication.prin) (cname:string) = new Prims.None<scookierec>() :> Prims.option<scookierec> *)
(* let ext_get_evt_queue (u:bool) = new Prims.Nil<(DataModel.evname * evlisteners)>() :> Prims.list<(DataModel.evname * evlisteners)> *)
(* let ext_set_evt_queue (evqueue:Prims.list<(DataModel.evname * evlisteners)>) = false *)
(* let ext_register_event_listener (f:(DataModel.event -> 'a -> 'a)) = false *)                    
