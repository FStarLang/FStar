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

let _ = 
  let st = Facade.read_authstate false in
  let prin = (DataModel.U "Asclepius") :> DataModel.prin in
  let cred_opt = Authentication.login prin  "suipelcsA" in
    match cred_opt with
      | :? Prims.Some<DataModel.cred> ->
        let _ = print_any "Logged in!\n" in
        let cred = (cred_opt :?> Prims.Some<DataModel.cred>).field_1 in
        let request = new DataModel.GetRecordById(688) :> DataModel.request in
(*         let request = new DataModel.GetReadableRecords() :> DataModel.request in *)
        let response = HealthMgr.handle_req prin cred request in
          (match response with
             | :? DataModel.OneRecord ->
               let record = (response :?> DataModel.OneRecord).field_1 in
               let _ = Facade.print_record record in 
               let annots = Db.getAnnotations 688 in
                 Facade.print_annots annots
             | :? DataModel.Denied -> print_any "Request Denied"
             | _ -> print_any ("Unexpected response", response))
            (*         let recs = Db.findAuthoredRecords prin in  *)
            (*           Facade.print_records recs *)
      | _ -> print_any "Login failed :(\n"

(*   let r = new DataModel.ActiveRole(new DataModel.U("Asclepius"), new DataModel.Doctor()) :> DataModel.attribute in *)
(*   let s = new DataModel.ActiveRole(new DataModel.U("Asclepius"), new DataModel.Doctor()) :> DataModel.attribute in *)
(*   let p = new DataModel.U("Asclepius") :> DataModel.prin in *)
(*   let q = new DataModel.U("Asclepius") :> DataModel.prin in *)
(*     if r=s then *)
(*       print_any "Yes" *)
(*     else print_any "No" *)
          
          
