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

module HealthDB

let parse_date (s:string) : (int*int*int) = (1, 2, 2010) 

type dbrec = {recid:int; 
              patient:string;
	      author:string; 
	      subject:string; 
              contents:string; 
              timestamp:string;}

let find_records_by_keyword (kw:string) : Prims.list<dbrec> = 
  (new Prims.Nil<dbrec>() :> Prims.list<dbrec>)
    
let persist_record: dbrec -> int = 
  fun x -> 0
    
let read_authstate: bool -> string = 
  fun x -> "Empty"

let general = new DataModel.General()
let psych = new DataModel.Psychiatric()
let hiv = new DataModel.HIV()
let other x = new DataModel.Other(x)

let parse_dbrec (r1:dbrec) : DataModel.record =
  let subj = match r1.subject with 
      "General" -> general :> DataModel.subject
    | "Psych" -> psych :> DataModel.subject
    | "HIV" -> hiv :> DataModel.subject
    | x -> other x :> DataModel.subject in
  let d,m,y = parse_date r1.timestamp in
  let rec_date = new DataModel.date(d, m, y) in
  let priv = new DataModel.Contents(rec_date, 
                                    r1.contents, 
                                    new Prims.Nil<DataModel.annotation>()) in 
    new DataModel.record(r1.recid, 
                         new Authentication.U(r1.patient), 
                         new Authentication.U(r1.author), 
                         subj, 
                         priv)
;;

let x = find_records_by_keyword "nothing" in 
let dbr = {recid=18; patient="Nik"; author="Doc"; 
           subject="Something";contents="This is some note.";
           timestamp="01-Feb-2010"} in
let record = parse_dbrec dbr in
  print_any record
