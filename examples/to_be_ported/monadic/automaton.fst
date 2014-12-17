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
#monadic(DST, returnTX, bindNoExnTX)
(* Checking a dynamically tagged type-state property on a file API *)

module File 

(* primitive ops on file *)  
type file 
val system_file_open: string -> file
val system_file_read: file -> string
val system_file_close: file -> unit

type state =
  | FileOpen : state
  | FileClosed : state
      
logic data type sfile = 
  | SFile : file  -> ref state -> sfile
    
type InState :: _ = fun (st:state) (f:sfile) (h:heap) => (EqTyp (TypeOf (SFile_proj_1 f)) (ref state)
                                                          && InHeap h (SFile_proj_1 f)
                                                          && (st = SelHeap h (SFile_proj_1 f)))

val fopen: string -> Ensures sfile (fun h sf h' => 
    ((not(InHeap h (SFile_proj_1 sf))) && 
        SFile_is sf &&
        Modifies (SFile_proj_1 sf) h h' &&
        InState FileOpen sf h'))
let fopen fn =
  let f = system_file_open fn in
  let s = ref FileOpen in 
    (SFile f s)
          
val fread: f:sfile -> ReqEns string (InState FileOpen f) (fun h s h' => (h=h'))
let fread sf = match sf with 
  | SFile f s -> system_file_read f 
 
val fclose: sf:sfile -> ReqEns unit (InState FileOpen sf) (fun h u h' => 
    ((Modifies (SFile_proj_1 sf) h h')
     && InState FileClosed sf h'))
let fclose sf = match sf with 
  | SFile f s -> 
      let _ = system_file_close f in 
        s := FileClosed

val client: unit -> D unit
let client (x:unit) = 
  let f = fopen "foo.txt" in 
  let g = fopen "bar.txt" in
  let s = fread f in
  let _ = fclose f in
  let s = fread g in
  let s' = fread g in
    fclose g
