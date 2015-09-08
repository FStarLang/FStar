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
#monadic(DST, returnTX, bindTX)
module Auth
type pk
type sk
type dsig = bytes
type msg = string

logic data type event =
  | Good : string -> event
 
val log : ref (list event)

assume HeapInv_def: forall h. HeapInv h
assume DeltaHeap_def: forall h1 h2. 
  DeltaHeap h1 h2 (* <==> (forall x. In x (SelHeap h1 log) ==> In x (SelHeap h2 log)) *)

type Event :: _ = (fun (h:heap) (ev:event) => 
    (In ev (SelHeap h log)
    (* || (exists (h':heap). Witness h' && In ev (SelHeap h' log)) *)

))

val sign: sk -> m:msg -> iDST dsig (fun ('Post::result dsig => heap => E) h => 
    (Event h (Good m)
     && forall (x:dsig). 'Post (V x) h))
let sign sk m = (* some dummy impl of dsig *)
  pickle m
  
val verify: pk -> m:msg -> dsig -> iDST bool (fun ('Post::result bool => heap => E) h => 
    forall (x:bool). (x=true ==> Event h (Good m)) ==> 'Post (V x) h)
let verify pk m ds = (* dummy abstract impl of dsig ... just look in the log *)
  let l = !log in
    mem (Good m) l

val send: msg -> dsig -> unit
val recv: unit -> (msg * dsig) 

val client : sk -> iDST unit (fun ('Post::result unit => heap => E) h =>
    forall h'. 'Post (V ()) h')
let client privkey =
  let msg = "hello" in
  let _ = log := ((Good msg)::!log) in
  let _ = witness () in 
  let dsig = sign privkey msg in
    send msg dsig

val server: pk -> iDST msg (fun ('Post::result string => heap => E) h => 
    forall r. ResultIs r (fun (m:msg) => Event h (Good m))
    ==> 'Post r h)
let server client_pk =
  let (m,d) = recv () in
    if verify client_pk m d then m
    else raise (Exception "Bad message")
      
