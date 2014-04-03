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
module NextFragment

type IsEmpty :: int => E
type StreamRead :: int => int => E
logic function App : int -> int -> int

type option :: * => * =
  | None : option int
  | Some : int -> option int

val is_empty_stream: 'Post::(bool => heap => E)
  -> s:(int)
  -> ST (fun (h:heap) => (forall (b:bool). 
          ((((b=true) => IsEmpty s)
          && ((b=false) => not(IsEmpty s)))
          => ('Post b h))))
        bool
        'Post

(*
val stream_read: 'Post::(int => heap => E)
  -> s:(ref int)
  -> l:int
  -> ST (fun (h:heap) =>
          forall (f:int).  (StreamRead s f => 'Post f (Update s (App (Select s h) f) h)))
        int
        'Post
*)

val stream_read: 'Post::((int*int) => heap => E)
  -> s:int
  -> l:int
  -> ST (fun (h:heap) =>
          forall (r:(int*int)).
            ((exists (f:int) (rem:int). 
              (r=(f,rem)) && StreamRead s f) => 'Post r h))
        (int*int)
        'Post


val next_fragment: 'Post::(option int => heap => E)
  -> l:int
  -> out:(ref int)
  -> ST (fun (h:heap) => 
          ((IsEmpty (Select out h)) => 'Post None h)
          && (not(IsEmpty (Select out h)) => (forall (fopt:option int). exists (f:int). (fopt=(Some f)) && StreamRead (Select out h) f => 'Post fopt (Update out (App (Select out h) f) h))))
        (option int)
        'Post

(*
let next_fragment l out =
  if (is_empty_stream (!out)) 
  then 0
  else stream_read out l
*)

let next_fragment l out =
  if (is_empty_stream (!out)) 
  then None
  else 
    let f, rem = stream_read (!out) l in
    let _ = out := rem in
      Some f

