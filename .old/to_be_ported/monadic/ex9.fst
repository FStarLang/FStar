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
#monadic(DST, returnDST, composeDST)
module Ex9

type counter = ref int

val new_counter : 'a::* 
               -> n:'a
               -> DST (ref 'a) (fun ('Post::ref 'a => heap => E) (h:heap) => 
                   (Forall (ref 'a) (fun (x:(ref 'a)) => 
                        ((Mem x (Domain h))=false => ('Post x (Update x n h))))))
let new_counter n =
  ref n

val inc : c:counter
       -> DST int (fun ('Post::int => heap => E) (h:heap) =>
           ((fun (z:unit) => (fun (h':heap) => ('Post (Select c h') h')))
              () (Update c (Add (Select c h) 1) h)))
let inc c =
  let _ = c := (!c + 1) in
    !c
      
val dec : c:counter
       -> DST int (fun ('Post::int => heap => E) (h:heap) =>
               ((fun (z:unit) => (fun (h':heap) => ('Post (Select c h') h')))
                 () (Update c (Sub (Select c h) 1) h)))
let dec c =
  let _ = c := (!c - 1) in
    !c

val peek : c:(ref 'a)
        -> DST 'a (fun ('Post::'a => heap => E) (h:heap) => ('Post (Select c h) h))
let peek c =
  !c

