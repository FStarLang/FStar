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
#monadic(DST.DST, DST.returnTX, DST.bindNoExnTX)
module Hello
open RefSet
open DST

val copy: r:ref int -> Writer (ref int)
                              (Requires (Permission r))
                              (Ensures _ (fun h s h' =>
                                    (StarH (Singleton r) (Singleton s) (Permission r) (Permission s) h'
                                     && (SelHeap h' s = SelHeap h r))))
                              (Modifies EmptySet)

let copy (r:ref int) = 
  let v = !r in 
  let s = ref v in 
    s

val swap: 'a::* -> r1:ref 'a -> r2:ref 'a -> Writer unit
                                            (Requires (fun h => (Permission r1 h && Permission r2 h)))
                                            (Ensures _ (fun h s h' => (Permission r1 h' && Permission r2 h'
                                                                       && (SelHeap h' r1 = SelHeap h r2)
                                                                       && (SelHeap h' r2 = SelHeap h r1))))
                                            (Modifies (Union (Singleton r1) (Singleton r2)))
let swap ('a::*) (r1:ref 'a) (r2:ref 'a) =
  let tmp = !r1 in 
  let _ = r1 := (!r2) in 
    r2 := tmp


val main: x:unit -> Writer unit TrivialPre (TrivialPost unit) (Modifies EmptySet)
let main () = 
  let x1 = ref 0 in 
  let x2 = ref 1 in 
  let _ = swap x1 x1 in
  let _ = swap x1 x2 in
  let tmp1 = !x1 in 
  let tmp2 = !x2 in 
  let _ = assert (tmp1 = 1) in
  let _ = assert (tmp2 = 0) in
    ()

