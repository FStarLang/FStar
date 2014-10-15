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
module Array
type nat = int
type arr :: * => *
type array 'a = ref (arr 'a)
logic function SizeOf : arr 'a -> nat
logic function Emp : nat -> 'a -> arr 'a
logic function ArrSel : nat -> arr 'a -> 'a
logic function ArrUpd : nat -> 'a -> arr 'a -> arr 'a
assume (forall (x:arr 'a) (n:nat) (v:'a). ((ArrSel n (ArrUpd n v x)) = v))
assume (forall (x:arr 'a) (n:nat) (m:nat) (v:'a). (not (m=n)) => ((ArrSel n (ArrUpd m v x)) = (ArrSel n x)))

val create: 'a::*
         -> 'Post::(array 'a => heap => E)
         -> n:nat
         -> ST (fun (H:heap) => (forall (x:array 'a) (a:arr 'a) (H':heap). 
                                   ((Mem x (Domain H) = false) && ((SizeOf a)=n) && (H'=(Update x a H))) => 'Post x H'))
               (array 'a)
               'Post

val init: 'a::*
       -> 'Post::(unit => heap => E)
       -> a:array 'a
       -> v:'a 
       -> ST (fun (H:heap) => (forall (b:arr 'a) (a1:arr 'a) (H':heap). 
                                 (a1=(Select a H)) && ((SizeOf b)=(SizeOf a1)) && (forall (i:nat). (ArrSel i b)=v) && (H'=(Update a b H))
                               => 'Post () H'))
              unit
             'Post

val get:  'a::*
       -> 'Post::('a => heap => E)
       -> a:array 'a
       -> i:nat
       -> ST (fun (H:heap) => (forall (a1:arr 'a) (v1:'a) (H':heap). (a1=(Select a H) && v1=(ArrSel i a1) => ((LT i (SizeOf a1)) && 'Post v1 H))))
            'a
            'Post

val set:  'a::* 
       -> 'Post::(unit => heap => E)
       -> a:array 'a
       -> i:nat
       -> v:'a
       -> ST (fun (H:heap) => (forall (a1:arr 'a) (a2:arr 'a) (H':heap). (a1=(Select a H)) && (a2=(ArrUpd i v a1)) && (H'=(Update a a2 H)) =>
                                ((LT i (SizeOf a1)) &&  
                                  (((SizeOf a2)=(SizeOf a1)) => 'Post () H'))))
             unit
            'Post
end 

module Test
open Array

val test : 'a::*
        -> 'Post :: (unit => heap => E)
        -> x:'a
        -> ST (fun (h:heap) => (True && (forall (y:unit) (h':heap). (True => 'Post y h')))) unit 'Post
let test x = 
  let a = Array.create 10 in 
  let b = Array.create 20 in
    Array.init a 0;
    Array.init b 0;
    Assert<(fun (H:heap) => ((ArrSel 5 (Select a H)) = 0)), _> ();
    Assert<(fun (H:heap) => ((ArrSel 7 (Select b H)) = 0)), _> ();
    Array.set a 5 1;
    Array.set b 7 2;
    Assert<(fun (H:heap) => ((ArrSel 5 (Select a H)) = 1)), _> ();
    Assert<(fun (H:heap) => ((ArrSel 7 (Select b H)) = 2)), _> ();
    Assert<(fun (H:heap) => ((ArrSel 0 (Select a H)) = 0)), _> ();
    Assert<(fun (H:heap) => ((ArrSel 0 (Select b H)) = 0)), _> ()

end

