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
module Array1
type pos = i:int{(GT i 0)}
type arr :: * => *
type array 'a = ref (arr 'a)
logic val SizeOf : arr 'a -> int
logic val Emp : int -> 'a -> arr 'a
logic val ArrSel : int -> arr 'a -> 'a
logic val ArrUpd : int -> 'a -> arr 'a -> arr 'a
assume (forall (x:arr 'a) (n:pos) (v:'a). ((ArrSel n (ArrUpd n v x)) = v))
assume (forall (x:arr 'a) (n:pos) (m:pos) (v:'a). (not (m=n)) => ((ArrSel n (ArrUpd m v x)) = (ArrSel n x)))

val create: n:pos
  -> DST (array 'a) (fun ('Post::(array 'a => heap => E)) (H:heap) => (forall (x:array 'a) (a:arr 'a). 
                                                                         ((Mem x (Domain H) = false) && ((SizeOf a)=n)) => 'Post x (Update x a H)))
               

val init: a:array 'a
       -> v:'a 
       -> DST unit (fun ('Post::(unit => heap => E)) (H:heap) => (forall (b:arr 'a). 
                                 ((SizeOf b)=(SizeOf (Select a H))) && (forall (i:pos). (ArrSel i b)=v)
                               => 'Post () (Update a b H)))

val get:  a:array 'a
       -> i:pos
       -> DST 'a (fun ('Post::('a => heap => E)) (H:heap) => ((LT i (SizeOf (Select a H))) && 'Post (ArrSel i (Select a H)) H))

val set:  a:array 'a
       -> i:pos
       -> v:'a
       -> DST unit (fun ('Post::(unit => heap => E)) (H:heap) => ((LT i (SizeOf (Select a H))) &&  
                                                                    (((SizeOf (ArrUpd i v (Select a H)))=(SizeOf (Select a H))) => 'Post () (Update a (ArrUpd i v (Select a H)) H))))
end 

module Test1
open Array1

val test : x:'a
        -> DST unit (fun ('Post :: (unit => heap => E)) (h:heap) => (True && (forall (y:unit) (h':heap). (True => 'Post y h')))) 
let test x = 
  (* let c = Array.create<int, _> 0 in *) (* Should fail *)
  let a = Array1.create 10 in 
  let b = Array1.create<int> 20 in
    Array1.init a 0;
    Array1.init b 0;
    Assert<(fun (H:heap) => ((ArrSel 5 (Select a H)) = 0))> ();
    Assert<(fun (H:heap) => ((ArrSel 7 (Select b H)) = 0))> ();
    Array1.set a 5 1;
    Array1.set b 7 2;
    Assert<(fun (H:heap) => ((ArrSel 5 (Select a H)) = 1))> ();
    Assert<(fun (H:heap) => ((ArrSel 7 (Select b H)) = 2))> ();
    Assert<(fun (H:heap) => ((ArrSel 1 (Select a H)) = 0))> ();
    Assert<(fun (H:heap) => ((ArrSel 1 (Select b H)) = 0))> () 

end

