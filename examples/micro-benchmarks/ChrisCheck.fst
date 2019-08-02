(*
   Copyright 2008-2018 Microsoft Research

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
module ChrisCheck
//An example from Chris Hawblitzel
//Used to run out of memory prior to F* 0.9.6
assume val identity (#a:Type) (x:a) : a
assume val weaken_squash (#a:Type) (#b:Type) ($ab:a -> Tot b) (sa:squash a) : Tot (squash b)
assume val weaken_and (#a:Type) (#b:Type) (#a':Type) (#b':Type) ($fa:(a -> a')) ($fb:(b -> b')) (ab:(a /\ b)) : (a' /\ b')
assume val weaken_forall (#a:Type) (#p:a -> GTot Type0) (#p':a -> GTot Type0) (fpp':(x:a -> p x -> p' x)) (fp:(forall (x:a). p x)) : (forall (x:a). p' x)
assume val weaken_implies (#a:Type) (#b:Type) (#b':Type) ($fb:(b -> b')) (ab:(a ==> b)) : (a ==> b')

assume val gg : int -> Type0
assume val gg1 : gg 1
assume val gg1_imp_gg2 : gg 1 -> gg 2

let foo () =
  (weaken_squash (weaken_forall (fun p -> weaken_implies (weaken_forall (fun x -> weaken_implies
       (weaken_implies (weaken_forall (fun y -> weaken_implies (weaken_forall (fun k -> weaken_implies
            (weaken_forall (fun b -> weaken_forall (fun b -> weaken_implies (weaken_forall (fun x ->
                 weaken_implies (weaken_implies (weaken_forall (fun y -> weaken_implies (weaken_forall (fun k -> weaken_implies
                      (weaken_forall (fun b -> weaken_forall (fun b -> weaken_implies (weaken_forall (fun x ->
                           weaken_implies (weaken_implies (weaken_forall (fun y -> weaken_implies (weaken_forall (fun k -> weaken_implies
                                (weaken_forall (fun b -> weaken_forall (fun b -> weaken_implies (weaken_forall (fun x ->
                                     weaken_implies (weaken_implies (weaken_forall (fun y -> weaken_implies (weaken_forall (fun k -> weaken_implies
                                          (weaken_forall (fun b -> weaken_forall (fun b -> weaken_implies (weaken_forall (fun x ->
                                               weaken_implies (weaken_implies (weaken_forall (fun y -> weaken_implies (weaken_forall (fun k -> weaken_implies
                                                    (weaken_forall (fun b -> weaken_forall (fun b -> weaken_implies (weaken_forall (fun x ->
                                                         weaken_implies (weaken_implies (weaken_forall (fun y -> weaken_implies (weaken_forall (fun k -> weaken_implies
                                                              (weaken_forall (fun b -> weaken_forall (fun b -> weaken_implies (weaken_and identity (weaken_forall
                                                                   (fun x -> weaken_implies (weaken_and (weaken_and identity gg1_imp_gg2) (weaken_forall (fun x ->
                                                                       weaken_implies (weaken_forall (fun x -> identity)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
