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
assume val weaken_squash (#a:prop) (#b:prop) ($ab:squash a -> Tot (squash b)) (sa:squash a) : Tot (squash b)
assume val weaken_and (#a:prop) (#b:prop) (#a':prop) (#b':prop) ($fa:(squash a -> squash a')) ($fb:(squash b -> squash b')) (ab:(a /\ b)) : (a' /\ b')
assume val weaken_forall (#a:Type) (#p:a -> GTot prop) (#p':a -> GTot prop) (fpp':(x:a -> squash (p x) -> squash (p' x))) (fp:(forall (x:a). p x)) : (forall (x:a). p' x)
assume val weaken_implies (#a:prop) (#b:prop) (#b':prop) ($fb:(squash b -> squash b')) (ab:(a ==> b)) : (a ==> b')

assume val gg : int -> prop
assume val gg1 : gg 1
assume val gg1_imp_gg2 : gg 1 -> gg 2

[@@expect_failure [66]]
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
