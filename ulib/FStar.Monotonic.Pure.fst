(*
   Copyright 2019 Microsoft Research

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

module FStar.Monotonic.Pure

#push-options "--warn_error -271"
let wp_monotonic_pure (_:unit)
  : Lemma
    (forall (a:Type) (wp:pure_wp a). (forall (p q:pure_post a).
       (forall (x:a). p x ==> q x) ==> (wp p ==> wp q)))
  = let aux (a:Type)
      : Lemma (forall (wp:pure_wp a). (forall (p q:pure_post a).
                                    (forall (x:a). p x ==> q x) ==> (wp p ==> wp q)))
        [SMTPat ()]
      = reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic #a) in
    ()
#pop-options
