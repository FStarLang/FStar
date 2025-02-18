(*
   Copyright 2023 Microsoft Research

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

module Pulse.Typing.FV
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let mem_intension_pat (#a:eqtype) (x:a) (f:(a -> Tot bool))
  : Lemma
    (ensures FStar.Set.(mem x (intension f) = f x))
    [SMTPat FStar.Set.(mem x (intension f))]
  = Set.mem_intension x f

let contains (g:env) (x:var) = Some? (lookup g x)
let vars_of_env (g:env) = dom g

let set_minus (#a:eqtype) (s:Set.set a) (x:a) =
  Set.intersect s (Set.complement (Set.singleton x))

val freevars_close_term (e:term) (x:var) (i:index)
  : Lemma 
    (ensures freevars (close_term' e x i) ==
             freevars e `set_minus` x)
    [SMTPat (freevars (close_term' e x i))]

val freevars_close_st_term (e:st_term) (x:var) (i:index)
  : Lemma 
    (ensures freevars_st (close_st_term' e x i) ==
             freevars_st e `set_minus` x)
    [SMTPat (freevars_st (close_st_term' e x i))]

val tot_typing_freevars (#g:_) (#t:_) (#ty:_)
                        (d:tot_typing g t ty)
  : Lemma 
      (ensures freevars t `Set.subset` vars_of_env g /\
               freevars ty `Set.subset` vars_of_env g)

val comp_typing_freevars  (#g:_) (#c:_) (#u:_)
                          (d:comp_typing g c u)
  : Lemma 
      (ensures freevars_comp c `Set.subset` vars_of_env g)

val st_typing_freevars (#g:_) (#t:_) (#c:_)
                       (d:st_typing g t c)
  : Lemma 
    (ensures freevars_st t `Set.subset` vars_of_env g /\
             freevars_comp c `Set.subset` vars_of_env g)


let st_typing_freevars_inv (#g:_) (#t:_) (#c:_)
                           (d:st_typing g t c)
                           (x:var)
  : Lemma 
    (requires None? (lookup g x))
    (ensures ~(x `Set.mem` freevars_st t) /\
             ~(x `Set.mem` freevars_comp c))
  = st_typing_freevars d
