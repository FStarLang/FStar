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
module Bug1256

open FStar.Tactics.V2

let ddump m = if debugging () then dump m

let my_cut (t:term) : Tac unit =
    let qq = pack (Tv_FVar (pack_fv ["FStar";"Tactics";"V2";"Derived";"__cut"])) in
    let tt = pack (Tv_App qq (t, Q_Explicit)) in
    apply tt

assume val aug : (unit -> prop) -> prop

let test (p:(unit -> prop)) (q:(unit -> prop))
   = assert (p == q ==>
             aug p ==>
             aug q)
         by (let eq = implies_intro () in
             let h = implies_intro () in
             ddump "A";
             my_cut h.sort;
             ddump "B";
             rewrite eq;
             norm [];
             ddump "C";
             let hh = intro () in
             exact (pack (Tv_Var (binding_to_namedv hh)));
             ddump "D";
             exact (pack (Tv_Var (binding_to_namedv h))) )

[@@expect_failure]
let test2 (post:(unit -> Type0))
   = assert ((post ==  (fun x -> post ())) ==>
             aug post ==>
             aug (fun x -> post ()))
         by (let eq = implies_intro () in
             let h = implies_intro () in
             ddump "A";
             my_cut (type_of_binder h);
             ddump "B";
             rewrite eq;
             norm [];
             ddump "C";
             let hh = intro () in
             ())

let test3 (p:(unit -> prop)) (q:(unit -> prop))
   = assert (p == q ==> aug p ==> aug q)
         by (let eq = implies_intro () in
             let h = implies_intro () in
             ddump "A";
             my_cut h.sort;
             ddump "B";
             rewrite eq;
             norm [];
             ddump "C";
             let hh = intro () in
             ddump "D";
             exact (pack (Tv_Var (binding_to_namedv hh)));
             ddump "E";
             exact (pack (Tv_Var (binding_to_namedv h)))
             )

let test4 (post:(unit -> prop))
   = assert ((post ==  (fun x -> post ())) ==> aug post ==> aug (fun x -> post ()))
         by (let eq = implies_intro () in
             let h = implies_intro () in
             ddump "A";
             my_cut h.sort;
             ddump "B";
             rewrite eq;
             norm [];
             ddump "C";
             let hh = intro () in
             exact (pack (Tv_Var (binding_to_namedv hh)));
             exact (pack (Tv_Var (binding_to_namedv h)));
             ())
