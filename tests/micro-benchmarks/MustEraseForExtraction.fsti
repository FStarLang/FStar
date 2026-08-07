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
module MustEraseForExtraction

(* An informative type, declared without the `erasable` attribute. *)
val t1 : Type0

(* A non-informative type, declared as erasable. The negative cases --- a
   definition that is erasable behind a declaration that is not, and vice
   versa --- are in tests/interfaces/IfaceMustErase, since they are diagnosed
   against the interface's `val` and so cannot be wrapped in an
   [@@expect_failure] here: such a block defines nothing, and the declaration
   would be left unimplemented. *)
[@@erasable]
val t2 : Type0
