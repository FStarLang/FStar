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
module FStar.BaseTypes

(* When reading the F* sources as an F* program, you need to open BaseTypes to
 * get types such as int8 or int32. When reading the F* sources as an F#
 * program, you don't need to do this because these types already defined by F#.
 * (for an example see prettyprint/prettyprint.fsi which uses float)
 * *)

