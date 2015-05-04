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
// (c) Microsoft Corporation. All rights reserved

module Microsoft.FStar.Unionfind

type uvar 'a
assume val uvar_id: uvar<'a> -> int
assume val fresh : 'a -> uvar<'a>
assume val find : uvar<'a> -> 'a
assume val change : uvar<'a> -> 'a -> unit
assume val equivalent : uvar<'a> -> uvar<'a> -> Tot bool (* Cheating a bit? *)
assume val union : uvar<'a> -> uvar<'a> -> unit
