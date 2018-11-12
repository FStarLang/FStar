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
module Bug331Index

type list1 (a:Type) : bool -> Type =
  | Nil1 : list1 a false
  | Cons1: hd:a -> tl:list2 a -> list1 a true
and list2 (a:Type) =
  | List: #b:bool ->
           v:list1 a b ->
           list2 a
