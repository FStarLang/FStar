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
module FStar.Reflection.V2.Compare

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Order

[@@plugin]
val compare_name (n1 n2 : name) : order

[@@plugin]
val compare_fv (f1 f2 : fv) : order

[@@plugin]
val compare_const (c1 c2 : vconst) : order

[@@plugin]
val compare_ident (i1 i2:ident) : order

[@@plugin]
val compare_universe (u1 u2:universe) : order

[@@plugin]
val compare_universes (us1 us2:universes) : order

[@@plugin]
val compare_term (s t : term) : order

[@@plugin]
val compare_comp (c1 c2 : comp) : order

[@@plugin]
val compare_binder (b1 b2 : binder) : order
