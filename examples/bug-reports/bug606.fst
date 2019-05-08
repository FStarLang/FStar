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
module Bug606

////////////////////////////////////////////////////////////////////////////////
//minimalistic
////////////////////////////////////////////////////////////////////////////////
let t (a:nat) = int
let test (x:t 0) : t 1 = x


////////////////////////////////////////////////////////////////////////////////
//Testing for the absence of unification loops
////////////////////////////////////////////////////////////////////////////////
type list (t:Type) = l:list t

let rec f (x:list bool) =
  match x with
  | [] -> nat
  | _::tl -> list (f tl)

let rec g (x:list bool) =
  match x with
  | [] -> nat
  | _::tl -> list (g tl)

let rec f_eq_g (l:list bool)
  : Lemma (ensures (f l == g l))
          [SMTPat (f l)]
  = match l with
    | [] -> ()
    | _::tl -> f_eq_g tl

let h (l:list bool) (x:list (f l)) : list (g l) = x

////////////////////////////////////////////////////////////////////////////////
//A slightly larger example
////////////////////////////////////////////////////////////////////////////////
open FStar.UInt

#set-options "--print_universes --log_types"

(*
//  In FStar.UInt:
//  type uint_t (n:pos) = x:int{size x n}

//  In FStar.UInt64:
//  val v        : t -> Tot (uint_t n)
//  val uint_to_t: uint_t n -> Pure t
//  *)

let n:pos = 32

val uint64_to_uint32: m:UInt64.t{fits (UInt64.v m) n} -> Tot FStar.UInt32.t
let uint64_to_uint32 m =
  let m': x:int{size x n} = UInt64.v m in
  UInt32.uint_to_t m'

//With this uncommented, uint64_to_uint32' below typechecks
//type uint_t (n:pos) = x:int{size x n}

val uint64_to_uint32': m:UInt64.t{fits (UInt64.v m) n} -> Tot FStar.UInt32.t
let uint64_to_uint32' m =
  cut (uint_t n == x:int{size x n});
  cut (forall (p:uint_t n). p:(x:int{size x n}));
  let m':uint_t n = UInt64.v m in // This fails, even if the above is provable
  UInt32.uint_to_t m'
