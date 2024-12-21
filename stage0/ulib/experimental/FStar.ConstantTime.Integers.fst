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
module FStar.ConstantTime.Integers

(** 
    This module provides a refinement of FStar.IFC providing an
    interface restricted only to constant-time operations on integers.
    
    In contrast, FStar.IFC provides a general monadic information-flow
    control framework, which need not be restricted to constant-time
    operations. 
*)
    
open FStar.IFC
open FStar.Integers

/// A `secret_int l s` is a machine-integer at secrecy level `l` and
/// signedness/width `s`.
let secret_int (#sl:sl)
               (l:lattice_element sl)
               (s:sw) : Type0 =
    protected l (int_t s)

/// A `secret_int l s` can be seen as an int in spec
let reveal (#sl:sl)
           (#l:lattice_element sl)
           (#s:sw)
           (x:secret_int l s)
   : GTot (y:int{within_bounds s y})
   = v (reveal x)

/// `hide` is the inverse of `reveal`, proving that `secret_int` is injective
let hide (#sl:sl) (#l:lattice_element sl) (#s:sw) (x:int{within_bounds s x})
  : GTot (secret_int l s)
  = return l (u x)

let reveal_hide #sl #l #s x = ()
let hide_reveal #sl #l #s x = ()

let promote #sl #l0 #s x l1 =  
    join (return #_ #(secret_int l0 s) l1 x)

//////////////////////////////////////////////////////////////////////////////////////////
/// The remainder of this module provides liftings of specific integers operations
/// to work on secret integers, i.e., only those that respect the constant time guarantees
/// and do not break confidentiality.
///
/// Note, with our choice of representation, it is impossible to
/// implement functions that break basic IFC guarantees, e.g., we
/// cannot implement a boolean comparison function on secret_ints
noextract
inline_for_extraction
let addition #sl (#l:lattice_element sl) #s
             (x : secret_int l s)
             (y : secret_int l s {ok ( + ) (m x) (m y)})
    : Tot (z:secret_int l s{m z == m x + m y})
    = let>> a = x in
      let>> b = y in
      return l (a + b)

noextract
inline_for_extraction
let addition_mod (#sl:sl)
                 (#l:lattice_element sl)
                 (#sw: _ {Unsigned? sw /\ width_of_sw sw <> W128})
                 (x : secret_int l sw)
                 (y : secret_int l sw)
    : Tot (z:secret_int l sw { m z == m x +% m y } )
    = let>> a = x in
      let>> b = y in
      return l (a +% b)
