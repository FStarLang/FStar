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

/// This module provides a refinement of FStar.IFC providing an
/// interface restricted only to constant-time operations on integers.
///
/// In contrast, FStar.IFC provides a general monadic information-flow
/// control framework, which need not be restricted to constant-time
/// operations.

open FStar.IFC
open FStar.Integers


(** `sw`: signedness and width of machine integers excluding
      FStar.[U]Int128, which does not provide constant-time
      operations. *)
let sw = s:signed_width{width_of_sw s <> Winfinite
      /\ width_of_sw s <> W128}

(** A `secret_int l s` is a machine-integer at secrecy level `l` and
    signedness/width `s`. *)
val secret_int (#sl:sl u#c)
               (l:lattice_element sl)
               (s:sw) : Type0

(** A `secret_int l s` can be seen as an int in spec *)
val reveal (#sl:sl)
           (#l:lattice_element sl)
           (#s:sw)
           (x:secret_int l s)
   : GTot (y:int{within_bounds s y})

(** A `secret_int l s` can be also be seen as an machine integer in spec *)
let m #sl (#t:lattice_element sl) #s (x:secret_int t s)
  : GTot (int_t s)
  = u (reveal x)

(** `hide` is the inverse of `reveal`, proving that `secret_int` is injective *)
val hide (#sl:sl)
         (#l:lattice_element sl)
         (#s:sw)
         (x:int{within_bounds s x})
  : GTot (secret_int l s)

val reveal_hide (#sl:sl)
                (#l:lattice_element sl)
                (#s:sw)
                (x:int{within_bounds s x})
  : Lemma (reveal (hide #sl #l #s x) == x)

val hide_reveal (#sl:sl)
                (#l:lattice_element sl)
                (#s:sw)
                (x:secret_int l s)
  : Lemma (hide (reveal x) == x)
          [SMTPat (reveal x)]

(** `promote x l` allows increasing the confidentiality classification of `x`
  This can easily be programmed using the FStar.IFC interface *)
val promote (#sl:sl)
            (#l0:lattice_element sl)
            (#s:sw)
            (x:secret_int l0 s)
            (l1:lattice_element sl)
  : Tot (y:secret_int (l1 `lub` l0) s{reveal y == reveal x})

/// The remainder of this module provides liftings of specific
/// integers operations to work on secret integers, i.e., only those
/// that respect the constant time guarantees and do not break
/// confidentiality.
///
/// Note, with our choice of representation, it is impossible to
/// implement functions that break basic IFC guarantees, e.g., we
/// cannot implement a boolean comparison function on secret_ints

(** Bounds-respecting addition *)
noextract
inline_for_extraction
val addition (#sl:sl)
             (#l:lattice_element sl)
             (#s:sw)
             (x : secret_int l s)
             (y : secret_int l s {ok ( + ) (m x) (m y)})
    : Tot (z:secret_int l s{m z == m x + m y})

(** Addition modulo *)
noextract
inline_for_extraction
val addition_mod (#sl:sl)
                 (#l:lattice_element sl)
                 (#sw: _ {Unsigned? sw /\ width_of_sw sw <> W128})
                 (x : secret_int l sw)
                 (y : secret_int l sw)
    : Tot (z:secret_int l sw { m z == m x +% m y } )

/// If we like this style, I will proceed to implement a lifting of
/// the rest of the constant-time integers over secret integers


/// Now, a multiplexing layer to overload operators over int_t and secret_int

(** A type of qualifiers, distinguishing secret and public integers *)
noeq
type qual =
  | Secret: #sl:sl
          -> l:lattice_element sl
          -> sw:sw
          -> qual
  | Public: sw:signed_width
          -> qual

(** The signedness and width of a qualifier *)
[@@mark_for_norm]
unfold
let sw_qual = function
  | Secret _ sw -> sw
  | Public sw -> sw

(** The lattice element of a secret qualifier *)
[@@mark_for_norm]
unfold
let label_qual (q:qual{Secret? q}) : lattice_element (Secret?.sl q) =
  match q with
  | Secret l _ -> l

(** The type corresponding to a qualifier, either an integer or a secret integer *)
[@@mark_for_norm]
unfold
let t (q:qual) =
  match q with
  | Secret l s -> secret_int l s
  | Public s -> int_t s

[@@mark_for_norm]
unfold
let i (#q:qual) (x:t q) : GTot (int_t (sw_qual q)) =
  match q with
  | Public s -> x
  | Secret l s -> m (x <: secret_int l s)

[@@mark_for_norm]
unfold
let as_secret (#q:qual{Secret? q}) (x:t q)
  : secret_int (label_qual q) (sw_qual q)
  = x

[@@mark_for_norm]
unfold
let as_public (#q:qual{Public? q}) (x:t q)
  : int_t (sw_qual q)
  = x

(** Lifting addition to work over both secret and public integers *)
[@@mark_for_norm]
unfold
noextract
inline_for_extraction
let ( + ) (#q:qual) (x:t q) (y:t q{ok (+) (i x) (i y)})
    : Tot (t q)
    = match q with
      | Public s -> as_public x + as_public y
      | Secret l s -> as_secret x `addition` as_secret y

(** Lifting addition modulo to work over both secret and public integers *)
[@@mark_for_norm]
unfold
noextract
inline_for_extraction
let ( +% ) (#q:qual{norm (Unsigned? (sw_qual q) /\ width_of_sw (sw_qual q) <> W128)})
           (x:t q)
           (y:t q)
    : Tot (t q)
    = match q with
      | Public s -> as_public x +% as_public y
      | Secret l s -> as_secret x `addition_mod` as_secret y

(**** See src/tests/microbenchmarks/Test.ConstantTimeIntegers.fst for some unit tests *)

