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
module OneTimePad

open Bijection
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 4 --max_ifuel 4"
let nib = bool * bool * bool * bool
let xor_b (b1:bool) (b2:bool) = b1 <> b2
let xor (a, b, c, d) (w, x, y, z) = (a `xor_b` w,  b `xor_b` x, c `xor_b` y, d `xor_b` z)
let xor_properties (x:nib) (y:nib) =
  assert (x `xor` y = y `xor` x);
  assert (y `xor` (x `xor` y) = x);
  assert (x `xor` (x `xor` y) = y);
  assert ((x `xor` y) `xor` y = x)

type tape = int -> Tot nib
type random (a:Type) = (int * (int -> Tot nib)) -> M (a * int)
let return (a:Type) (x:a) : random a = fun s -> (x, fst s)
let bind (a b : Type) (x:random a) (f: a -> random b)
  : random b
= fun store ->
    let (z, n) = x store in
    f z (n, snd store)
let rand () : random nib = fun store ->
  let n, tape = store in
  tape n, n + 1

total reifiable reflectable new_effect {
  RANDOM : a:Type -> Effect
  with repr   = random
    ; bind   = bind
    ; return = return
    ; rand = rand
}

effect Rand (a:Type) =
  RANDOM a (fun initial_tape post -> forall (x:(a * int)). post x)


let one_time_pad () : Rand ((nib -> nib) * (nib -> nib)) =
  let key = RANDOM?.rand () in
  let encrypt (msg:nib) = msg `xor` key in
  let decrypt (cipher:nib) = cipher `xor` key in
  encrypt, decrypt

let related_tape (b:int -> bij) (t_0 t_1:tape) = forall i. b i (t_0 i) = (t_1 i)
let id_nib (x:nib) = x
let xor_at (pos:int) (x : nib) (i:int) : bij = if i = pos then xor x else id_nib

let one_time_pad_ok x_0 x_1 tape_0 tape_1
    : Lemma (requires (related_tape (xor_at 0 (x_0 `xor` x_1)) tape_0 tape_1))
            (ensures (let (enc_0, dec_0), _ = reify (one_time_pad ()) (0, tape_0) in
                      let (enc_1, dec_1), _ = reify (one_time_pad ()) (0, tape_1) in
                      dec_0 (enc_0 x_0) = x_0 /\
                      dec_1 (enc_1 x_1) = x_1 /\
                      enc_0 x_0 = enc_1 x_1))
= ()

