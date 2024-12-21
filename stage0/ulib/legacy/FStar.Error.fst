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
/// A library for optional results,
/// where the error case carries some payload
module FStar.Error

type optResult 'a 'b =
  | Error of 'a
  | Correct of 'b

/// allowing inverting optResult without having
/// to globally increase the fuel just for this
let invertOptResult (a:Type) (b:Type)
  : Lemma
    (requires True)
    (ensures (forall (x:optResult a b). Error? x \/ Correct? x))
    [SMTPat (optResult a b)]
  = allow_inversion (optResult a b)

irreducible
let perror
    (file:string)
    (line:int)
    (text:string)
  : Tot string
  = text

let correct
    (#a:Type)
    (#r:Type)
    (x:r)
  : Tot (optResult a r)
  = Correct x

(* Both unexpected and unreachable are aliases for failwith;
   they indicate code that should never be executed at runtime.
   This is verified by typing only for the unreachable function;
   this matters e.g. when dynamic errors are security-critical *)
let rec unexpected
    (#a:Type)
    (s:string)
   : Div a
     (requires True)
     (ensures (fun _ -> True))
   = let _ = FStar.IO.debug_print_string ("Platform.Error.unexpected: " ^ s) in
     unexpected s

let rec unreachable
    (#a:Type)
    (s:string)
   : Div a
     (requires False)
     (ensures (fun _ -> False))
   = let _ = FStar.IO.debug_print_string ("Platform.Error.unreachable: " ^ s) in
     unreachable s

irreducible
let if_ideal
    (f:unit -> Tot 'a)
    (x:'a)
  : Tot 'a
  = x
