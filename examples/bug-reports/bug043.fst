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
module Bug043

type nat =
  | O : nat
  | S : nat -> nat

type env = int -> Tot (option nat)

assume val f : e:nat -> Tot bool

val free_in_context : e:nat -> g:env -> Pure unit
      (requires True)
      (ensures (Some? (g 42)))
let rec free_in_context e g =
  match e with
  | S n' -> free_in_context n' g

(*
fstar.exe bug43.fst
bug43.fst(11,31-11,32) : Error
Expected a function;
got an expression of type "_7894:(_:int -> Tot (option nat)){(Precedes #lex_t #lex_t (LexPair #nat #lex_t e (LexPair #(_:int -> Tot (option nat)) #lex_t _7894 LexTop)) (LexPair #nat #lex_t e (LexPair #(_:int -> Tot (option nat)) #lex_t g LexTop)))}"
*)
