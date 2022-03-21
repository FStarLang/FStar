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
module EEOT

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | _::_ -> (1 + length)

(* We get different error messages depending on whether the --verify flag is on:
Without --verify flag:
  typing-error-expected-expression-of-type.fst(7,17-7,23) : Error
  Expected expression of type "int";
  got expression "(length )" of type "(_:(list ('U520 'a)) -> Tot nat)"
With --verify flag:
  typing-error-expected-expression-of-type.fst(7,17-7,23) : Error
  Expected expression of type "int";
  got expression "(length )" of type "(_:_7896:(list ('U527 'a)){(Precedes   (LexPair   _7896 LexTop) (LexPair   l LexTop))} -> Tot nat)"

(* Here is what we get with the --print_implicits flag (before and after normalization)

Expected expression of type "[Before:int][After:int]";
got expression "(length #('U531 'a))" of type
"[Before:(_:_7861:(list ('U531 'a)){(Precedes #((fun 'a:Type l:((fun 'a:Type => (list 'a)) 'a) 'a:Type _7861:(list 'a) => lex_t) 'a l ('U531 'a) _7861) #((fun 'a:Type l:((fun 'a:Type => (list 'a)) 'a) 'a:Type _7861:(list 'a) => lex_t) 'a l ('U531 'a) _7861) (LexPair #((fun 'a:Type 'a:Type => (list 'a)) 'a ('U531 'a)) #((fun 'a:Type 'a:Type => lex_t) 'a ('U531 'a)) _7861 LexTop) (LexPair #((fun 'a:Type 'a:Type => (list 'a)) 'a ('U531 'a)) #((fun 'a:Type 'a:Type => lex_t) 'a ('U531 'a)) l LexTop))} -> Tot nat)]
[After:(_:_7861:(list ('U531 'a)){(Precedes #lex_t #lex_t (LexPair #(list ('U531 'a)) #lex_t _7861 LexTop) (LexPair #(list 'a) #lex_t l LexTop))} -> Tot nat)]"
*)
