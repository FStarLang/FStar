module EEOT3

val rev : list 'a -> Tot (list 'a)
let rec rev l =
  match l with
  | []   -> []
  | h::t -> rev h

(* We get different error messages depending on whether the --verify flag is on:
Without --verify flag:
  typing-error-expected-expression-of-type3.fst(7,16-7,17) : Error
  Expected expression of type "(list ('U521 'a))";
  got expression "h" of type "'a"
With --verify flag:
  typing-error-expected-expression-of-type3.fst(7,16-7,17) : Error
  Expected expression of type "_7897:(list ('U528 'a)){(Precedes   (LexPair   _7897 LexTop) (LexPair   l LexTop))}";
  got expression "h" of type "'a"
*)

(* Here both the expected type and the actual type need normalization
Expected expression of type "
[Before:_7862:(list ('U532 'a)){(Precedes #((fun 'a:Type l:((fun 'a:Type => (list 'a)) 'a) 'a:Type _7862:(list 'a) => lex_t) 'a l ('U532 'a) _7862) #((fun 'a:Type l:((fun 'a:Type => (list 'a)) 'a) 'a:Type _7862:(list 'a) => lex_t) 'a l ('U532 'a) _7862) (LexPair #((fun 'a:Type 'a:Type => (list 'a)) 'a ('U532 'a)) #((fun 'a:Type 'a:Type => lex_t) 'a ('U532 'a)) _7862 LexTop) (LexPair #((fun 'a:Type 'a:Type => (list 'a)) 'a ('U532 'a)) #((fun 'a:Type 'a:Type => lex_t) 'a ('U532 'a)) l LexTop))}]
[After:_7862:(list ('U532 'a)){(Precedes #lex_t #lex_t (LexPair #(list ('U532 'a)) #lex_t _7862 LexTop) (LexPair #(list 'a) #lex_t l LexTop))}]";
got expression "h" of type "
[Before:((fun 'a:Type => ((fun 'a:Type => 'a) 'a)) 'a)]
[After:'a]"
*)
