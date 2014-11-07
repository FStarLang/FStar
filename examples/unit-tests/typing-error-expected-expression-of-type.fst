module EEOT

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | _::_ -> (1 + length)

(* Should still make implicits go away

Expected expression of type "[Before:int][After:int]";
got expression "(length #('U531 'a))" of type
"[Before:(_:_7861:(list ('U531 'a)){(Precedes #((fun 'a:Type l:((fun 'a:Type => (list 'a)) 'a) 'a:Type _7861:(list 'a) => lex_t) 'a l ('U531 'a) _7861) #((fun 'a:Type l:((fun 'a:Type => (list 'a)) 'a) 'a:Type _7861:(list 'a) => lex_t) 'a l ('U531 'a) _7861) (LexPair #((fun 'a:Type 'a:Type => (list 'a)) 'a ('U531 'a)) #((fun 'a:Type 'a:Type => lex_t) 'a ('U531 'a)) _7861 LexTop) (LexPair #((fun 'a:Type 'a:Type => (list 'a)) 'a ('U531 'a)) #((fun 'a:Type 'a:Type => lex_t) 'a ('U531 'a)) l LexTop))} -> Tot nat)]
[After:(_:_7861:(list ('U531 'a)){(Precedes #lex_t #lex_t (LexPair #(list ('U531 'a)) #lex_t _7861 LexTop) (LexPair #(list 'a) #lex_t l LexTop))} -> Tot nat)]"
*)
