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
