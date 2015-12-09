module Platform.Error

type optResult 'a 'b =
    | Error of 'a
    | Correct of 'b

assume val perror: string -> int -> string -> Tot string

//assume val correct: #a:Type -> #b:Type -> x:a -> Tot (y:(optResult b a){y = Correct(x)})
assume val correct: #a:Type -> a -> Tot (optResult 'b a)

(* Both unexpected and unreachable are aliases for failwith;
   they indicate code that should never be executed at runtime.
   This is verified by typing only for the unreachable function;
   this matters e.g. when dynamic errors are security-critical *)

(*@ assume val unexpected: string -> 'a {false} @*)
assume val unexpected: string -> 'a

(*@ assume val unreachable: string {false} -> 'a @*)
assume val unreachable: string -> 'a


assume val if_ideal: (unit -> 'a) -> 'a -> 'a 
