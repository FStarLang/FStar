module Platform.Error

open FStar.Heap
open FStar.HyperHeap

type optResult 'a 'b =
    | Error of 'a
    | Correct of 'b

assume val perror: string -> int -> string -> Tot string

//assume val correct: #a:Type -> #b:Type -> x:a -> Tot (y:(optResult b a){y = Correct(x)})
assume val correct: #r:Type -> r -> Tot (optResult 'a r)

(* Both unexpected and unreachable are aliases for failwith;
   they indicate code that should never be executed at runtime.
   This is verified by typing only for the unreachable function;
   this matters e.g. when dynamic errors are security-critical *)

assume val unexpected: string -> ST 'a
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))

assume val unreachable: string -> ST 'a
  (requires (fun _ -> False))
  (ensures (fun _ _ _ -> False))

assume val if_ideal: (unit -> 'a) -> 'a -> 'a 
