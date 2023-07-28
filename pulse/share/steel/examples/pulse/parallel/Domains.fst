    module Domains
    
    open Pulse.Main
    open Pulse.Steel.Wrapper
    open Steel.Effect.Common
    
    assume val domain : a:Type0 -> (a -> vprop) -> Type0
    
    assume val spawn :
     (#a:Type0) -> (#pre : vprop) -> (#post : (a -> vprop)) ->
     ($f : (unit -> stt a pre post)) ->
     stt (domain a post) pre (fun _ -> emp)
    
    assume val join :
      (#a:Type0) -> (#post : (a -> vprop)) ->
      domain a post ->
      stt a emp post
    
    let rec fib0 (n:nat) : nat =
      if n < 2 then n
      else fib0 (n-1) + fib0 (n-2)
    
    let just #a (x:a) : stt a emp (fun _ -> emp) =
      sub_stt _ _ (magic()) (magic ()) (return_stt x (fun _ -> emp))
    
    ```pulse
    fn pth (n:pos) (_:unit)
      requires emp
      returns r:(r:nat{r == fib0 (n-1)})
      ensures emp
      // With this version:
      //    returns r:nat
      //    ensures pure (r == fib0 (n-1))
      // We get:
      //    cannot prove vprop pure (eq2 (fib0 (op_Subtraction n 1)) (fib0 (op_Subtraction n 1))) in the context: emp
      //    (the prover was started with goal pure (eq2 (fib0 (op_Subtraction n 1)) (fib0 (op_Subtraction n 1))) and initial context emp)
    {
      fib0 (n-1)
    }
    ```
    
    ```pulse
    fn pfib (n:nat)
      requires emp
      returns r:(r:nat{r == fib0 n})
      ensures emp
    {
      if (n < 20) {
        fib0 n
      } else {
        let r_th = spawn (pth n);
        let l = fib0 (n-2);
        let r = join r_th;
        let res = l+r;
        res
      }
    }
    ```