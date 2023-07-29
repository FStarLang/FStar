module Domains

open Pulse.Main
open Pulse.Steel.Wrapper
open Steel.Effect.Common

assume val domain : a:Type0 -> (a -> vprop) -> Type0

assume val joinable :
  #a:Type0 -> #post:(a -> vprop) ->
  domain a post -> vprop

assume val spawn :
 (#a:Type0) -> (#pre : vprop) -> (#post : (a -> vprop)) ->
 ($f : (unit -> stt a pre post)) ->
 stt (domain a post) pre (fun dom -> joinable dom)

assume val join :
  (#a:Type0) -> (#post : (a -> vprop)) ->
  d:domain a post ->
  stt a (joinable d) post
  
assume val in_parallel_section : vprop

val begin_par_block :
  #a:_ -> #pre:_ -> #post:_ ->
  n:nat ->
  (unit -> stt a (in_parallel_section `star` pre) post) ->
  // ^ can maybe take a "blockid" identfying the thread pool?
  // not now at least, since we won't have unscoped sections yet
  stt a pre post

  // begin_par_block 16 (fun () ->
  //   let th1 = spawn(..) in
  //   let th2 = spawn(..) in  
  //   join th1 + join th2
  // )

let rec fib0 (n:nat) : nat =
  if n < 2 then n
  else fib0 (n-1) + fib0 (n-2)

// ```pulse
// fn pth (n:pos) (_:unit)
//   requires emp
//   returns r:(r:nat{r == fib0 (n-1)})
//   ensures emp

//   // With this version:
//   //    returns r:nat
//   //    ensures pure (r == fib0 (n-1))
//   // We get:
//   //    cannot prove vprop pure (eq2 (fib0 (op_Subtraction n 1)) (fib0 (op_Subtraction n 1))) in the context: emp
//   //    (the prover was started with goal pure (eq2 (fib0 (op_Subtraction n 1)) (fib0 (op_Subtraction n 1))) and initial context emp)
// {
//   let r = fib0 (n-1);
//   r
// }
// ```

```pulse
fn sfib (n:nat)
  requires emp
  returns r:(r:nat{r == fib0 n})
  ensures emp
{
  admit()
}
```

```pulse
fn pfib (n:nat)
  (cb : (n:nat -> stt (r:nat{r == fib0 n}) emp (fun _ -> emp))) // callback as we don't have recursion
  requires emp
  returns r:(r:nat{r == fib0 n})
  ensures emp
{
  if (n < 20) {
    let r = sfib n;
    r
  } else {
    let r_th = spawn (fun () -> cb (n-1));
    let l = sfib (n-2);
    let r = join r_th;
    let res = l+r;
    res
  }
}
```
