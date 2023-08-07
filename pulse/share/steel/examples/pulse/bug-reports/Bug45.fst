module Bug45

open Pulse.Main
open Pulse.Lib.Pervasives

assume val domain : a:Type -> (a -> vprop) -> Type

assume val spawn :
 (#a:Type) -> (#pre : vprop) -> (#post : (a -> vprop)) ->
 ($f : unit -> stt a pre post) ->
 stt (domain a post) pre (fun _ -> emp)

assume val join :
  (#a:Type) -> (#post : (a -> vprop)) ->
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
  returns n:nat
  ensures emp
{
  fib0 (n-1)
}
```

[@@expect_failure]
```pulse
fn pfib (n:nat)
  requires emp
  returns n:nat
  ensures emp
{
  if (n < 20) {
    fib0 n
  } else {
    //let c = (fun () -> just #_ (fib0 (n-1))) <: unit -> stt nat emp (fun _ -> emp);
    // let th = spawn #nat #emp #(fun _ -> emp) c;
    let th = spawn #nat #emp #(fun (n:nat) -> emp) (pth n);
    let r = 123; // fib (n-2) + join th;
    r
  }
}
```
