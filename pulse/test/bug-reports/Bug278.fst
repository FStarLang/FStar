module Bug278

#lang-pulse
open Pulse

assume val domain : a:Type -> (a -> slprop) -> Type

assume val spawn :
 (#a:Type) -> (#pre : slprop) -> (#post : (a -> slprop)) ->
 ($f : unit -> stt a pre post) ->
 stt (domain a post) pre (fun _ -> emp)

fn pth (n:nat) (_:unit)
  returns n:nat
{
  2
}

fn pfib (n:nat)
{
  ();
  let _n = spawn u#0 u#0 #nat #emp #(fun (n:nat) -> emp) (pth n);
  ();
}

[@@expect_failure] // for some reason we need to provide universes
fn pfib2 (n:nat)
{
  ();
  let _n = spawn #nat #emp #(fun (n:nat) -> emp) (pth n);
  ();
}
