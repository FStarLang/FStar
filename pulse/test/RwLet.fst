module RwLet
open Pulse
#lang-pulse

(* Aliasing a reference with a plain 'let' breaks the proof: Pulse does not
   know r' and r are interchangeable, so 'r' |-> v' fails to match the
   context 'r |-> v'. *)
[@@expect_failure [228]]
fn alias_plain (r: ref int) (#v:erased int)
  requires r |-> v
  ensures r |-> v
{
  let r' : ref int = r;
  assert (r' |-> v);
}

(* 'let rewrite' fixes it: it adds 'assert rewrites_to r' r', so the matcher
   replaces r' by r and the proof goes through. *)
fn alias_rewrite (r: ref int) (#v:erased int)
  requires r |-> v
  ensures r |-> v
{
  let rewrite r' : ref int = r;
  assert (r' |-> v);
}

(* It works in the other direction too: rewriting lets us present the
   resource under the alias and still satisfy a postcondition stated with
   the original name. *)
fn alias_rewrite_post (r: ref int)
  requires r |-> 0
  ensures r |-> 0
{
  let rewrite r' : ref int = r;
  r' := 0;
}
