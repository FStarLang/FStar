module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
#lang-pulse

(** Immutable backup nodes, with one-use ghost publication tickets.
The finite arena replaces allocation/reclamation; lookup is not constant time.
Different nodes may contain equal values, including an A--B--A history. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.ForEvery
module G = Pulse.Lib.GhostReference
module L = FStar.List.Tot
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model

noeq type cell = { value:H.value; token:G.ref unit }
type arena = xs:list cell { 0 < L.length xs }
type id (cells:arena) = n:nat { n < L.length cells }
let at (cells:arena) (n:id cells) = L.index cells n
let value (cells:arena) (n:id cells) = (at cells n).value
let ticket (cells:arena) (n:id cells) = G.pts_to (at cells n).token ()

let used_at (cells:arena) (ns:S.seq (id cells)) (k:nat) =
  if k < S.length ns then ticket cells (S.index ns k) else emp

let used (cells:arena) (ns:S.seq (id cells)) =
  forall+ (k:nat { k < S.length ns }). used_at cells ns k

instance send_ticket cells n : is_send (ticket cells n) =
  FStar.Tactics.Typeclasses.solve

instance send_used cells ns : is_send (used cells ns) =
  is_send_forevery (fun (k:nat { k < S.length ns }) -> used_at cells ns k)
    #(fun k -> send_ticket cells (S.index ns k))

ghost fn fresh (cells:arena) (ns:S.seq (id cells)) (n:id cells)
  preserves used cells ns ** ticket cells n
  ensures pure (forall (k:nat). k < S.length ns ==> S.index ns k =!= n)
{
  let present = FStar.IndefiniteDescription.strong_excluded_middle
    (exists (k:nat). k < S.length ns /\ S.index ns k == n);
  if present {
    let k = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun (k:nat) -> k < S.length ns /\ S.index ns k == n);
    unfold used;
    forevery_remove' #nat (fun j -> j < S.length ns) (used_at cells ns) k;
    rewrite used_at cells ns k as G.pts_to (at cells (S.index ns k)).token ();
    rewrite each (S.index ns k) as n;
    unfold ticket cells n;
    G.gather (at cells n).token;
    G.pts_to_perm_bound (at cells n).token;
    assert pure False;
    unreachable ();
  }
}

ghost fn append (cells:arena) (ns:S.seq (id cells)) (n:id cells)
  requires used cells ns ** ticket cells n
  ensures used cells (S.append ns (S.create 1 n))
{
  unfold used;
  let ns' = S.append ns (S.create 1 n);
  forevery_ext
    (fun (j:nat { j < S.length ns }) -> used_at cells ns j)
    (fun j -> used_at cells ns' j);
  rewrite ticket cells n as used_at cells ns' (S.length ns);
  forevery_insert #nat #(fun j -> j < S.length ns)
    (used_at cells ns') (S.length ns);
  forevery_refine_ext #nat (fun j -> j < S.length ns')
    (used_at cells ns');
  fold used cells ns';
  rewrite each ns' as S.append ns (S.create 1 n);
}

ghost fn singleton (cells:arena) (n:id cells)
  requires ticket cells n
  ensures used cells (S.create 1 n)
{
  forevery_intro_false #nat (used_at cells (S.create 1 n));
  rewrite ticket cells n as used_at cells (S.create 1 n) 0;
  forevery_insert #nat #(fun _ -> False)
    (used_at cells (S.create 1 n)) 0;
  forevery_refine_ext #nat (fun j -> j < S.length (S.create 1 n))
    (used_at cells (S.create 1 n));
  fold used cells (S.create 1 n);
}

fn node (v:H.value)
  returns c:cell
  ensures G.pts_to c.token () ** pure (c.value == v)
{
  let token = G.alloc ();
  let c = { value=v; token };
  rewrite each token as c.token;
  c
}
