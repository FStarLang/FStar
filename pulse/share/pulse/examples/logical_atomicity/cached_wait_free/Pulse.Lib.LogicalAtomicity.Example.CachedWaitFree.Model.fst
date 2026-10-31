module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model

(**
The cache-coherence argument of Cached-WaitFree (Big Atomics, Algorithm 1).
Backup identities are never reused; publication extends a history. A cache
writer acquires an even version, writes the words separately, then releases
the next even version. Validation is separate from releasing the cache.

Versions are mathematical naturals, as in CachedWaitFree.v, not wrapping
machine counters. The model establishes safety, not a progress bound.
*)

module S = FStar.Seq
module U32 = FStar.UInt32
open FStar.Preorder

type value = U32.t & U32.t

let even (n:nat) = n % 2 == 0

let prefix (#a:Type0) (xs ys:S.seq a) =
  S.length xs <= S.length ys /\
  (forall (i:nat). i < S.length xs ==> S.index xs i == S.index ys i)

let unique (#a:Type0) (xs:S.seq a) =
  forall (i j:nat). i < S.length xs /\ j < S.length xs /\
    S.index xs i == S.index xs j ==> i == j

type state (a:Type0) = {
  nodes:S.seq a;
  version:nat;
  cached:nat;
  target:nat;
  cache:value;
  validated:bool;
}

let valid (#a:Type0) (value:a -> value) (s:state a) =
  s.cached < S.length s.nodes /\ s.target < S.length s.nodes /\
  unique s.nodes /\
  (even s.version ==> s.cache == value (S.index s.nodes s.cached)) /\
  (not (even s.version) ==> s.cached < s.target /\ not s.validated) /\
  (s.validated ==> even s.version /\ s.cached + 1 == S.length s.nodes)

(** Besides cache/version monotonicity, validation is permanent while the
publication history has the same length. Only publishing a fresh node may
mark the backup again. Every transition below proves this invariant; it is
the fact that Attempt.two_failures needs to distinguish publication from
unmarking alone. Equality of payload values does not imply equal histories. *)
let advances (#a:Type0) : preorder (state a) =
  fun s t ->
    prefix s.nodes t.nodes /\ s.version <= t.version /\ s.cached <= t.cached /\
    (s.version == t.version ==>
      s.cached == t.cached /\
      (even s.version ==> s.cache == t.cache) /\
      (not (even s.version) ==> s.target == t.target)) /\
    (S.length s.nodes == S.length t.nodes /\ s.validated ==> t.validated)

let current (#a:Type0) (s:state a { 0 < S.length s.nodes }) =
  S.index s.nodes (S.length s.nodes - 1)

let initial (#a:Type0) (value:a -> value) (node:a)
  : s:state a { valid value s } =
  { nodes=S.create 1 node; version=0; cached=0; target=0;
    cache=value node; validated=true }

[@@"opaque_to_smt"]
let publish (#a:Type0) (value:a -> value) (s:state a { valid value s })
  (node:a { forall (i:nat). i < S.length s.nodes ==> S.index s.nodes i =!= node })
  : t:state a { valid value t /\ advances s t /\ current t == node /\
      t.nodes == S.append s.nodes (S.create 1 node) /\ t.version == s.version /\
      t.cached == s.cached /\ t.target == s.target /\ t.cache == s.cache /\ not t.validated } =
  { s with nodes=S.append s.nodes (S.create 1 node); validated=false }

(** A successful version CAS must use a version sampled BEFORE publication.
Without that premise a delayed older writer could overwrite a valid cache. *)
[@@"opaque_to_smt"]
let acquire (#a:Type0) (value:a -> value)
  (s:state a { valid value s /\ even s.version })
  (k:nat { s.cached < k /\ k < S.length s.nodes })
  : t:state a { valid value t /\ advances s t /\ t.version == s.version + 1 /\
      t.nodes == s.nodes /\ t.cached == s.cached /\ t.target == k /\ t.cache == s.cache /\
      t.validated == s.validated } =
  { s with version=s.version + 1; target=k }

[@@"opaque_to_smt"]
let write_first (#a:Type0) (value:a -> value)
  (s:state a { valid value s /\ not (even s.version) }) (x:U32.t)
  : t:state a { valid value t /\ advances s t /\ t.version == s.version /\
      t.nodes == s.nodes /\ t.cached == s.cached /\ t.target == s.target /\
      t.cache == (x, snd s.cache) /\ t.validated == s.validated } =
  { s with cache=(x, snd s.cache) }

[@@"opaque_to_smt"]
let write_second (#a:Type0) (value:a -> value)
  (s:state a { valid value s /\ not (even s.version) }) (y:U32.t)
  : t:state a { valid value t /\ advances s t /\ t.version == s.version /\
      t.nodes == s.nodes /\ t.cached == s.cached /\ t.target == s.target /\
      t.cache == (fst s.cache, y) /\ t.validated == s.validated } =
  { s with cache=(fst s.cache, y) }

[@@"opaque_to_smt"]
let release (#a:Type0) (value:a -> value)
  (s:state a { valid value s /\ not (even s.version) /\
    s.cache == value (S.index s.nodes s.target) })
  : t:state a { valid value t /\ advances s t /\ t.version == s.version + 1 /\
      t.nodes == s.nodes /\ t.cached == s.target /\ t.target == s.target /\
      t.cache == s.cache /\ t.validated == s.validated } =
  { s with version=s.version + 1; cached=s.target }

(** Once a writer has released its cache, a successful unmark of THAT node
implies no newer cache writer has acquired the version in the meantime. *)
let can_validate (#a:Type0) (value:a -> value)
  (old now:state a) (k:nat)
  : Lemma
      (requires valid value old /\ valid value now /\ advances old now /\
        old.cached == k /\ k < S.length old.nodes /\
        S.index old.nodes k == current now)
      (ensures now.cached == k /\ even now.version /\
        now.cache == value (current now)) =
  ()

[@@"opaque_to_smt"]
let validate (#a:Type0) (value:a -> value)
  (s:state a { valid value s /\ even s.version /\
    s.cached + 1 == S.length s.nodes })
  : t:state a { valid value t /\ advances s t /\ t.version == s.version /\
      t.nodes == s.nodes /\ t.cached == s.cached /\ t.target == s.target /\
      t.cache == s.cache /\ t.validated } =
  { s with validated=true }

(** This is the fast-path theorem. The pointer is sampled BETWEEN the cache
word reads and the final version read, not before copying the cache. *)
let cached_read (#a:Type0) (value:a -> value)
  (start first second backup finish:state a)
  : Lemma
      (requires valid value start /\ valid value first /\ valid value second /\
        valid value backup /\ valid value finish /\
        advances start first /\ advances first second /\
        advances second backup /\ advances backup finish /\
        backup.validated /\ start.version == finish.version)
      (ensures (fst first.cache, snd second.cache) == value (current backup)) =
  ()

let same_node (#a:Type0) (old now:state a) (i j:nat)
  : Lemma
      (requires unique now.nodes /\ advances old now /\
        i < S.length old.nodes /\ j < S.length now.nodes /\
        S.index old.nodes i == S.index now.nodes j)
      (ensures i == j) =
  ()
