module Steel.ST.C.Model.Rewrite

open Steel.C.Model.PCM
open Steel.C.Model.Connection

let rewrite_forall_from
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
: GTot prop
= forall (x: from) . rewrite_to_from (rewrite_from_to x) == x

let rewrite_forall_from_intro
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
  (f: (x: from) -> Lemma
    (rewrite_to_from (rewrite_from_to x) == x)
  )
: Lemma
  (rewrite_forall_from rewrite_from_to rewrite_to_from)
= Classical.forall_intro f

let rewrite_forall_to
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
: GTot prop
= forall (y: to) . rewrite_from_to (rewrite_to_from y) == y

let rewrite_forall_to_intro
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
  (f: (x: to) -> Lemma
    (rewrite_from_to (rewrite_to_from x) == x)
  )
: Lemma
  (rewrite_forall_to rewrite_from_to rewrite_to_from)
= Classical.forall_intro f

noeq
type rewrite_elts (from: Type) (to: Type) = {
  rewrite_from_to : (from -> Tot to);
  rewrite_to_from: (to -> Tot from);
  rewrite_equiv : squash (
    rewrite_forall_from rewrite_from_to rewrite_to_from /\
    rewrite_forall_to rewrite_from_to rewrite_to_from
  );
}

val rewrite_pcm
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Tot (pcm to)

val rewrite_pcm_composable
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
  (x1 x2: to)
: Lemma
  (composable (rewrite_pcm p rewrite) x1 x2 <==> composable p (rewrite.rewrite_to_from x1) (rewrite.rewrite_to_from x2))
  [SMTPat (composable (rewrite_pcm p rewrite) x1 x2)]

val rewrite_pcm_op
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
  (x1 x2: to)
: Lemma
  (requires (composable (rewrite_pcm p rewrite) x1 x2))
  (ensures (op (rewrite_pcm p rewrite) x1 x2 == rewrite.rewrite_from_to (op p (rewrite.rewrite_to_from x1) (rewrite.rewrite_to_from x2))))
  [SMTPat (op (rewrite_pcm p rewrite) x1 x2)]

val rewrite_pcm_one
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Lemma
  (one (rewrite_pcm p rewrite) == rewrite.rewrite_from_to (one p))
  [SMTPat (one (rewrite_pcm p rewrite))]

val rewrite_pcm_refine
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
  (x: to)
: Lemma
  (p_refine (rewrite_pcm p rewrite) x <==> p_refine p (rewrite.rewrite_to_from x))
  [SMTPat (p_refine (rewrite_pcm p rewrite) x)]

let rewrite_iso
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Tot (isomorphism p (rewrite_pcm p rewrite))
= mkisomorphism
    (mkmorphism
      rewrite.rewrite_from_to
      ()
      (fun _ _ -> ())
    )
    (mkmorphism
      rewrite.rewrite_to_from
      ()
      (fun _ _ -> ())
    )
    ()
    ()
    (fun _ -> ())
    (fun _ -> ())
