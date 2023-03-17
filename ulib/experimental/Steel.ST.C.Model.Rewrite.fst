module Steel.ST.C.Model.Rewrite

open Steel.C.Model.PCM
open Steel.C.Model.Connection

module P = FStar.PCM

noeq
type rewrite_elts (from: Type) (to: Type) = {
  rewrite_from_to : (from -> Tot to);
  rewrite_to_from: (to -> Tot from);
  rewrite_equiv : squash (
    (forall (x: from) . rewrite_to_from (rewrite_from_to x) == x) /\
    (forall (y: to) . rewrite_from_to (rewrite_to_from y) == y)
  );
}

let fstar_rewrite_pcm
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Tot (P.pcm to)
= let fp = fstar_pcm_of_pcm p in
  {
    P.p = {
      P.composable = (fun y1 y2 -> composable p (rewrite.rewrite_to_from y1) (rewrite.rewrite_to_from y2));
      P.op = (fun y1 y2 -> rewrite.rewrite_from_to (op p (rewrite.rewrite_to_from y1) (rewrite.rewrite_to_from y2)));
      P.one = rewrite.rewrite_from_to (one p);
    };
    P.comm = (fun _ _ -> ());
    P.assoc = (fun _ _ _ -> ());
    P.assoc_r = (fun _ _ _ -> ());
    P.is_unit = (fun _ -> ());
    P.refine = (fun y -> p_refine p (rewrite.rewrite_to_from y));
  }

let rewrite_pcm
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Tot (pcm to)
= let fp = fstar_pcm_of_pcm p in
  pcm_of_fstar_pcm (fstar_rewrite_pcm p rewrite)

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
