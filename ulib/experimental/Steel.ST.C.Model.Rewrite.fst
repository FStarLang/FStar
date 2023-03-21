module Steel.ST.C.Model.Rewrite

module P = FStar.PCM

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

let rewrite_pcm_composable
  p rewrite x1 x2
= ()

let rewrite_pcm_op
  p rewrite x1 x2
= ()

let rewrite_pcm_one
  p rewrite
= ()

let rewrite_pcm_refine
  p rewrite x
= ()
