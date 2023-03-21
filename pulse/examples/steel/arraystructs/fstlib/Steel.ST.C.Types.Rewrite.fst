module Steel.ST.C.Types.Rewrite
open Steel.ST.Util

friend Steel.ST.C.Types.Base
open Steel.ST.C.Types.Base

module RW = Steel.ST.C.Model.Rewrite

let rewrite_typedef
  (#from #to: Type)
  (td: typedef from)
  (rewrite: RW.rewrite_elts from to)
: Tot (typedef to)
= {
    pcm = RW.rewrite_pcm td.pcm rewrite;
    fractionable = (fun y -> td.fractionable (rewrite.rewrite_to_from y));
    mk_fraction = (fun y p -> rewrite.rewrite_from_to (td.mk_fraction (rewrite.rewrite_to_from y) p));
    mk_fraction_full = (fun y -> td.mk_fraction_full (rewrite.rewrite_to_from y));
    mk_fraction_compose = (fun y p1 p2 -> td.mk_fraction_compose (rewrite.rewrite_to_from y) p1 p2);
    fractionable_one = ();
    mk_fraction_one = (fun p -> td.mk_fraction_one p);
    uninitialized = rewrite.rewrite_from_to td.uninitialized;
    mk_fraction_split = (fun y p1 p2 -> td.mk_fraction_split (rewrite.rewrite_to_from y) p1 p2);
    mk_fraction_join = (fun y p1 p2 -> td.mk_fraction_join (rewrite.rewrite_to_from y) p1 p2);
    mk_fraction_eq_one = (fun y p -> td.mk_fraction_eq_one (rewrite.rewrite_to_from y) p);
  }
