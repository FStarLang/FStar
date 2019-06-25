module LowStar.RST.Par

open LowStar.Resource
open LowStar.RST

assume
val par (#in1 #in2:resource)
        (#a #b:Type)
        (#out1:a -> resource)
        (#out2:b -> resource)
        (out:(a & b) -> resource)
        (#pre1:r_pre in1)
        (#pre2:r_pre in2)
        (#post1:r_post in1 a out1)
        (#post2:r_post in2 b out2)
        ($f1:unit -> RST a in1 out1 pre1 post1)
        ($f2:unit -> RST b in2 out2 pre2 post2)
        : RST (a & b)
              (in1 <*> in2)
              (out)
              //(fun (x, y) -> out1 x <*> out2 y)
              // Without this formulation, z3 returns an unexpected output, with all variables not in pattern
              (fun h -> pre1 h /\ pre2 h /\ (forall x y. out1 x <*> out2 y == out (x, y)))
              (fun h0 (x, y) h1 -> out1 x <*> out2 y == out (x, y) /\ post1 h0 x h1 /\ post2 h0 y h1)
