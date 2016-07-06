module Bug292

type shared (s:int) = p:(int * int){(fst p) + (snd p) = s}
type shared2 (h:(int * int)) = p:((shared (fst h)) * (shared (snd h)))

val triple_a : unit -> Tot (r:(a:(int*int) & shared2 a) {snd(snd(dsnd r))=0} )
let triple_a () = let r  = (|(0,0),((0,0),(0,0))|) in
                  let r' = (|(0,0),((0,0),(0,0))|) in
(*                   cut(b2t(0=(snd(snd(dsnd r'))))); *)
(*                   cut(b2t(r = r')); *)
                  cut(b2t(0=(snd(snd(dsnd r)))));
                  r
