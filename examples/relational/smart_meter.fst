(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/st2.fst $LIB/all.fst $LIB/bytes.fst $LIB/list.fst 

  --*)

module SmartMeter 
open Bytes
open List

let left = fst 
let right = snd
let twice x = x, x
type double (t:Type) = t * t
type eq (t:Type) = p:(double t){left p = right p}

let add_pair (a,b) (c,d) = a+c, b+d
let mul_pair (a,b) (c,d) = a*c, b*d
val tail_pair: #a:Type -> l:double (list a){is_Cons (left l) /\ is_Cons (right l)}-> Tot (double (list a))
let tail_pair (_::xs, _::ys) = xs, ys
let cons_pair (x,y) (xs,ys) = x::xs, y::ys
let pair_pair (x,y) (x',y') = (x,x'),(y,y')



type elt (* elements of the group *)
assume logic val idelt: elt 

(* Treating exponents as int is dodgy; they are integers modulo. *)
type tp (* trapdoor (private param) *)
type public_param (* public param: p, g, h *)
type pparam = eq public_param 
assume logic val trap: public_param -> int (* such that g = h^(trap pp) *) 

type text = int (* exponents for values *)
type opng = int (* exponents for openings *)

type openingP (lx:text) (rx:text) (lo:opng) (ro:opng) = lx + lo = rx + ro
type opening (x:double text) = o:(double opng){ openingP (left x) (right x) (left o) (right o) }

type openingsP (ll:list (text * opng)) (lr:list (text * opng))
type openings  = os:(double (list (text *opng))){openingsP (left os) (right os) /\
                                                 length (left  os) = length (right os)}
assume Openings_nil : (openingsP [] [])
assume Openings_cons : (forall lx rx lo ro lrest rrest.
                            (openingP lx rx lo ro /\ openingsP lrest rrest 
                            <==> openingsP ((lx,lo)::lrest) ((rx,ro)::rrest)))

val fsts: #a:Type -> #b:Type -> i:list (a * b) -> Tot (o:(list a){length i = length o})
let rec fsts l = match l with 
  | [] -> []
  | (a,b)::ls -> a :: fsts ls 

let fsts_pair (ll, lr) = fsts ll, fsts lr

val scalar_product :l1:list int -> l2:list int{length l1 = length l2} -> Tot int
let rec scalar_product l1 l2 = match l1, l2 with
  | [], [] -> 1
  | x::xs, y::ys -> x*y + scalar_product xs ys

assume val commitP: double public_param -> double text -> double opng -> Tot (double elt)
assume val commit: pp:pparam -> x:double text 
                   -> p:(double opng * eq elt){openingP (left x) (right x) (left(fst p)) (right(fst p)) 
                                            /\ commitP pp x (fst p) = snd p}

assume val verify: pp:pparam -> x:double text -> r:double opng -> c:double elt 
                   -> b:(eq bool){fst b ==> c = commitP pp x r}


assume Commit_injective : (forall pp x0 x1 r0 r1. (commitP pp x0 r0 = commitP pp x1 r1) ==> x0 = x1)



assume val mult: c0:double elt -> c1: double elt 
                 -> c:double elt{forall pp x0 x1 r0 r1.
                          (c0 = commitP pp x0 r0 /\ c1=commitP pp x1 r1) ==> 
                          c=commitP pp (add_pair x0 x1) (add_pair r0 r1)}

assume val exp: c0:double elt -> z:double int
                 -> c:double elt{forall pp x0 r0.
                          c0 = commitP pp x0 r0 ==> 
                          c=commitP pp (mul_pair x0 z) (mul_pair r0 z)}
                  
assume val commitsP: pp:double (public_param) -> double (list(text * opng)) -> Tot (double (list elt))
assume val commitsP_nil: pp:pparam -> xrs:double(list (text * opng)) -> Lemma (commitsP pp xrs = twice [] <==> xrs = twice [])
assume val commitsP_cons: pp:pparam -> xrs:double (list(text * opng)) 
                          -> hd:double(elt) -> tl:(double(list(elt))) 
                          -> Lemma((commitsP pp xrs = cons_pair hd tl) <==> 
                                     (exists x r xrstl. (xrs = cons_pair (pair_pair x r) xrstl
                                                       /\ hd = commitP pp x r
                                                       /\ tl = commitsP pp xrstl)))
                                                              




(******************************* Smart Meters ******************************)

let fst3=MkTuple3._1
let snd3=MkTuple3._2
let thd3=MkTuple3._3

assume logic type readings (l:double (list int))
assume logic type rates (l:double (list int))
assume ReadingsTail : (forall l. is_Cons (left l) /\ is_Cons (right l) 
                                  ==> readings (tail_pair l))
assume RatesTail : (forall l. is_Cons (left l) /\ is_Cons (right l) 
                                  ==> rates (tail_pair l))

type signed (pp:pparam) (cs:double (list elt)) = 
              (exists xrs. readings (fsts_pair xrs) /\ cs = commitsP pp xrs)

type dsig = bytes

assume val sign: pp:pparam -> cs:eq(list elt){signed pp cs} -> eq dsig

assume val verify_meter_signature: pp:pparam
  -> cs:eq (list elt)
  -> eq dsig
  -> b:eq bool{left  b ==> signed pp cs }



(* METER *)

val commits: pp:pparam
  -> xs:double (list int){readings xs /\ length (left xs) = length (right xs)}
  -> r:(openings * eq (list elt))
     {xs = fsts_pair (fst r)
   /\ commitsP pp (fst r) = snd r}
let rec commits pp xs = match left xs, right xs with 
  | [], [] -> commitsP_nil pp (twice []); ([],[]),([],[]) 
  | lx::lxs, rx::rxs -> let xrstl, cs = commits pp (lxs, rxs) in 
                        let r , c = commit pp (lx, rx) in 
                        let xrshd =  ((lx, left  r), (rx, right r)) in
                        let xrs = cons_pair xrshd xrstl in
                        cut(b2t(xrs = cons_pair (pair_pair (lx,rx) r) xrstl));
                        cut(exists x r. xrs  = cons_pair (pair_pair x r) xrstl);
                        commitsP_cons pp xrs c cs;
                        xrs, (cons_pair c cs)

val meter: pp:pparam 
          -> xs:double(list int){readings xs /\ length (left xs) = length (right xs)}
          -> r:(openings * eq(list elt) * eq dsig)
            {xs = fsts_pair (fst3 r)
          /\ commitsP pp (fst3 r) = snd3 r}
let meter pp xs = 
          let xrs,cs = commits pp xs in 
          assume (signed pp cs);
          (xrs, cs, sign pp cs)

(* USER *)
(*
val sums: xrs: openings -> ps:eq(list int){length(left  ps) = length (left  xrs) /\ 
                                           length(right ps) = length (right xrs)} -> 
                          (x:(double int){left  x=scalar_product (fsts (left  xrs)) (left  ps) /\
                                          right x=scalar_product (fsts (right xrs)) (right ps)}
                                          & opening x)
let rec sums xrs ps = match xrs, ps with
  | (lxr::lxrs,rxr::rxrs), (lp::lps,rp::rps) -> 
      let (lx, rx), (lr, rr) = lxr, rxr in
      let (| (lx0, rx0), (lr0, rr0) |) = sums (lxrs, rxrs) (lps, rps) in 
      assert(openingP  lx rx lr rr);
      assert(lx0 + lr0 = rx0 + rr0);
      assert(lx0 + lx * lp + lr0 + lr * lp = rx0 + rx * rp + rr0 +rr * rp);
(*       (| (lx0 + lx*lp, rx0 + rx*rp), (lr0 + lr * lp, rr0 + rr * rp) |) *)
      admit ()
  | (([],[]),([],[])) -> (| (twice 1),(twice 0) |)
*)
