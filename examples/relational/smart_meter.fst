(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:ext.fst set.fsi heap.fst st.fst st2.fst all.fst bytes.fst list.fst
  --*)

module SmartMeter
open FStar.Bytes
open FStar.List
open FStar.Relational



type elt (* elements of the group *)
assume logic val idelt: elt

(* Treating exponents as int is dodgy; they are integers modulo. *)
type tp (* trapdoor (private param) *)
type public_param (* public param: p, g, h *)
type pparam = eq public_param
assume logic val trap: public_param -> Tot int (* such that g = h^(trap pp) *)

type text = int (* exponents for values *)
type opng = int (* exponents for openings *)

type openingP (lx:text) (rx:text) (lo:opng) (ro:opng) = lx + lo = rx + ro
type opening (x:double text) = o:(double opng){ openingP (R.l x) (R.r x) (R.l o) (R.r o) }

type openingsP (ll:list (text * opng)) (lr:list (text * opng))
type openings  = os:(double (list (text *opng))){openingsP (R.l os) (R.r os) /\
                                                 length (R.l os) = length (R.r os)}
assume Openings_nil : (openingsP [] [])
assume Openings_cons : (forall lx rx lo ro lrest rrest.
                            (openingP lx rx lo ro /\ openingsP lrest rrest
                            <==> openingsP ((lx,lo)::lrest) ((rx,ro)::rrest)))

val fsts: #a:Type -> #b:Type -> i:list (a * b) -> Tot (o:(list a){length i = length o})
let rec fsts l = match l with
  | [] -> []
  | (a,b)::ls -> a :: fsts ls

let fsts_rel = rel_map1T fsts

val scalar_product :l1:list int -> l2:list int{length l1 = length l2} -> Tot int
let rec scalar_product l1 l2 = match l1, l2 with
  | [], [] -> 1
  | x::xs, y::ys -> x*y + scalar_product xs ys

val scalar_product_rel : l1:double (list int)
                         -> l2:double (list int){length (R.l l1) = length (R.l l2)
                                                 /\ length (R.r l1) = length (R.r l2)}
                         -> Tot (double int)
let scalar_product_rel (R ll1 rl1) (R ll2 rl2) = R (scalar_product ll1 ll2) (scalar_product rl1 rl2)

assume val commitP: double public_param -> double text -> double opng -> Tot (double elt)
assume val commit: pp:pparam -> x:double text
                   ->Tot (p:(double opng * eq elt){openingP (R.l x) (R.r x) (R.l(fst p)) (R.r(fst p))
                                            /\ commitP pp x (fst p) = snd p})

assume val verify: pp:pparam -> x:double text -> r:double opng -> c:double elt
                   -> Tot (b:(eq bool){R.l b ==> c = commitP pp x r})


assume CommitP_injective : (forall pp x0 x1 r0 r1. (commitP pp x0 r0 = commitP pp x1 r1) ==> x0 = x1)



assume val mult: c0:double elt -> c1: double elt
                 -> Tot (c:double elt{forall pp x0 x1 r0 r1.
                          (c0 = commitP pp x0 r0 /\ c1=commitP pp x1 r1) ==>
                          c=commitP pp (x0 ^+ x1) (r0 ^+ r1)})

assume val exp: c0:double elt -> z:double int
                 -> Tot (c:double elt{forall pp x0 r0.
                          c0 = commitP pp x0 r0 ==>
                          c=commitP pp (x0 ^* z) (r0 ^* z)})

assume val commitsP: pp:double (public_param) -> double (list(text * opng)) -> Tot (double (list elt))
assume val commitsP_nil: pp:pparam -> xrs:double(list (text * opng)) -> Lemma (commitsP pp xrs = twice [] <==> xrs = twice [])
assume val commitsP_cons: pp:pparam -> xrs:double (list(text * opng))
                          -> hd:double(elt) -> tl:(double(list(elt)))
                          -> Lemma((commitsP pp xrs = cons_rel hd tl) <==>
                                     (exists x r xrstl. (xrs = cons_rel (pair_rel x r) xrstl
                                                       /\ hd = commitP pp x r
                                                       /\ tl = commitsP pp xrstl)))

type commitments (p:(double (list text) -> Type)) (pp:double (public_param)) =
           cs:double (list elt){forall x xs. p (cons_rel x xs) ==> p xs
                                /\ (exists xrs. p (fsts_rel xrs) /\ cs=commitsP pp xrs)}
(* TODO *)
assume val scalar_exp : p:(double (list text) -> Type)
                        -> pp:pparam
                        -> commitments p pp
                        -> ps:double (list int)
                        -> Tot (c:double elt{exists xs r. p xs
                                             /\ length (R.l xs) = length (R.l ps)
                                             /\ length (R.r xs) = length (R.r ps)
                                             /\ c = commitP pp (scalar_product_rel xs ps) r})



(******************************* Smart Meters ******************************)

let fst3=MkTuple3._1
let snd3=MkTuple3._2
let thd3=MkTuple3._3

assume logic type readings (l:double (list int))
assume logic type rates (l:double (list int))
assume ReadingsTail : (forall l. is_Cons (R.l l) /\ is_Cons (R.r l)
                                  ==> readings (tl_rel l))
assume RatesTail : (forall l. is_Cons (R.l l) /\ is_Cons (R.r l)
                                  ==> rates (tl_rel l))

type signed (pp:pparam) (cs:double (list elt)) =
              (exists xrs. readings (fsts_rel xrs) /\ cs = commitsP pp xrs)

type dsig = bytes

assume val sign: pp:pparam -> cs:eq(list elt){signed pp cs} -> Tot (eq dsig)

assume val verify_meter_signature: pp:pparam
  -> cs:eq (list elt)
  -> eq dsig
  -> Tot (b:eq bool{R.l b ==> signed pp cs })


(* METER *)
val commits: pp:pparam
  -> xs:double (list int){readings xs /\ length (R.l xs) = length (R.r xs)}
  -> Tot (r:(openings * eq (list elt)){xs = fsts_rel (fst r)
                                       /\ commitsP pp (fst r) = snd r})
                                      (decreases (R.l xs))
let rec commits pp xs = match xs with
  | R [] [] -> commitsP_nil pp (twice []); (twice []),(twice [])
  | R (lx::lxs) (rx::rxs) -> let x = R lx rx in
                             let xs = R lxs rxs in
                             let xrstl, cs = commits pp xs in
                             let r,  c = commit pp x in
                             let xrshd =  pair_rel x r in
                             let xrs = cons_rel xrshd xrstl in
                             cut(b2t(xrs = cons_rel (pair_rel x r) xrstl));
                             cut(exists x r. xrs  = cons_rel (pair_rel x r) xrstl);
                             commitsP_cons pp xrs c cs;
                             xrs, (cons_rel c cs)


val meter: pp:pparam
          -> xs:double(list int){readings xs /\ length (R.l xs) = length (R.r xs)}
          -> Tot (r:(openings * eq(list elt) * eq dsig) {xs = fsts_rel (fst3 r)
                                                         /\ commitsP pp (fst3 r) = snd3 r})
let meter pp xs =
          let xrs,cs = commits pp xs in
          (xrs, cs, sign pp cs)

(* USER *)
val sums: xrs: openings -> ps:eq(list int){length(R.l ps) = length (R.l xrs) /\
                                           length(R.r ps) = length (R.r xrs)}
          -> Tot (x:(double int){R.l x=scalar_product (fsts (R.l xrs)) (R.l ps)
                              /\ R.r x=scalar_product (fsts (R.r xrs)) (R.r ps)}
                  & opening x)
                  (decreases (R.l xrs))

let rec sums xrs ps = match xrs, ps with
  | R (lxr::lxrs) (rxr::rxrs), R (lp::lps) (rp::rps) ->
      (* move from single sided values to relational values again *)
      let xr = R lxr rxr in
      let xrs = R lxrs rxrs in
      let p = R lp rp in
      let ps = R lps rps in

      let x = fst_rel xr in
      let r = snd_rel xr in
      let (| x0, r0 |) = sums xrs ps in
      (| x0 ^+ (x ^* p), r0 ^+ (r ^* p) |)
  | R [] [], R [] [] -> (| (twice 1),(twice 0) |)

val make_payment: pp:pparam -> xrs:openings{readings (fsts_rel xrs)}
               -> ps:(eq (list int)){rates ps
                                     /\ length (R.l xrs) = length (R.l ps)
                                     /\ length (R.r xrs) = length (R.r ps)
                                     /\ scalar_product (fsts (R.l xrs)) (R.l ps)
                                          = scalar_product (fsts (R.r xrs)) (R.r ps)}
               -> Tot (eq int * eq int)
let make_payment pp xrs ps =
      let (| x, o |) =  sums xrs ps in
      x,o

(* VERIFYIER *)

val verify_payment: pp:pparam
                    -> ps:eq (list int){rates ps}
                    -> cs:eq (list elt)
                    -> s:eq dsig
                    -> x:double text
                    -> r:double opng
                    -> Tot (b:eq bool{R.l b ==> (exists xs. readings xs
                                                            /\ length (R.l xs) = length (R.l ps)
                                                            /\ length (R.r xs) = length (R.r ps)
                                                            /\ x  = scalar_product_rel xs ps)})
let verify_payment pp ps cs s x r =
  match  verify_meter_signature pp cs s with
  | R true  true  -> let c = scalar_exp #readings pp cs ps in
                     verify pp x r c
  | R false false -> twice false
