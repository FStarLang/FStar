(*--build-config
    options:--z3timeout 20;
    other-files: sample.fst 
  --*)

module Fp

assume type prime (p:pos)
type prime_number = p:pos{prime p}
assume val p:prime_number

(* type fp = i:int{0 <= i /\ i < p} *)
type fp = int

val mod_p : int -> Tot fp
let mod_p x = x //% p

val add_fp : fp -> fp -> Tot fp
let add_fp x y = mod_p (x + y)

val mul_fp : fp -> fp -> Tot fp
let mul_fp x y = mod_p (x * y)

val minus_fp : fp -> fp -> Tot fp
let minus_fp x y = add_fp x (mod_p (-y))

assume val div_fp : a:fp -> b:fp -> Tot (r:fp{mul_fp b r = a})

(*
let mod_laws1 = assume(forall a b.((a % p) + b) % p = (a + b) %p)
let mod_laws2 = assume(forall a b.(a + (b % p)) % p = (a + b) %p)
let mod_laws3 = assume(forall a b.((a % p) * b) % p = (a * b) %p)
let mod_laws4 = assume(forall a b.(a * (b % p)) % p = (a * b) %p)
let mod_laws5 = assume(forall a b.((a % p) - b) % p = (a - b) %p)
let mod_laws6 = assume(forall a b.(a - (b % p)) % p = (a - b) %p)
*)

module Triples
open Fp
open Sample
open Bijection

let fst3 = MkTuple3._1
let snd3 = MkTuple3._2
let thd3 = MkTuple3._3

val help_triple_a: x:fp -> sl0:fp -> sr0:fp
           -> Lemma (minus_fp sl0 x = minus_fp sr0 (add_fp (minus_fp x sl0) sr0))
let help_triple_a x sl0 sr0 = ()

opaque val triple_a : sl0:(fp*fp) -> sr0:(fp*fp)
               -> Pure ((fp*(fp*fp))*(fp*(fp*fp)))
                      (requires  True)
                      (ensures  fun r -> minus_fp (snd sl0) (snd(snd(fst r))) =
                                             minus_fp (snd sr0) (snd(snd(snd r)))
                                          /\ add_fp (fst(snd(fst r))) (snd(snd(fst r))) = (fst(fst r))
                                          /\ add_fp (fst(snd(snd r))) (snd(snd(snd r))) = (fst(snd r))
                                          /\ fst(snd(fst r))=fst(snd(snd r)))
let triple_a sl0 sr0 =
                       let sample_fun = (fun x -> add_fp (minus_fp x (snd sl0)) (snd sr0)) in
                       let sample_fun'= (fun x -> add_fp (minus_fp x (snd sr0)) (snd sl0)) in
                       cut(inverses #fp #fp sample_fun sample_fun');
                       lemma_inverses_bij #fp #fp sample_fun sample_fun';
                       let asl0, asr0 = sample (fun x -> x) in
                       let asl1, asr1 = sample  sample_fun in
                       let al = add_fp asl0 asl1 in
                       let ar = add_fp asr0 asr1 in
                       let ar = add_fp asr0 asr1 in
                       help_triple_a asl1 (snd sl0) (snd sr0);
                       cut(b2t(minus_fp (snd sl0) asl1 = minus_fp (snd sr0) asr1));
                       cut(b2t(add_fp asl0 asl1 = al));
                       cut(b2t(add_fp asr0 asr1 = ar));
                       cut(b2t(asl0 = asr0));
                       cut(b2t(add_fp asl0 asl1 = al));
                       let r = (al,(asl0, asl1)),(ar,(asr0,asr1)) in
                       cut(b2t(minus_fp (snd sl0) (snd(snd(fst r))) =
                               minus_fp (snd sr0) (snd(snd(snd r)))));
                       cut(b2t(add_fp (fst(snd(fst r))) (snd(snd(fst r))) = (fst(fst r))));
                       cut(b2t(add_fp (fst(snd(snd r))) (snd(snd(snd r))) = (fst(snd r))));
                       cut(b2t(fst(snd(fst r))=fst(snd(snd r))));
                       r
#reset-options


opaque val triple_c : a:(fp*fp) -> b:(fp*fp)
               -> Pure ((fp*(fp*fp))*(fp*(fp*fp)))
                      (requires  True)
                      (ensures  fun r -> mul_fp (fst a) (fst b) = fst(fst r)
                                          /\ mul_fp (snd a) (snd b) = fst(snd r)
                                          /\ add_fp (fst(snd(fst r))) (snd(snd(fst r))) = (fst(fst r))
                                          /\ add_fp (fst(snd(snd r))) (snd(snd(snd r))) = (fst(snd r))
                                          /\ fst(snd(fst r))=fst(snd(snd r)))
let triple_c (al,ar) (bl,br) = let cl = mul_fp al bl in
                               let cr = mul_fp ar br in
                               let csl0, csr0 = sample (fun x -> x) in
                               let csl1, csr1 = minus_fp cl csl0, minus_fp cr csr0 in
                               (cl,(csl0, csl1)),(cr,(csr0,csr1))
#reset-options

opaque val triple : sl0:(fp*fp) -> sl1:(fp*fp) -> sr0:(fp*fp) -> sr1:(fp*fp)
                    -> Pure (((fp*(fp*fp))*(fp*(fp*fp))*(fp*(fp*fp))) * ((fp*(fp*fp))*(fp*(fp*fp))*(fp*(fp*fp))))
                           (requires ( True))
                           (ensures  (fun r -> mul_fp (fst(fst3(fst r))) (fst(snd3(fst r)))
                                                         = fst(thd3(fst r))
                                                 /\ mul_fp (fst(fst3(snd r))) (fst(snd3(snd r)))
                                                         = fst(thd3(snd r))
                                                 /\ add_fp (fst(snd(fst3(fst r)))) (snd(snd(fst3(fst r)))) = fst(fst3(fst r))
                                                 /\ add_fp (fst(snd(snd3(fst r)))) (snd(snd(snd3(fst r)))) = fst(snd3(fst r))
                                                 /\ add_fp (fst(snd(thd3(fst r)))) (snd(snd(thd3(fst r)))) = fst(thd3(fst r))
                                                 /\ add_fp (fst(snd(fst3(snd r)))) (snd(snd(fst3(snd r)))) = fst(fst3(snd r))
                                                 /\ add_fp (fst(snd(snd3(snd r)))) (snd(snd(snd3(snd r)))) = fst(snd3(snd r))
                                                 /\ add_fp (fst(snd(thd3(snd r)))) (snd(snd(thd3(snd r)))) = fst(thd3(snd r))
                                                 /\ minus_fp (snd sl0) (snd(snd(fst3(fst r)))) =
                                                    minus_fp (snd sr0) (snd(snd(fst3(snd r))))
                                                 /\ minus_fp (snd sl1) (snd(snd(snd3(fst r)))) =
                                                    minus_fp (snd sr1) (snd(snd(snd3(snd r))))
                                                 /\ fst(snd(fst3(fst r))) = fst(snd(fst3(snd r)))
                                                 /\ fst(snd(snd3(fst r))) = fst(snd(snd3(snd r)))
                                                 /\ fst(snd(thd3(fst r))) = fst(snd(thd3(snd r)))
                                                    ))
let triple sl0 sl1 sr0 sr1 = let (al,(asl0,asl1)),(ar,(asr0,asr1)) = triple_a sl0 sr0 in
                             let (bl,(bsl0,bsl1)),(br,(bsr0,bsr1)) = triple_a sl1 sr1 in
                             let (cl,(csl0,csl1)),(cr,(csr0,csr1)) = triple_c (al,ar) (bl,br) in
                             cut(b2t(mul_fp al bl = cl));
                             cut(b2t(mul_fp ar br = cr));
                             cut(b2t(al = add_fp asl0 asl1));
                             cut(b2t(ar = add_fp asr0 asr1));
                             cut(b2t(bl = add_fp bsl0 bsl1));
                             cut(b2t(br = add_fp bsr0 bsr1));
                             cut(b2t(cl = add_fp csl0 csl1));
                             cut(b2t(cr = add_fp csr0 csr1));
                             cut(b2t(minus_fp (snd sl0) asl1 = minus_fp (snd sr0) asr1));
                             cut(b2t(minus_fp (snd sl1) bsl1 = minus_fp (snd sr1) bsr1));
                             cut(b2t(asl0 = asr0));
                             cut(b2t(bsl0 = bsr0));
                             cut(b2t(csl0 = csr0));
                             ((al,(asl0,asl1)),(bl,(bsl0,bsl1)),(cl,(csl0,csl1))),
                             ((ar,(asr0,asr1)),(br,(bsr0,bsr1)),(cr,(csr0,csr1)))
#reset-options


module MPC
open Fp
open Sample
open Triples

type shared (secret:fp) = p:(fp * fp){add_fp (fst p) (snd p) = secret}
val share : hl:fp -> hr:fp
            -> Pure ((fp*fp)*(fp*fp))
                   (requires ( True))
                   (ensures  (fun r -> add_fp (fst(fst r)) (snd(fst r)) = hl
                                        /\ add_fp (fst(snd r)) (snd(snd r)) = hr
                                        /\ fst(fst r) = fst(snd r)))
let share hl hr = let sl0, sr0 = sample (fun x -> x) in
                  let sl1, sr1 = minus_fp hl sl0, minus_fp hr sr0 in
                  (sl0, sl1),(sr0, sr1)


opaque val reconstruct : #h0:fp -> #h1:fp -> s0:(fp*fp) -> s1:(fp*fp)
                  -> Pure (fp * fp)
                         (requires ( add_fp (fst s0) (snd s0) = h0 /\
                                             add_fp (fst s1) (snd s1) = h1 /\
                                             fst s0 = fst s1 /\
                                             snd s0 = snd s1))
                         (ensures  (fun r -> fst r = snd r /\
                                                 fst r = h0 /\
                                                 snd r = h1))
let reconstruct _ _  (sl0, sl1) (sr0, sr1) = add_fp sl0 sl1, add_fp sr0 sr1

opaque val add_adv : sl0:fp -> sl1:fp -> sr0:fp -> sr1:fp ->
              Pure (fp * fp)
                  (requires ( sl0 = sr0 /\ sl1 = sr1))
                  (ensures  (fun r -> fst r = snd r /\
                                          fst r = add_fp sl0 sl1 /\
                                          snd r = add_fp sr0 sr1))
let add_adv sl0 sl1 sr0 sr1 = add_fp sl0 sl1, add_fp sr0 sr1

opaque val add_hon : sl0:fp -> sl1:fp -> sr0:fp -> sr1:fp ->
              Pure (fp * fp)
                  (requires ( True))
                  (ensures  (fun r -> fst r = add_fp sl0 sl1 /\
                                          snd r = add_fp sr0 sr1))
let add_hon sl0 sl1 sr0 sr1 = add_fp sl0 sl1, add_fp sr0 sr1

opaque val add_mpc : #hl0:fp -> #hl1:fp -> #hr0:fp -> #hr1:fp
              -> sl0:shared hl0 -> sl1:shared hl1
              -> sr0:shared hr0 -> sr1:shared hr1
(*               -> Pure ((shared (add_fp hl0 hl1)) * (shared (add_fp hr0 hr1))) *)
              -> Pure ((fp*fp)*(fp*fp))
                     (requires ( fst sl0 = fst sr0 /\
                                         fst sl1 = fst sr1))
                     (ensures  (fun r -> fst (fst r) = fst (snd r)
                                          /\ add_fp (fst (fst r)) (snd (fst r)) = add_fp hl0 hl1
                                          /\ add_fp (fst (snd r)) (snd (snd r)) = add_fp hr0 hr1 ))
let add_mpc _ _ _ _ sl0 sl1 sr0 sr1 = let rl0, rr0 = add_adv (fst sl0) (fst sl1) (fst sr0) (fst sr1) in
                                      let rl1, rr1 = add_hon (snd sl0) (snd sl1) (snd sr0) (snd sr1) in
                                      (rl0, rl1), (rr0, rr1)

opaque val scalar_mul_adv : a:fp -> sl:fp -> sr:fp ->
                     Pure (fp * fp)
                         (requires ( sl = sr))
                         (ensures  (fun r -> fst r = snd r /\
                                                 fst r = mul_fp a sl /\
                                                 snd r = mul_fp a sr))
let scalar_mul_adv a sl sr = mul_fp a sl, mul_fp a sr

opaque val scalar_mul_hon : a:fp -> sl:fp -> sr:fp ->
                     Pure (fp * fp)
                         (requires ( True))
                         (ensures  (fun r -> fst r = mul_fp a sl /\
                                                 snd r = mul_fp a sr))
let scalar_mul_hon a sl sr = mul_fp a sl, mul_fp a sr

opaque val scalar_mul_mpc : #hl:fp -> #hr:fp
                     -> a:fp -> sl:shared hl -> sr:shared hr
(*                      -> Pure ((shared (mul_fp a hl)) * (shared (mul_fp a hr))) *)
                     -> Pure ((fp*fp)*(fp*fp))
                            (requires ( fst sl = fst sr))
                            (ensures  (fun r -> fst (fst r) = fst (snd r)
                                                 /\ add_fp (fst (fst r)) (snd (fst r)) = mul_fp a hl
                                                 /\ add_fp (fst (snd r)) (snd (snd r)) = mul_fp a hr ))
let scalar_mul_mpc _ _ a sl sr = let rl0, rr0 = scalar_mul_adv a (fst sl) (fst sr) in
                                 let rl1, rr1 = scalar_mul_hon a (snd sl) (snd sr) in
                                 (rl0, rl1), (rr0, rr1)

opaque val add_const_adv : a:fp -> sl:fp -> sr:fp ->
                    Pure (fp * fp)
                        (requires ( sl = sr))
                        (ensures  (fun r -> fst r = snd r /\
                                                fst r = add_fp a sl /\
                                                snd r = add_fp a sr))
let add_const_adv a sl sr = add_fp a sl, add_fp a sr

opaque val add_const_hon : a:fp -> sl:fp -> sr:fp ->
                    Pure (fp * fp)
                        (requires ( True))
                        (ensures  (fun r -> fst r = add_fp a sl /\
                                                snd r = add_fp a sr))
let add_const_hon a sl sr = add_fp a sl, add_fp a sr

opaque val add_const_mpc : #hl:fp -> #hr:fp
                    -> a:fp -> sl:shared hl -> sr:shared hr
(*                     -> Pure ((shared (add_fp a hl)) * (shared (add_fp a hr))) *)
                    -> Pure ((fp*fp)*(fp*fp))
                           (requires ( fst sl = fst sr))
                           (ensures  (fun r -> fst (fst r) = fst (snd r)
                                                /\ add_fp (fst (fst r)) (snd (fst r)) = add_fp a hl
                                                /\ add_fp (fst (snd r)) (snd (snd r)) = add_fp a hr ))
let add_const_mpc _ _ a sl sr = let rl0, rr0 = add_const_adv a (fst sl) (fst sr) in
                                let rl1, rr1 = add_const_hon (mod_p 0) (snd sl) (snd sr) in
                                (rl0, rl1), (rr0, rr1)

opaque val minus_adv : sl0:fp -> sl1:fp -> sr0:fp -> sr1:fp ->
              Pure (fp * fp)
                  (requires ( sl0 = sr0 /\ sl1 = sr1))
                  (ensures  (fun r -> fst r = snd r /\
                                          fst r = minus_fp sl0 sl1 /\
                                          snd r = minus_fp sr0 sr1))
let minus_adv sl0 sl1 sr0 sr1 = minus_fp sl0 sl1, minus_fp sr0 sr1

opaque val minus_hon : sl0:fp -> sl1:fp -> sr0:fp -> sr1:fp ->
              Pure (fp * fp)
                  (requires ( True))
                  (ensures  (fun r -> fst r = minus_fp sl0 sl1 /\
                                          snd r = minus_fp sr0 sr1))
let minus_hon sl0 sl1 sr0 sr1 = minus_fp sl0 sl1, minus_fp sr0 sr1

opaque val minus_mpc : #hl0:fp -> #hl1:fp -> #hr0:fp -> #hr1:fp
              -> sl0:shared hl0 -> sl1:shared hl1
              -> sr0:shared hr0 -> sr1:shared hr1
(*               -> Pure ((shared (minus_fp hl0 hl1)) * (shared (minus_fp hr0 hr1))) *)
              -> Pure ((fp*fp)*(fp*fp))
                     (requires ( fst sl0 = fst sr0 /\
                                         fst sl1 = fst sr1))
                     (ensures  (fun r -> fst (fst r) = fst (snd r)
                                          /\ add_fp (fst (fst r)) (snd (fst r)) = minus_fp hl0 hl1
                                          /\ add_fp (fst (snd r)) (snd (snd r)) = minus_fp hr0 hr1 ))
let minus_mpc _ _ _ _ sl0 sl1 sr0 sr1 = let rl0, rr0 = minus_adv (fst sl0) (fst sl1) (fst sr0) (fst sr1) in
                                      let rl1, rr1 = minus_hon (snd sl0) (snd sl1) (snd sr0) (snd sr1) in
                                      (rl0, rl1), (rr0, rr1)

#reset-options
opaque val mul_mpc : #hl0:fp -> #hl1:fp -> #hr0:fp -> #hr1:fp
              -> sl0:shared hl0 -> sl1:shared hl1
              -> sr0:shared hr0 -> sr1:shared hr1
(*               -> Pure ((shared (mul_fp hl0 hl1)) * (shared (mul_fp hr0 hr1))) *)
              -> Pure ((fp*fp)*(fp*fp))
                     (requires ( fst sl0 = fst sr0 /\
                                         fst sl1 = fst sr1))
                     (ensures  (fun r -> fst (fst r) = fst (snd r)
                                         /\ add_fp (fst (fst r)) (snd (fst r)) = mul_fp hl0 hl1
                                         /\ add_fp (fst (snd r)) (snd (snd r)) = mul_fp hr0 hr1))
let mul_mpc hl0 hl1 hr0 hr1 sl0 sl1 sr0 sr1 =
                                              let ((al,asl), (bl,bsl), (cl,csl)), ((ar,asr), (br,bsr), (cr,csr)) =
                                                  triple sl0 sl1 sr0 sr1 in
                                              let el', er' = minus_mpc #hl0 #al #hr0 #ar sl0 asl sr0 asr in
                                              assert(fst el' = fst er');
                                              assert (snd el' = snd er');
                                              let el, er = reconstruct  #(minus_fp hl0 al) #(minus_fp hr0 ar) el' er' in
                                              let dl', dr' = minus_mpc #hl1 #bl #hr1 #br sl1 bsl sr1 bsr in let dl, dr = reconstruct  #(minus_fp hl1 bl) #(minus_fp hr1 br) dl' dr' in
                                              let tmp1l, tmp1r = scalar_mul_mpc #al #ar dl asl asr in
                                              let tmp2l, tmp2r = add_mpc #(mul_fp dl al) #cl  #(mul_fp ar dr) #cr tmp1l csl tmp1r csr in
                                              let tmp3l, tmp3r = scalar_mul_mpc #bl #br el bsl bsr in
                                              let tmp4l, tmp4r = add_mpc #(mul_fp el bl) #(add_fp (mul_fp dl al) cl)
                                                                         #(mul_fp er br) #(add_fp (mul_fp dr ar) cr)
                                                                         tmp3l tmp2l tmp3r tmp2r in
                                              let tmp5l, tmp5r = add_const_mpc #(add_fp (mul_fp el bl) (add_fp (mul_fp dl al) cl))
                                                                               #(add_fp (mul_fp er br) (add_fp (mul_fp dr ar) cr))
                                                                               (mul_fp dl el) tmp4l tmp4r in
                                              cut (b2t(add_fp (mul_fp dl el) (add_fp (mul_fp el bl) (add_fp (mul_fp dl al) cl))
                                                              = add_fp (fst tmp5l) (snd tmp5l)));
                                              cut (b2t(add_fp (mul_fp dl el) (add_fp (mul_fp el bl) (add_fp (mul_fp dl al) cl))
                                                              = mul_fp hl0 hl1));
                                              cut (b2t(add_fp (mul_fp dr er) (add_fp (mul_fp er br) (add_fp (mul_fp dr ar) cr))
                                                              = add_fp (fst tmp5r) (snd tmp5r)));
                                              cut (b2t(add_fp (mul_fp dr er) (add_fp (mul_fp er br) (add_fp (mul_fp dr ar) cr))
                                                              = mul_fp hr0 hr1));
                                              cut (b2t(add_fp (fst tmp5l) (snd tmp5l) = mul_fp hl0 hl1));
                                              cut (b2t(add_fp (fst tmp5r) (snd tmp5r) = mul_fp hr0 hr1));
                                              cut (b2t(fst tmp5l = fst tmp5r));
                                              let r = tmp5l, tmp5r in
                                              r
