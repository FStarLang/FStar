module Bug4663_A

(* Definitions for Bug4663_B; see there. *)

noeq type st (a: Type0) = { f: Seq.seq a }

unfold type word = nat

(* A deep, non-recursive call graph whose full unfolding is exponential in size:
   each step uses its argument twice. *)
let r0 (#a: Type0) (s: st a) : st a = { f = Seq.append s.f s.f }
let r1 (#a: Type0) (s: st a) : st a = r0 (r0 s)
let r2 (#a: Type0) (s: st a) : st a = r1 (r1 s)
let r3 (#a: Type0) (s: st a) : st a = r2 (r2 s)
let r4 (#a: Type0) (s: st a) : st a = r3 (r3 s)
let r5 (#a: Type0) (s: st a) : st a = r4 (r4 s)
let r6 (#a: Type0) (s: st a) : st a = r5 (r5 s)
let r7 (#a: Type0) (s: st a) : st a = r6 (r6 s)
let r8 (#a: Type0) (s: st a) : st a = r7 (r7 s)
let r9 (#a: Type0) (s: st a) : st a = r8 (r8 s)
let r10 (#a: Type0) (s: st a) : st a = r9 (r9 s)
let r11 (#a: Type0) (s: st a) : st a = r10 (r10 s)
let r12 (#a: Type0) (s: st a) : st a = r11 (r11 s)
let r13 (#a: Type0) (s: st a) : st a = r12 (r12 s)
let r14 (#a: Type0) (s: st a) : st a = r13 (r13 s)
let r15 (#a: Type0) (s: st a) : st a = r14 (r14 s)
let r16 (#a: Type0) (s: st a) : st a = r15 (r15 s)
let r17 (#a: Type0) (s: st a) : st a = r16 (r16 s)
let r18 (#a: Type0) (s: st a) : st a = r17 (r17 s)
let r19 (#a: Type0) (s: st a) : st a = r18 (r18 s)
let r20 (#a: Type0) (s: st a) : st a = r19 (r19 s)
let r21 (#a: Type0) (s: st a) : st a = r20 (r20 s)
let r22 (#a: Type0) (s: st a) : st a = r21 (r21 s)
let r23 (#a: Type0) (s: st a) : st a = r22 (r22 s)
let r24 (#a: Type0) (s: st a) : st a = r23 (r23 s)

let kf (#a: Type0) (s: st a) : st a = r24 s

let g (x: Seq.seq word) (k: nat) (y: Seq.seq word)
  : Pure nat (requires Seq.length y > k) (ensures fun _ -> True) = k
