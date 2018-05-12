module FStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module U32 = FStar.UInt32

noeq
type loc_aux : Type =
  | LocBuffer:
    (#t: Type) ->
    (b: B.buffer t) ->
    loc_aux
  | LocUnion:
    (l1: loc_aux) ->
    (l2: loc_aux) ->
    loc_aux

let rec loc_aux_in_addr
  (l: loc_aux)
  (r: HS.rid)
  (n: nat)
: GTot Type0
  (decreases l)
= match l with
  | LocUnion l1 l2 -> loc_aux_in_addr l1 r n /\ loc_aux_in_addr l2 r n
  | LocBuffer b ->
    B.frameOf b == r /\
    B.as_addr b == n

noeq
type loc' : Type =
  | Loc:
      (regions: Ghost.erased (Set.set HS.rid)) ->
      (addrs: (
	(r: HS.rid) ->
	Ghost (Set.set nat)
	(requires (Set.mem r (Ghost.reveal regions)))
	(ensures (fun _ -> True))
      )) ->
      (aux_addrs: (
	(r: HS.rid) ->
	Ghost (Set.set nat)
	(requires (Set.mem r (Ghost.reveal regions)))
	(ensures (fun y -> Set.subset (Set.intersect y (addrs r)) Set.empty))
      )) ->
      (aux: (
	(r: HS.rid) ->
	(n: nat) ->
	Ghost loc_aux
	(requires (
	  Set.mem r (Ghost.reveal regions) /\
	  Set.mem n (aux_addrs r)
	))
	(ensures (fun y ->
          loc_aux_in_addr y r n
      )))) ->
      loc'

let loc = loc'

let loc_none = Loc
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (fun _ -> Set.empty)
  (fun _ _ -> false_elim ())

let regions_of_loc
  (s: loc)
: GTot (Set.set HS.rid)
= Ghost.reveal (Loc?.regions s)

let addrs_of_loc_weak
  (l: loc)
  (r: HS.rid)
: GTot (Set.set nat)
= if Set.mem r (regions_of_loc l)
  then Loc?.addrs l r
  else Set.empty

let addrs_of_loc_aux
  (l: loc)
  (r: HS.rid)
: GTot (Set.set nat)
= if Set.mem r (regions_of_loc l)
  then Loc?.aux_addrs l r
  else Set.empty

let addrs_of_loc
  (l: loc)
  (r: HS.rid)
: GTot (Set.set nat)
= Set.union
    (addrs_of_loc_weak l r)
    (addrs_of_loc_aux l r)

let addrs_of_loc_aux_prop
  (l: loc)
  (r: HS.rid)
: Lemma
  (Set.subset (Set.intersect (addrs_of_loc_aux l r) (addrs_of_loc_weak l r)) Set.empty)
  [SMTPatOr [
    [SMTPat (addrs_of_loc_aux l r)];
    [SMTPat (addrs_of_loc_weak l r)];
    [SMTPat (addrs_of_loc l r)];
  ]]
= ()

let loc_union s1 s2 =
  if StrongExcludedMiddle.strong_excluded_middle (s1 == s2)
  then s1
  else
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in
  let regions = Set.union regions1 regions2 in
  let addrs
    (r: HS.rid)
  : Ghost (Set.set nat)
    (requires (Set.mem r regions))
    (ensures (fun _ -> True))
  = Set.union
      (if Set.mem r regions1 then Loc?.addrs s1 r else Set.empty)
      (if Set.mem r regions2 then Loc?.addrs s2 r else Set.empty)
  in
  let aux_addrs
    (r: HS.rid)
  : Ghost (Set.set nat)
    (requires (Set.mem r regions))
    (ensures (fun y -> Set.subset (Set.intersect y (addrs r)) Set.empty))
  = Set.intersect
      (Set.union (addrs_of_loc_aux s1 r) (addrs_of_loc_aux s2 r))
      (Set.complement (addrs r))
  in
  let aux
    (r: HS.rid)
    (n: nat)
  : Ghost loc_aux
    (requires (Set.mem r regions /\ Set.mem n (aux_addrs r)))
    (ensures (fun y -> loc_aux_in_addr y r n))
  = let l1 =
      if Set.mem r regions1 && Set.mem n (Loc?.aux_addrs s1 r)
      then Some (Loc?.aux s1 r n)
      else None
    in
    let l2 =
      if Set.mem r regions2 && Set.mem n (Loc?.aux_addrs s2 r)
      then Some (Loc?.aux s2 r n)
      else None
    in
    match l1, l2 with
    | Some l1, Some l2 -> LocUnion l1 l2
    | Some l1, _ -> l1
    | _, Some l2 -> l2
  in
  Loc
    (Ghost.hide regions)
    addrs
    aux_addrs
    aux

let loc_union_idem s = ()

let loc_buffer #t b =
    Loc
      (Ghost.hide (Set.singleton (B.frameOf b)))
      (fun _ -> Set.empty)
      (fun _ -> Set.singleton (B.as_addr b))
      (fun _ _ -> LocBuffer b)

let loc_addresses r n =
  Loc
    (Ghost.hide (Set.singleton r))
    (fun _ -> n)
    (fun _ -> Set.empty)
    (fun _ _ -> false_elim ())

let loc_regions r =
  Loc
    (Ghost.hide r)
    (fun r' -> if Set.mem r' r then Set.complement Set.empty else Set.empty)
    (fun _ -> Set.empty)
    (fun _ _ -> false_elim ())

let rec loc_aux_includes_buffer
  (#a: Type)
  (s: loc_aux)
  (b: B.buffer a)
: GTot Type0
  (decreases s)
= match s with
  | LocUnion s1 s2 -> loc_aux_includes_buffer s1 b \/ loc_aux_includes_buffer s2 b
  | LocBuffer #a0 b0 -> a == a0 /\ b0 `B.includes` b

let rec loc_aux_includes
  (s1 s2: loc_aux)
: GTot Type0
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r -> loc_aux_includes s1 s2l /\ loc_aux_includes s1 s2r
  | LocBuffer b -> loc_aux_includes_buffer s1 b

let rec loc_aux_includes_union_l
  (s1 s2 s: loc_aux)
: Lemma
  (requires (loc_aux_includes s1 s \/ loc_aux_includes s2 s))
  (ensures (loc_aux_includes (LocUnion s1 s2) s))
  (decreases s)
= match s with 
  | LocUnion sl sr -> loc_aux_includes_union_l s1 s2 sl; loc_aux_includes_union_l s1 s2 sr
  | _ -> ()

let rec loc_aux_includes_refl
  (s: loc_aux)
: Lemma
  (loc_aux_includes s s)
= match s with
  | LocUnion sl sr ->
    loc_aux_includes_refl sl;
    loc_aux_includes_refl sr;
    loc_aux_includes_union_l sl sr sl;
    loc_aux_includes_union_l sl sr sr
  | _ -> ()

let loc_aux_includes_union_l_r
  (s s': loc_aux)
: Lemma
  (loc_aux_includes (LocUnion s s') s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s s' s

let loc_aux_includes_union_l_l
  (s s': loc_aux)
: Lemma
  (loc_aux_includes (LocUnion s' s) s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s' s s

let rec loc_aux_includes_buffer_includes
  (#a: Type)
  (s: loc_aux)
  (b1 b2: B.buffer a)
: Lemma
  (requires (loc_aux_includes_buffer s b1 /\ b1 `B.includes` b2))
  (ensures (loc_aux_includes_buffer s b2))
  (decreases s)
= match s with
  | LocUnion sl sr ->
    Classical.or_elim
      #(loc_aux_includes_buffer sl b1)
      #(loc_aux_includes_buffer sr b1)
      #(fun _ -> loc_aux_includes_buffer s b2)
      (fun _ -> loc_aux_includes_buffer_includes sl b1 b2)
      (fun _ -> loc_aux_includes_buffer_includes sr b1 b2)
  | _ -> ()

let rec loc_aux_includes_loc_aux_includes_buffer
  (#a: Type)
  (s1 s2: loc_aux)
  (b: B.buffer a)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_buffer s2 b))
  (ensures (loc_aux_includes_buffer s1 b))
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r ->
    Classical.or_elim
      #(loc_aux_includes_buffer s2l b)
      #(loc_aux_includes_buffer s2r b)
      #(fun _ -> loc_aux_includes_buffer s1 b)
      (fun _ -> loc_aux_includes_loc_aux_includes_buffer s1 s2l b)
      (fun _ -> loc_aux_includes_loc_aux_includes_buffer s1 s2r b)
  | LocBuffer b2 -> loc_aux_includes_buffer_includes s1 b2 b

let rec loc_aux_includes_trans
  (s1 s2 s3: loc_aux)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
  (decreases s3)
= match s3 with
  | LocUnion s3l s3r ->
    loc_aux_includes_trans s1 s2 s3l;
    loc_aux_includes_trans s1 s2 s3r
  | LocBuffer b -> loc_aux_includes_loc_aux_includes_buffer s1 s2 b

(* the following is necessary because `decreases` messes up 2nd-order unification with `Classical.forall_intro_3` *)

let loc_aux_includes_trans'
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  ((loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3) ==> loc_aux_includes s1 s3)
= Classical.move_requires (loc_aux_includes_trans s1 s2) s3

let addrs_of_loc_weak_loc_union
  (l1 l2: loc)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (loc_union l1 l2) r == Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r))
  [SMTPat (addrs_of_loc_weak (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc_weak (loc_union l1 l2) r) (Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r)))

let addrs_of_loc_union
  (l1 l2: loc)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (loc_union l1 l2) r == Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r))
  [SMTPat (addrs_of_loc (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc (loc_union l1 l2) r) (Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r)))

let loc_includes s1 s2 =
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in (
    Set.subset regions2 regions1 /\ (
      forall (r: HS.rid) .
      Set.subset (addrs_of_loc_weak s2 r) (addrs_of_loc_weak s1 r)
    ) /\ (
      forall (r: HS.rid) .
      Set.subset (addrs_of_loc s2 r) (addrs_of_loc s1 r)
    ) /\ (
      forall (r: HS.rid) (n: nat) .
      (Set.mem r regions2 /\ Set.mem n (addrs_of_loc_aux s2 r) /\ Set.mem n (addrs_of_loc_aux s1 r)) ==>
      loc_aux_includes (Loc?.aux s1 r n) (Loc?.aux s2 r n)
  ))

let loc_includes_refl s =
  let pre
    (r: HS.rid)
    (n: nat)
  : GTot Type0
  = Set.mem r (regions_of_loc s) /\
    Set.mem n (Loc?.aux_addrs s r)
  in
  let post
    (r: HS.rid)
    (n: nat)
  : GTot Type0
  = pre r n /\
    loc_aux_includes (Loc?.aux s r n) (Loc?.aux s r n)
  in
  let f
    (r: HS.rid)
    (n: nat)
  : Lemma
    (requires (pre r n))
    (ensures (post r n))
  = loc_aux_includes_refl (Loc?.aux s r n)
  in
  Classical.forall_intro_2 (fun r -> Classical.move_requires (f r))

let loc_includes_trans s1 s2 s3 =
  Classical.forall_intro_3 loc_aux_includes_trans'

let loc_includes_union_r s s1 s2 = ()

let loc_includes_union_l s1 s2 s =
  let u12 = loc_union s1 s2 in
  if StrongExcludedMiddle.strong_excluded_middle (s1 == s2)
  then ()
  else begin
    Classical.forall_intro loc_aux_includes_refl;
    Classical.forall_intro_2 loc_aux_includes_union_l_l;
    Classical.forall_intro_2 loc_aux_includes_union_l_r;
    Classical.or_elim
      #(loc_includes s1 s)
      #(loc_includes s2 s)
      #(fun _ -> loc_includes (loc_union s1 s2) s)
      (fun _ -> loc_includes_trans u12 s1 s)
      (fun _ -> loc_includes_trans u12 s2 s)
  end

let loc_includes_none s = ()

let loc_includes_buffer #t b1 b2 = ()

let loc_includes_gsub_buffer_r l #t b i len =
  loc_includes_trans l (loc_buffer b) (loc_buffer (B.sub b i len))

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 = ()

let loc_includes_addresses_buffer #t r s p = ()

let loc_includes_region_buffer #t s b = ()

let loc_includes_region_addresses s r a = ()

let loc_includes_region_region s1 s2 = ()

#set-options "--z3rlimit 16"

let loc_includes_region_union_l l s1 s2 = ()

#reset-options


(* Disjointness of two memory locations *)

let rec loc_aux_disjoint_buffer
  (l: loc_aux)
  (#t: Type)
  (p: B.buffer t)
: GTot Type0
  (decreases l)
= match l with
  | LocUnion ll lr ->
    loc_aux_disjoint_buffer ll p /\ loc_aux_disjoint_buffer lr p
  | LocBuffer b -> B.disjoint b p

let rec loc_aux_disjoint
  (l1 l2: loc_aux)
: GTot Type0
  (decreases l2)
= match l2 with
  | LocUnion ll lr ->
    loc_aux_disjoint l1 ll /\ loc_aux_disjoint l1 lr
  | LocBuffer b ->
    loc_aux_disjoint_buffer l1 b

let rec loc_aux_disjoint_union_l
  (ll1 lr1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint (LocUnion ll1 lr1) l2 <==> (loc_aux_disjoint ll1 l2 /\ loc_aux_disjoint lr1 l2)))
  (decreases l2)
= match l2 with
  | LocUnion ll2 lr2 ->
    loc_aux_disjoint_union_l ll1 lr1 ll2;
    loc_aux_disjoint_union_l ll1 lr1 lr2
  | _ -> ()

let loc_aux_disjoint_union_r
  (l1 ll2 lr2: loc_aux)
: Lemma
  (loc_aux_disjoint l1 (LocUnion ll2 lr2) <==> (loc_aux_disjoint l1 ll2 /\ loc_aux_disjoint l1 lr2))
= ()

let rec loc_aux_size
  (l: loc_aux)
: GTot nat
= match l with
  | LocUnion l1 l2 ->
    let n1 = loc_aux_size l1 in
    let n2 = loc_aux_size l2 in
    1 + (if n1 > n2 then n1 else n2)
  | _ -> 0

let rec loc_aux_disjoint_sym
  (l1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
  (decreases (loc_aux_size l1 + loc_aux_size l2))
= match l2 with
  | LocUnion ll lr ->
    loc_aux_disjoint_union_r l1 ll lr;
    loc_aux_disjoint_sym l1 ll;
    loc_aux_disjoint_sym l1 lr;
    loc_aux_disjoint_union_l ll lr l1
  | _ ->
    begin match l1 with
    | LocUnion ll lr ->
      loc_aux_disjoint_union_l ll lr l2;
      loc_aux_disjoint_sym ll l2;
      loc_aux_disjoint_sym lr l2;
      loc_aux_disjoint_union_r l2 ll lr
    | _ -> ()
    end

(* Same problem with decreases here *)

let loc_aux_disjoint_sym'
  (l1 l2: loc_aux)
: Lemma
  (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1)
= loc_aux_disjoint_sym l1 l2

let regions_of_loc_loc_union
  (s1 s2: loc)
: Lemma
  (regions_of_loc (loc_union s1 s2) == regions_of_loc s1 `Set.union` regions_of_loc s2)
  [SMTPat (regions_of_loc (loc_union s1 s2))]
= assert (regions_of_loc (loc_union s1 s2) `Set.equal` (regions_of_loc s1 `Set.union` regions_of_loc s2))

let regions_of_loc_monotonic
  (s1 s2: loc)
: Lemma
  (requires (loc_includes s1 s2))
  (ensures (Set.subset (regions_of_loc s2) (regions_of_loc s1)))
= ()

let loc_disjoint'
  (l1 l2: loc)
: GTot Type0
= (forall (r: HS.rid) .
      Set.subset (Set.intersect (addrs_of_loc_weak l1 r) (addrs_of_loc l2 r)) Set.empty /\
      Set.subset (Set.intersect (addrs_of_loc l1 r) (addrs_of_loc_weak l2 r)) Set.empty
  ) /\
  (forall (r: HS.rid) (n: nat) .
    (Set.mem r (regions_of_loc l1) /\ Set.mem n (addrs_of_loc_aux l1 r) /\
     Set.mem r (regions_of_loc l2) /\ Set.mem n (addrs_of_loc_aux l2 r)) ==>
    loc_aux_disjoint (Loc?.aux l1 r n) (Loc?.aux l2 r n)
  )

let loc_disjoint = loc_disjoint'

let loc_disjoint_sym l1 l2 =
  Classical.forall_intro_2 loc_aux_disjoint_sym'

let loc_disjoint_none_r s = ()

let loc_disjoint_union_r s s1 s2 = ()

let rec loc_aux_disjoint_buffer_includes
  (l: loc_aux)
  (#t: Type)
  (p1: B.buffer t)
  (p2: B.buffer t)
: Lemma
  (requires (loc_aux_disjoint_buffer l p1 /\ p1 `B.includes` p2))
  (ensures (loc_aux_disjoint_buffer l p2))
  (decreases l)
= match l with
  | LocUnion ll lr ->
    loc_aux_disjoint_buffer_includes ll p1 p2;
    loc_aux_disjoint_buffer_includes lr p1 p2
  | _ -> ()

let rec loc_aux_disjoint_loc_aux_includes_buffer
  (l1 l2: loc_aux)
  (#t3: Type)
  (b3: B.buffer t3)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes_buffer l2 b3))
  (ensures (loc_aux_disjoint_buffer l1 b3))
  (decreases l2)
= match l2 with
  | LocUnion l2l l2r ->
    Classical.or_elim
      #(loc_aux_includes_buffer l2l b3)
      #(loc_aux_includes_buffer l2r b3)
      #(fun _ -> loc_aux_disjoint_buffer l1 b3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_buffer l1 l2l b3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_buffer l1 l2r b3)
  | LocBuffer b2 -> loc_aux_disjoint_buffer_includes l1 b2 b3

let rec loc_aux_disjoint_loc_aux_includes
  (l1 l2 l3: loc_aux)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
  (decreases l3)
= match l3 with
  | LocUnion ll3 lr3 ->
    loc_aux_disjoint_loc_aux_includes l1 l2 ll3;
    loc_aux_disjoint_loc_aux_includes l1 l2 lr3
  | LocBuffer b3 ->
    loc_aux_disjoint_loc_aux_includes_buffer l1 l2 b3

let loc_disjoint_includes p1 p2 p1' p2' =
  regions_of_loc_monotonic p1 p1';
  regions_of_loc_monotonic p2 p2';
  let pre = //A rather brutal way to force inlining of pre and post in VC of the continuation
    (fun r n ->
      Set.mem r (regions_of_loc p1') /\ Set.mem n (addrs_of_loc_aux p1' r) /\
      Set.mem r (regions_of_loc p2') /\ Set.mem n (addrs_of_loc_aux p2' r))
    <: Tot ((r:HS.rid) -> (n:nat) -> GTot Type0)
  in
  let post =
    (fun r n ->
       pre r n /\
       loc_aux_disjoint (Loc?.aux p1' r n) (Loc?.aux p2' r n))
    <: Tot ((r:HS.rid) -> (n:nat) -> GTot Type0)
  in
  let f
    (r: HS.rid)
    (n: nat)
  : Lemma
    (requires (pre r n))
    (ensures (post r n))
  = let l1 = Loc?.aux p1 r n in
    let l2 = Loc?.aux p2 r n in
    let l1' = Loc?.aux p1' r n in
    let l2' = Loc?.aux p2' r n in
    loc_aux_disjoint_loc_aux_includes l1 l2 l2';
    loc_aux_disjoint_sym l1 l2';
    loc_aux_disjoint_loc_aux_includes l2' l1 l1';
    loc_aux_disjoint_sym l2' l1'
  in
  Classical.forall_intro_2 (fun r -> Classical.move_requires (f r))

let loc_disjoint_buffer #t1 #t2 b1 b2 = ()

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 = ()

let loc_disjoint_addresses r1 r2 n1 n2 = ()

let loc_disjoint_buffer_addresses #t p r n = ()

let loc_disjoint_regions rs1 rs2 = ()


(** The modifies clause proper *)

let modifies_preserves_mreferences
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) .
    let r = HS.frameOf p in (
      HS.contains h1 p /\
      (Set.mem r (regions_of_loc s) ==> ~ (Set.mem (HS.as_addr p) (addrs_of_loc s r)))
    ) ==> (
      HS.contains h2 p /\
      HS.sel h2 p == HS.sel h1 p
  ))

let modifies_preserves_buffers
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (b: B.buffer t) .
    let r = B.frameOf b in
    let a = B.as_addr b in (
      B.live h1 b /\
      B.length b <> 0 /\
      (Set.mem r (regions_of_loc s) ==> ~ (Set.mem a (addrs_of_loc_weak s r))) /\
      ((Set.mem r (regions_of_loc s) /\ Set.mem a (addrs_of_loc_aux s r)) ==> loc_aux_disjoint_buffer (Loc?.aux s r a) b)
    ) ==> (
      B.live h2 b /\
      B.as_seq h2 b == B.as_seq h1 b
  ))

let modifies'
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_preserves_mreferences s h1 h2 /\
  modifies_preserves_buffers s h1 h2

let modifies = modifies'

let modifies_mreference_elim #t #pre b p h h' = ()

let modifies_buffer_elim #t1 b p h h' = ()

let modifies_refl s h = ()

let loc_aux_disjoint_buffer_loc_aux_includes
  (l1: loc_aux)
: Lemma
  (forall (l2: loc_aux)
    (t3: Type)
    (b3: B.buffer t3) .
  (loc_aux_disjoint_buffer l1 b3 /\ loc_aux_includes l1 l2) ==> loc_aux_disjoint_buffer l2 b3)
= let f
  (l2: loc_aux)
  (t3: Type)
  (b3: B.buffer t3)
  : Lemma
    (requires (loc_aux_disjoint_buffer l1 b3 /\ loc_aux_includes l1 l2))
    (ensures (loc_aux_disjoint_buffer l2 b3))
  = loc_aux_disjoint_sym (LocBuffer b3) l1;
    loc_aux_disjoint_loc_aux_includes (LocBuffer b3) l1 l2;
    loc_aux_disjoint_sym (LocBuffer b3) l2
  in
  Classical.forall_intro_3 (fun (l2: loc_aux) (t3: Type) (b3: B.buffer t3) -> Classical.move_requires (f l2 t3) b3)

#set-options "--z3rlimit 32"

let modifies_loc_includes s1 h h' s2 =
  assert (modifies_preserves_mreferences s1 h h');
  Classical.forall_intro loc_aux_disjoint_buffer_loc_aux_includes;
  assert (modifies_preserves_buffers s1 h h')

#reset-options

let modifies_trans'
  (s: loc)
  (h1 h2: HS.mem)
  (h3: HS.mem)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
= ()

let modifies_trans s12 h1 h2 s23 h3 =
  let u = loc_union s12 s23 in
  modifies_loc_includes u h1 h2 s12;
  modifies_loc_includes u h2 h3 s23;
  modifies_trans' u h1 h2 h3

// #set-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

#set-options "--z3rlimit 32"

let modifies_only_live_regions_weak
  (rs: Set.set HS.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    loc_disjoint (loc_regions rs) l /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))
= ()

#reset-options

(* Restrict a set of locations along a set of regions *)

let restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: GTot loc
= let (Loc regions addrs aux_addrs aux) = l in
  Loc
    (Ghost.hide (Set.intersect (Ghost.reveal regions) rs))
    (fun r -> addrs r)
    (fun r -> aux_addrs r)
    (fun r n -> aux r n)

let regions_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (regions_of_loc (restrict_to_regions l rs) == Set.intersect (regions_of_loc l) rs)
  [SMTPat (regions_of_loc (restrict_to_regions l rs))]
= assert (Set.equal (regions_of_loc (restrict_to_regions l rs)) (Set.intersect (regions_of_loc l) rs))

let addrs_of_loc_weak_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))
  [SMTPat (addrs_of_loc_weak (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc_weak (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))

let addrs_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc l r else Set.empty))
  [SMTPat (addrs_of_loc (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc l r else Set.empty))

let loc_includes_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes l (restrict_to_regions l rs))
= Classical.forall_intro loc_aux_includes_refl

#set-options "--z3rlimit 32"

let loc_includes_loc_union_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_union (restrict_to_regions l rs) (restrict_to_regions l (Set.complement rs))) l)
= Classical.forall_intro loc_aux_includes_refl

#reset-options

let loc_includes_loc_regions_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions rs) (restrict_to_regions l rs))
= Classical.forall_intro loc_aux_includes_refl

let modifies_only_live_regions rs l h h' =
  let s = l in
  let c_rs = Set.complement rs in
  let s_rs = restrict_to_regions s rs in
  let s_c_rs = restrict_to_regions s c_rs in
  let lrs = loc_regions rs in
  loc_includes_loc_regions_restrict_to_regions s rs;
  loc_includes_union_l lrs s_c_rs s_rs;
  loc_includes_refl s_c_rs;
  loc_includes_union_l lrs s_c_rs s_c_rs;
  loc_includes_union_r (loc_union lrs s_c_rs) s_rs s_c_rs;
  loc_includes_loc_union_restrict_to_regions s rs;
  loc_includes_trans (loc_union lrs s_c_rs) (loc_union s_rs s_c_rs) s;
  modifies_loc_includes (loc_union lrs s_c_rs) h h' (loc_union lrs s);
  loc_includes_loc_regions_restrict_to_regions s c_rs;
  loc_disjoint_regions rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
  modifies_only_live_regions_weak rs s_c_rs h h';
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h h' s_c_rs

let no_upd_fresh_region r l h0 h1 =
  modifies_only_live_regions (HS.mod_set (Set.singleton r)) l h0 h1

let modifies_fresh_frame_popped h0 h1 s h2 h3 =
  modifies_loc_includes s h0 h1 loc_none;
  let s' = loc_union (loc_all_regions_from h1.HS.tip) s in
  modifies_loc_includes s' h2 h3 (loc_region_only h2.HS.tip);
  modifies_trans' s' h1 h2 h3;
  modifies_only_live_regions (HS.mod_set (Set.singleton h1.HS.tip)) s h0 h3

let modifies_loc_regions_intro rs h1 h2 = ()

#set-options "--z3rlimit 16"

let modifies_loc_addresses_intro_weak
  (r: HS.rid)
  (s: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only r) l) h1 h2 /\
    HS.modifies_ref r s h1 h2 /\
    loc_disjoint l (loc_region_only r)
  ))
  (ensures (modifies (loc_union (loc_addresses r s) l) h1 h2))
= assert (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) . (HS.frameOf p == r /\ HS.contains h1 p /\ ~ (Set.mem (HS.as_addr p) s)) ==> (HS.contains h2 p /\ HS.sel h2 p == HS.sel h1 p));
  assert (modifies_preserves_mreferences (loc_union (loc_addresses r s) l) h1 h2);
  assert (modifies_preserves_buffers (loc_union (loc_addresses r s) l) h1 h2)

#reset-options

#set-options "--z3rlimit 32"

let modifies_loc_addresses_intro r s l h1 h2 =
  loc_includes_loc_regions_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  assert (modifies (loc_union (loc_region_only r) (loc_union (restrict_to_regions l (Set.singleton r)) (restrict_to_regions l (Set.complement (Set.singleton r))))) h1 h2);
  modifies_loc_addresses_intro_weak r s (restrict_to_regions l (Set.complement (Set.singleton r))) h1 h2;
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r))

#reset-options

let modifies_ralloc_post #a #rel i init h x h' = ()

let modifies_salloc_post #a #rel init h x h' = ()

let modifies_free #a #rel r m = ()

let modifies_none_modifies h1 h2 = ()

let modifies_buffer_none_modifies h1 h2 = ()

let modifies_0_modifies h1 h2 =
  B.lemma_reveal_modifies_0 h1 h2

let modifies_1_modifies #a b h1 h2 =
  B.lemma_reveal_modifies_1 b h1 h2

let modifies_2_modifies #a1 #a2 b1 b2 h1 h2 =
  B.lemma_reveal_modifies_2 b1 b2 h1 h2

#set-options "--z3rlimit 32"

let modifies_3_modifies #a1 #a2 #a3 b1 b2 b3 h1 h2 =
  B.lemma_reveal_modifies_3 b1 b2 b3 h1 h2

#reset-options

let modifies_buffer_rcreate_post_common #a r init len b h0 h1 = ()

let mreference_live_buffer_unused_in_disjoint #t1 #pre #t2 h b1 b2 = ()

let buffer_live_mreference_unused_in_disjoint #t1 #t2 #pre h b1 b2 = ()


let does_not_contain_addr' (h: HS.mem) (ra: HS.rid * nat) : GTot Type0 =
  forall (a: Type) (rel: Preorder.preorder a) (r: HS.mreference a rel) . {:pattern (h `HS.contains` r) } (HS.frameOf r == fst ra /\ HS.as_addr r == snd ra /\ h `HS.contains` r) ==> False

let does_not_contain_addr = does_not_contain_addr'

let not_live_region_does_not_contain_addr h ra = ()

let unused_in_does_not_contain_addr h #a #rel r = ()

let addr_unused_in_does_not_contain_addr h ra = ()

let free_does_not_contain_addr #a #rel r m x = ()

let does_not_contain_addr_elim #a #rel r m x = ()

#set-options "--z3rlimit 16"

let modifies_only_live_addresses_weak
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses r a) l) h h' /\
    loc_disjoint (loc_addresses r a) l /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))
= assert (modifies_preserves_mreferences l h h')

#reset-options

(* Restrict a set of locations along a set of addresses in a given region *)

let restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
: Ghost loc
  (requires (loc_region_only r `loc_includes` l))
  (ensures (fun _ -> True))
= let (Loc regions addrs aux_addrs aux) = l in
  let aux_addrs' = if Set.mem r (Ghost.reveal regions) then Set.intersect (aux_addrs r) as else Set.empty in
    Loc
      (Ghost.hide (Set.intersect (Ghost.reveal regions) (Set.singleton r)))
      (fun _ -> if Set.mem r (Ghost.reveal regions) then Set.intersect (addrs r) as else Set.empty)
      (fun _ -> aux_addrs')
      (fun r n -> aux r n)

let regions_of_loc_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (regions_of_loc (restrict_to_addresses l r as) == Set.intersect (regions_of_loc l) (Set.singleton r)))
  [SMTPat (regions_of_loc (restrict_to_addresses l r as))]
= assert (regions_of_loc (restrict_to_addresses l r as) `Set.equal` Set.intersect (regions_of_loc l) (Set.singleton r))

let addrs_of_loc_weak_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
  (r' : HS.rid)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (addrs_of_loc_weak (restrict_to_addresses l r as) r' == (if r = r' then Set.intersect (addrs_of_loc_weak l r) as else Set.empty)))
  [SMTPat (addrs_of_loc_weak (restrict_to_addresses l r as) r')]
= assert (addrs_of_loc_weak (restrict_to_addresses l r as) r `Set.equal` Set.intersect (addrs_of_loc_weak l r) as)

let addrs_of_loc_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
  (r' : HS.rid)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (addrs_of_loc (restrict_to_addresses l r as) r' == (if r = r' then Set.intersect (addrs_of_loc l r) as else Set.empty)))
  [SMTPat (addrs_of_loc (restrict_to_addresses l r as) r')]
= assert (addrs_of_loc (restrict_to_addresses l r as) r `Set.equal` Set.intersect (addrs_of_loc l r) as);
  assert (r <> r' ==> addrs_of_loc (restrict_to_addresses l r as) r' `Set.equal` Set.empty)

let loc_includes_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_includes l (restrict_to_addresses l r as)))
= Classical.forall_intro loc_aux_includes_refl

let loc_includes_loc_union_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_includes (loc_union (restrict_to_addresses l r as) (restrict_to_addresses l r (Set.complement as))) l))
= Classical.forall_intro loc_aux_includes_refl

let loc_includes_loc_addresses_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_includes (loc_addresses r as) (restrict_to_addresses l r as)))
= Classical.forall_intro loc_aux_includes_refl

#set-options "--z3rlimit 64"

let modifies_only_live_addresses r a l h h' =
  let l_r = restrict_to_regions l (Set.singleton r) in
  let l_not_r = restrict_to_regions l (Set.complement (Set.singleton r)) in
  let l_a = restrict_to_addresses l_r r a in
  let l_r_not_a = restrict_to_addresses l_r r (Set.complement a) in
  let l_not_a = loc_union l_r_not_a l_not_r in
  let l' = loc_union (loc_addresses r a) l_not_a in
  loc_includes_loc_addresses_restrict_to_addresses l_r r a;
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_addresses l_r r a;
  loc_includes_trans (loc_union (loc_union l_a l_r_not_a) l_not_r) (loc_union l_r l_not_r) l;
  loc_includes_trans (loc_union l_a l_not_a) (loc_union (loc_union l_a l_r_not_a) l_not_r) l;
  loc_includes_trans l' (loc_union l_a l_not_a) l;
  modifies_loc_includes (loc_union (loc_addresses r a) l_not_a) h h' (loc_union (loc_addresses r a) l);

  assume (
    let l1 = loc_addresses r a in
    let l2 = l_not_a in
    (forall (r: HS.rid) .
       Set.subset (Set.intersect (addrs_of_loc_weak l1 r) (addrs_of_loc l2 r)) Set.empty /\
       Set.subset (Set.intersect (addrs_of_loc l1 r) (addrs_of_loc_weak l2 r)) Set.empty));

  modifies_only_live_addresses_weak r a l_not_a h h';
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_includes_restrict_to_addresses l_r r (Set.complement a);
  modifies_loc_includes l h h' l_not_a

#reset-options
