module LowStar.RST.Loops


module R = LowStar.Resource
module RST = LowStar.RST
module A = LowStar.Array
module AR = LowStar.RST.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = LowStar.Permissions
module U32 = FStar.UInt32

open FStar.Mul

let rec while res inv guard test body =
  if test () then begin
    body ();
    while res inv guard test body
  end


val for:
  start:U32.t ->
  finish:U32.t{U32.v finish >= U32.v start} ->
  inv:(h:HS.mem -> nat -> Type0) ->
  f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> RST unit
    (empty_resource)
    (fun _ -> empty_resource)
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h_1 _ h_2 -> U32.(inv h_1 (v i) /\ inv h_2 (v i + 1))))
  ) ->
  RST unit
    (empty_resource)
    (fun _ -> empty_resource)
    (requires (fun h -> inv h (U32.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (U32.v finish)))

let rec for start finish inv f =
  if start = finish then
    ()
  else begin
    f start;
    for (U32.(start +^ 1ul)) finish inv f
  end

val for_each:
  #a: Type ->
  b: A.array a ->
  #inv:(h:HS.mem -> i:nat -> Type) ->
  f: (i:U32.t{U32.v i < A.vlength b} -> x:a -> RST unit
    (empty_resource)
    (fun _ -> empty_resource)
    (fun h0 -> inv h0 (U32.v i) /\ x == Seq.index (A.as_seq h0 b) (U32.v i))
    (fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1))
  ) ->
  RST unit
    (R.(AR.array_resource b))
    (fun _ -> R.(AR.array_resource b))
    (fun h0 -> inv h0 0)
    (fun h0 _ h1 -> inv h1 (A.vlength b) /\
      R.sel (R.view_of (AR.array_resource b)) h0 ==
      R.sel (R.view_of (AR.array_resource b)) h1
    )

let for_each #a b #inv f =
  (**) let hinit = HST.get () in
  (**) let correct_inv = fun h i -> inv h i /\
  (**)  R.sel (R.view_of (AR.array_resource b)) hinit ==
  (**)  R.sel (R.view_of (AR.array_resource b)) h
  (**) in
  let correct_f (i:U32.t{U32.(0 <= v i /\ v i < A.vlength b)})
    : RST unit
      (R.(AR.array_resource b))
      (fun _ -> R.(AR.array_resource b))
      (requires (fun h0 ->
        correct_inv h0 (U32.v i)
      ))
      (ensures (fun h0 _ h1 ->
        U32.(correct_inv h0 (v i) /\ correct_inv h1 (v i + 1))
      ))
   =
     let x = RST.rst_frame
       (R.(AR.array_resource b))
       (fun _ -> R.(AR.array_resource b))
       (fun _ -> AR.index b i)
     in
     admit();
     RST.rst_frame
       (R.(AR.array_resource b))
       #empty_resource
       (fun _ -> R.(AR.array_resource b))
       #(fun _ -> empty_resource)
       #(AR.array_resource b)
       #(fun h0 -> inv h0 (U32.v i) /\ x == Seq.index (A.as_seq h0 b) (U32.v i))
       #(fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1))
       (fun _ -> let f' = f i x in f')
  in
  admit();
  for
    0ul
    (A.length b)
    correct_inv
    correct_f

val mapi:
  #a: Type ->
  #a': Type ->
  output: A.array a' ->
  input: A.array a{A.length output = A.length input} ->
  #spec_f:(i:nat -> a -> GTot a') ->
  f: (i:U32.t{U32.v i < A.vlength input} -> x:a -> RST a'
    (empty_resource)
    (fun _ -> empty_resource)
    (fun h0 -> x == Seq.index (A.as_seq h0 input) (U32.v i))
    (fun h0 y h1 -> y == spec_f (U32.v i) x)
  ) ->
  RST unit
    (R.(AR.array_resource output <*> AR.array_resource input))
    (fun _ -> R.(AR.array_resource output <*> AR.array_resource input))
    (fun h0 -> P.allows_write (R.sel (R.view_of (AR.array_resource output)) h0).AR.p)
    (fun h0 _ h1 ->
      R.sel (R.view_of (AR.array_resource input)) h1 ==
      R.sel (R.view_of (AR.array_resource input)) h0 /\
      (R.sel (R.view_of (AR.array_resource output)) h1).AR.p =
      (R.sel (R.view_of (AR.array_resource output)) h0).AR.p /\
      (R.sel (R.view_of (AR.array_resource output)) h1).AR.s ==
      Seq.init_ghost (A.vlength output) (fun i ->
        spec_f i (Seq.index (R.sel (R.view_of (AR.array_resource input)) h0).AR.s i)
      )
    )

let mapi #a #a' output input #spec_f f =
  (**) let hinit = HST.get () in
  (**) let correct_inv (h:HS.mem) (i:nat) : Type =
  (**)   admit();
  (**)   let i = if i >= A.vlength input then A.vlength input else i in
  (**)   (R.sel (R.view_of (AR.array_resource output)) h).AR.p =
  (**)   (R.sel (R.view_of (AR.array_resource output)) hinit).AR.p /\
  (**)   Seq.slice (R.sel (R.view_of (AR.array_resource output)) h).AR.s 0 i ==
  (**)   Seq.init_ghost i (fun j ->
  (**)     spec_f j (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j)
  (**)   )
  in
  let correct_f (i:U32.t{U32.v i < A.vlength input}) (x:a) : RST unit
    (R.(AR.array_resource output))
    (fun _ -> R.(AR.array_resource output))
    (fun h0 -> correct_inv h0 (U32.v i) /\ x == Seq.index (A.as_seq h0 input) (U32.v i))
    (fun h0 _ h1 -> correct_inv h0 (U32.v i) /\ correct_inv h1 (U32.v i + 1))
  =
   (**) let h0 = HST.get () in
    let new_x = RST.rst_frame
      (R.(AR.array_resource output))
      (fun _ -> R.(AR.array_resource output))
      (fun _ -> f i x)
    in
    RST.rst_frame
      (R.(AR.array_resource output))
      (fun _ -> R.(AR.array_resource output))
      (fun _ -> AR.upd output i new_x);
    (**) let h1 = HST.get () in
    (**) assert(correct_inv h0 (U32.v i));
    (**) if U32.v i >= A.vlength input then
    (**)   ()
    (**) else begin
    (**)   let vi = if U32.v i >= A.vlength input then A.vlength input else U32.v i in
    (**)   assert(vi = U32.v i);
    (**)   assert(Seq.slice (R.sel (R.view_of (AR.array_resource output)) h1).AR.s 0 vi ==
    (**)     Seq.init_ghost vi (fun j ->
    (**)       spec_f j (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j)
    (**)     )
    (**)   );
    (**)  let vi_plus_one = if U32.v i + 1 >= A.vlength input then A.vlength input else U32.v i + 1 in
    (**)  let aux (j:nat{j < vi_plus_one}) : Lemma (
    (**)    Seq.index (Seq.slice (R.sel (R.view_of (AR.array_resource output)) h1).AR.s 0 vi_plus_one) j ==
    (**)    Seq.index
    (**)      (Seq.init_ghost vi_plus_one
    (**)        (fun j' -> spec_f j' (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j')))
    (**)    j
    (**)  ) =
    (**)    assert(
    (**)      Seq.index (Seq.slice (R.sel (R.view_of (AR.array_resource output)) h1).AR.s 0 vi_plus_one) j ==
    (**)      Seq.index (R.sel (R.view_of (AR.array_resource output)) h1).AR.s j
    (**)    );
    (**)    assert(
    (**)      Seq.index
    (**)        (Seq.init_ghost vi_plus_one
    (**)          (fun j' -> spec_f j' (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j')))
    (**)      j  ==
    (**)      spec_f j (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j)
    (**)    );
    (**)    if j = U32.v i then begin
    (**)      assert(Seq.index (Seq.slice (R.sel (R.view_of (AR.array_resource output)) h1).AR.s 0 vi_plus_one) j ==
    (**)        Seq.index (R.sel (R.view_of (AR.array_resource output)) h1).AR.s j
    (**)      );
    (**)      assert(Seq.index
    (**)        (Seq.init_ghost vi_plus_one
    (**)          (fun j' -> spec_f j' (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j')))
    (**)          j ==
    (**)          spec_f j (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j)
    (**)      );
    (**)     assert(
    (**)       Seq.index (R.sel (R.view_of (AR.array_resource output)) h1).AR.s j ==
    (**)       new_x
    (**)     );
    (**)     admit();
    (**)     assert( Seq.index (R.sel (R.view_of (AR.array_resource input)) h0).AR.s j ==
    (**)        Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j);
    (**)     admit()
    (**)    end else begin
    (**)      assert(Seq.index (R.sel (R.view_of (AR.array_resource output)) h1).AR.s j ==
    (**)        Seq.index (R.sel (R.view_of (AR.array_resource output)) h0).AR.s j);
    (**)      assert(Seq.slice (R.sel (R.view_of (AR.array_resource output)) h0).AR.s 0 vi ==
    (**)        Seq.init_ghost vi (fun j' ->
    (**)          spec_f j' (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j')
    (**)      ));
    (**)      assert(Seq.index (Seq.slice (R.sel (R.view_of (AR.array_resource output)) h0).AR.s 0 vi) j ==
    (**)        Seq.index (R.sel (R.view_of (AR.array_resource output)) h0).AR.s j
    (**)      );
    (**)      assert(Seq.index (R.sel (R.view_of (AR.array_resource output)) h0).AR.s j ==
    (**)        spec_f j (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j)
    (**)      )
    (**)    end
    (**)  in
    (**)  Classical.forall_intro aux;
    (**)  assert(Seq.slice (R.sel (R.view_of (AR.array_resource output)) h1).AR.s 0 vi_plus_one `Seq.equal`
    (**)     Seq.init_ghost vi_plus_one (fun j ->
    (**)       spec_f j (Seq.index (R.sel (R.view_of (AR.array_resource input)) hinit).AR.s j)
    (**)     )
    (**)   )
    (**) end
  in
  admit();
  for_each #a input #correct_inv correct_f
