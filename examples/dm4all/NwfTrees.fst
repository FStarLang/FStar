module NwfTrees

open Stream

let f_sig (#s:Type) (p:(s -> Type)) : Type -> Type =
  fun a -> dtuple2 s (fun o -> p o -> a)

assume type nwf_trees (#s:Type) (p:(s -> Type))
assume val lbl : (#s:Type) -> (#p:(s -> Type)) -> nwf_trees p -> s
assume val branch : (#s:Type) -> (#p:(s -> Type)) -> (t:nwf_trees p) -> p (lbl t) -> nwf_trees p
assume val build_nwf_trees : (#s:Type) -> (#p:(s -> Type)) -> (#a:Type) -> (a -> f_sig p a) -> a -> nwf_trees p

assume LabelBuildNWFTrees : forall s p a h x. lbl (build_nwf_trees #s #p #a h x) == dfst (h x)
assume LabelBuildNWFTrees : forall s p a h x i. branch (build_nwf_trees #s #p #a h x) i == build_nwf_trees #s #p #a h (dsnd (h x) i)


let coerce (#a #b:Type) (x:a) : Pure b (requires (a == b)) (ensures (fun r -> r == x)) = x

let nwf_trees_bisim0 (#s:Type) (#p:(s -> Type)) (bisim : nwf_trees p * nwf_trees p -> prop)  ((t1,t2) : nwf_trees p * nwf_trees p) : prop =
  lbl t1 == lbl t2 /\ (forall (i : p (lbl t1)). bisim (branch t1 i, branch t2 (coerce i)))
let nwf_trees_bisim (#s:Type) (#p:(s -> Type)) = nu (nwf_trees_bisim0 #s #p)

assume NWFTreesEqualityIsBisimulation : forall s p (t1 t2 : nwf_trees #s p). t1 == t2 <==> nwf_trees_bisim (t1,t2)


assume type inp
assume type out

noeq
type s (a:Type) =
  | Inp : s a
  | Out : out -> s a
  | Ret : a -> s a

let p (a:Type) (o:s a) =
  match o with
  | Inp -> inp
  | Out _ -> unit
  | Ret _ -> False

let nwft (a:Type) = nwf_trees (p a)

let nwft_ret (#a:Type) (x:a) : nwft a =
  build_nwf_trees #(s a) #(p a) #unit (fun () -> (| Ret x, false_elim |)) ()

let extract_one_level (#a:Type) (t : nwft a) : f_sig (p a) (nwft a) =
   (| lbl t, branch t |)

let bind_aux (#a #b:Type) (f : a -> nwft b) (x:(either (nwft a) (nwft b))) : f_sig (p b) (either (nwft a) (nwft b)) =
  match x with
  | Inr tb -> (|lbl tb, (fun i -> Inr (branch tb i))|)
  | Inl ta ->
    match lbl ta with
    | Ret x -> let t = f x in (|lbl t, (fun i -> Inr (branch t i))|)
    | Out o -> (|Out o, (fun i -> Inl (branch ta i))|)
    | Inp -> (|Inp, (fun i -> Inl (branch ta i))|)

let nwft_bind0 (#a #b:Type) (f : a -> nwft b) (init : either (nwft a) (nwft b)) : nwft b =
  build_nwf_trees #(s b) #(p b) #(either (nwft a) (nwft b)) (bind_aux f) init

let nwft_bind (#a #b:Type) (m:nwft a) (f : a -> nwft b) : nwft b = nwft_bind0 f (Inl m)

let ret_bind_p (#a #b:Type) (f : a -> nwft b) ((t1,t2):nwft b*nwft b) = t2 == nwft_bind0 f (Inr t1)
let ret_bind_p_bisim0 (#a #b:Type) (f : a -> nwft b) (t12:nwft b*nwft b)
  : Lemma (requires ret_bind_p f t12) (ensures nwf_trees_bisim0 (coerce (ret_bind_p f)) t12) = ()

let bind_ret_p ((t1,t2):nwft a*nwft a) : prop = t2 == nwft_bind t1 nwft_ret
