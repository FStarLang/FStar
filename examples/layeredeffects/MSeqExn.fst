module MSeqExn

open FStar.HyperStack.ST
open FStar.Monotonic.Seq

module HS = FStar.HyperStack

type result (a:Type) =
  | Success : a -> result a
  | Error   : string -> result a


/// Type of pre- and postconditions for the new effect we are defining


/// Copying some definitions from your example

assume val entry_t : Type0

type trace_ = Seq.seq entry_t


assume val trace_inv0 : trace_ -> Type0

type trace = s:trace_{trace_inv0 s}

/// The pre- and postconditions are over traces that are both valid and trace_inv0

/// Precondition is a predicate on the input trace

type st_epre = trace -> Type0


/// Postcondition is a predicate on the result value and the output trace

type st_epost (a:Type) = result a -> trace -> Type0


/// WP is standard post -> pre ...
///
/// With an additional monotonicity refinement -- this should hopefully go away when we start treating monotonicity better

type st_ewp (a:Type) = wp:(st_epost a -> st_epre){
   forall p q. (forall r x. p r x ==> q r x) ==> (forall x. wp p x ==> wp q x)
}


/// Finally the global trace reference
///
/// Sincere apologies for the `norm` here, somehow Z3 barfs in the proof of bind below if this is not there


assume val trace_ref : (*norm [delta_only [`%i_seq] ]*) (i_seq HS.root entry_t trace_inv0)


/// Now the underlying representation of the new effect
///
/// Under the hoods, it's a STATE function that only modifies trace_ref

type st_erepr (a:Type) (wp:st_ewp a) =
  unit ->
  STATE (result a) (fun p h0 ->
    let s0 = i_sel h0 trace_ref in
    wp
      (fun r s1 ->
       forall h1. (i_sel h1 trace_ref == s1 /\
              equal_stack_domains h0 h1 /\
              HS.modifies_one HS.root h0 h1 /\  //and we modify nothing else in this effect
              HS.modifies_ref HS.root (Set.singleton (HS.as_addr trace_ref)) h0 h1) ==> p r h1)
      s0)


/// Effect combinators


/// return

let st_ereturn (a:Type) (x:a)
: st_erepr a (fun p s -> p (Success x) s)
= fun _ -> Success x


/// bind

let st_ebind (a:Type) (b:Type)
  (wp_f:st_ewp a) (wp_g:a -> st_ewp b)
  (f:st_erepr a wp_f) (g:(x:a -> st_erepr b (wp_g x)))
: st_erepr b
  (fun p s0 -> wp_f (fun r s1 ->
    match r with
    | Success x -> (wp_g x) p s1
    | Error s -> p (Error s) s1) s0)
= fun _ ->
  let r = f () in
  match r with
  | Success x -> (g x) ()
  | Error s -> Error s


/// sub computation

let st_esubcomp (a:Type)
  (wp_f:st_ewp a) (wp_g:st_ewp a)
  (f:st_erepr a wp_f)
: Pure (st_erepr a wp_g)
  (requires forall p n. wp_g p n ==> wp_f p n)
  (ensures fun _ -> True)
= f


/// if_then_else

let st_eif_then_else (a:Type)
  (wp_then:st_ewp a) (wp_else:st_ewp a)
  (f:st_erepr a wp_then) (g:st_erepr a wp_else)
  (p:Type0)
: Type
= st_erepr a (fun post n ->
    (p ==> wp_then post n) /\
    ((~ p) ==> wp_else post n))
  

/// And finally the effect definition

reifiable reflectable
layered_effect {
  STEXN : a:Type -> st_ewp a -> Effect
  with
  repr = st_erepr;
  return = st_ereturn;
  bind = st_ebind;
  subcomp = st_esubcomp;
  if_then_else = st_eif_then_else
}


/// DIV can be lifted to our effect


let lift_div_stexn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: st_erepr a (fun p n -> wp (fun x -> p (Success x) n))
= fun _ -> Success (f ())

sub_effect DIV ~> STEXN = lift_div_stexn


/// Hoare-style abbreviation

effect StExn (a:Type) (pre:trace -> Type0) (post:trace -> result a -> trace -> Type0) =
  STEXN a (fun p n0 -> pre n0 /\ (forall x n1. post n0 x n1 ==> p x n1))


/// To work with this new effect
///   while the DIV (and PURE) computations be lifted by the typechecker automatically,
///   STATE computations need to be lifted explicitly

let write_at_end_ (x:entry_t)
: st_erepr unit
  (fun p s0 ->
    let s1 = Seq.snoc s0 x in
    trace_inv0 s1 /\ p (Success ()) s1)
= fun _ ->
  Success (i_write_at_end trace_ref x)


/// Now reflect write_at_end_ into a StExn function that we will use now on to write to trace_refx

let write_at_end (x:entry_t)
: StExn unit
  (requires fun s -> trace_inv0 (Seq.snoc s x))
  (ensures fun s0 r s1 -> r == Success () /\ s1 == Seq.snoc s0 x)
= STEXN?.reflect (write_at_end_ x)


/// Similarly we can define a read function
///
/// By first defining a helper and then reflecting it

let read_ (i:nat)
: st_erepr entry_t
  (fun p s -> i < Seq.length s /\ p (Success (Seq.index s i)) s)
= fun _ ->
  let s = i_read trace_ref in
  Success (Seq.index s i)


let read (i:nat)
: StExn entry_t
  (requires fun s -> i < Seq.length s)
  (ensures fun s0 r s1 -> i < Seq.length s0 /\ r == Success (Seq.index s0 i) /\ s1 == s0)
= STEXN?.reflect (read_ i)


/// Some functions which we will use for testing

assume val some_pure_function (x:entry_t) : int

let get_ ()
: st_erepr trace (fun p s -> p (Success s) s)
= fun _ ->
  Success (i_read trace_ref)

let get ()
: StExn trace
  (requires fun _ -> True)
  (ensures fun s0 r s1 -> r == Success s0 /\ s1 == s0)
= STEXN?.reflect (get_ ())

let read_or_throw_ (i:nat)
: st_erepr entry_t
  (fun p s -> if i < Seq.length s then p (Success (Seq.index s i)) s else p (Error "") s)
= fun _ ->
  let s = i_read trace_ref in
  if i < Seq.length s then Success (Seq.index s i) else Error ""


let read_or_throw (i:nat)
: StExn entry_t
  (requires fun _ -> True)
  (ensures fun s0 r s1 ->
    s0 == s1 /\
    (match i < Seq.length s0 with
     | true -> r == Success (Seq.index s0 i)
     | false -> r == Error ""))
= STEXN?.reflect (read_or_throw_ i)


/// Now let's see this in action


/// We don't need state libraries or monotonic sequence anymore!


#set-options "--using_facts_from '* -FStar.HyperStack -FStar.Monotonic'"

let test (i j:nat)
: StExn unit
  (requires fun s -> i < Seq.length s)
  (ensures fun s0 r s1 ->
    match j < Seq.length s0 with
    | true -> r == Success () /\ Seq.length s1 == Seq.length s0 + 1
    | false -> r == Error "" /\ s0 == s1)
= let x = read i in
  let y = read_or_throw j in
  let b = some_pure_function y in
  let s = get () in
  if b > 0 then begin
    assume (trace_inv0 (Seq.snoc s y));
    write_at_end y
  end
  else begin
    assume (trace_inv0 (Seq.snoc s x));
    write_at_end x
  end

/// But we can still tell clients the stateful spec of test, for example:


/// Restart the solver to get state facts etc. in the context again

#restart-solver
#reset-options

let test_st (i j:nat)
: ST (result unit)
  (requires fun h -> i < Seq.length (i_sel h trace_ref))
  (ensures fun h0 r h1 -> 
    HS.modifies_one HS.root h0 h1 /\
    HS.modifies_ref HS.root (Set.singleton (HS.as_addr trace_ref)) h0 h1)  //can add functional specs too
= reify (test i j) ()
  







// assume val f_st (x:int)
// : st_erepr int
//   (fun p n ->
//    match x with
//    | 0 -> p (Error "") n
//    | _ -> p (Success x) n)


// assume val g_st (x:int)
// : st_erepr int
//   (fun p n ->
//    match x with
//    | 0 -> p (Error "f_st throws an exception") n
//    | _ -> p (Success x) n)


// let f (x:int)
// : StExn int
//   (requires fun _ -> True)
//   (ensures fun n0 r n1 -> n0 == n1 /\ ((x == 0 ==> Error? r) /\ (x =!= 0 ==> r == Success x)))
// = STEXN?.reflect (f_st x)


// let g (x:int)
// : StExn int
//   (requires fun _ -> True)
//   (ensures fun n0 r n1 -> n0 == n1 /\ ((x == 0 ==> Error? r) /\ (x =!= 0 ==> r == (Success x))))
// = STEXN?.reflect (g_st x)


// assume val some_pure_function (x:int) : int


// let test ()
// : StExn unit
//   (requires fun _ -> True)
//   (ensures fun n0 r n1 ->
//     let x = some_pure_function n0 in
//     match x with
//     | 0 -> Error? r /\ n1 == n0
//     | _ -> Success? r /\ n1 == 2)
// = let n = read () in

//   let n = some_pure_function n in

//   let n = f n in

//   let n = g n in

//   write 2

// let test_st ()
// : ST (result unit)
//   (requires fun _ -> True)
//   (ensures fun h0 r h1 ->
//     Heap.equal_dom h0 h1 /\
//     Heap.modifies (Set.singleton (Heap.addr_of global_ref)) h0 h1 /\
//     (let x = some_pure_function (sel h0 global_ref) in
//      match x with
//      | 0 -> Error? r /\ sel h0 global_ref == sel h1 global_ref
//      | _ -> Success? r /\ sel h1 global_ref == 2))
// = reify (test ())  ()



// let lift_exn_stexn (a:Type) (wp:ewp a) (f:erepr a wp)
// : st_erepr a (fun p n -> wp (fun x -> p x n))
// = fun _ -> f ()

// sub_effect EXN ~> STEXN = lift_exn_stexn



// type epre = Type0
// type epost (a:Type) = result a -> Type0
// type ewp (a:Type) = wp:(epost a -> epre){
//   forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)
// }


// type erepr (a:Type) (wp:ewp a) = unit -> PURE (result a) wp


// let ereturn (a:Type) (x:a)
// : erepr a (fun p -> p (Success x))
// = fun _ -> Success x

// let ebind (a:Type) (b:Type)
//   (wp_f:ewp a) (wp_g:a -> ewp b)
//   (f:erepr a wp_f) (g:(x:a -> erepr b (wp_g x)))
// : erepr b
//   (fun p -> wp_f (fun r ->
//     match r with
//     | Success x -> (wp_g x) p
//     | Error s -> p (Error s)))
// = fun _ ->
//   let r = f () in
//   match r with
//   | Success x -> (g x) ()
//   | Error s -> Error s

// let esubcomp (a:Type)
//   (wp_f:ewp a) (wp_g:ewp a)
//   (f:erepr a wp_f)
// : Pure (erepr a wp_g)
//   (requires forall p. wp_g p ==> wp_f p)
//   (ensures fun _ -> True)
// = f

// let eif_then_else (a:Type)
//   (wp_then:ewp a) (wp_else:ewp a)
//   (f:erepr a wp_then) (g:erepr a wp_else)
//   (p:Type0)
// : Type
// = erepr a (fun post ->
//     (p ==> wp_then post) /\
//     ((~ p) ==> wp_else post))
  

// reifiable reflectable
// layered_effect {
//   EXN : a:Type -> ewp a -> Effect
//   with
//   repr = erepr;
//   return = ereturn;
//   bind = ebind;
//   subcomp = esubcomp;
//   if_then_else = eif_then_else
// }


// let lift_pure_exn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> PURE a wp)
// : erepr a (fun p -> wp (fun x -> p (Success x)))
// = fun _ -> Success (f ())

// sub_effect PURE ~> EXN = lift_pure_exn

