/// #ocaml-and-coq VS hs-to-coq: An F* version of the hs-to-coq example by
/// Joachim Breitner
/// (https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it)
///
/// About a week ago I read Joachim's blog on verifying Haskell code. Today
/// there are many areas in which bugs in programs have become so expensive,
/// that programmers are willing to walk an extra mile to avoid bug infested
/// code.
///
/// Two popular approaches for this are the use of modern programming languages
/// and program verification.
///
/// There are some similarities and synergies between the two. Modern languages,
/// such as strictly typed functional programming languages, make (mathematical)
/// reasoning about program code easier and thus potentially make program
/// verification easier. There are also differences, the expressivity of a
/// programming language helps programmers understand their programs, but
/// supporting all that in a verification tool may hinder automation and may
/// result in a large trusted computing base. The established wisdom here is to
/// have a core calculus that is as small as possible, and to translate the more
/// complex human readable code to that calculus.
///

module IntervalIntersect
open FStar.List.Tot
open FStar.Math.Lib

/// [from] is inclusive, [to] is not inclusive
/// I made the type of [interval] stronger to require that intervals are non-empty
type interval = | I: from:int -> to:int{from<to} -> interval

/// This allows to simplify the [goodLOs] predicate
let rec goodLIs (is:list interval) (lb:int) =
  match is with
  | [] -> true
  | I f t :: is -> lb <= f
                 && goodLIs is t

let good is =
  match is with
  | [] -> true
  | I f t :: _ -> goodLIs is f

/// Functions require and ensure that all input and output intervalse are good,
/// respectively. It is thus convenient to strengthen the [intervals] type.
let intervals = is:list interval{good is}

let needs_reorder (is1 is2:intervals) : nat =
  match is1, is2 with
  | I f1 t1 :: _, I f2 t2 :: _ -> if t1 < t2 then 1 else 0
  | _, _ -> 0

/// The termination argument uses lexicographical ordering of two calues: either
/// joint length of the lists decreases, or the bid inticating whether a
/// reordering is necessary decreases from 1 to 0.
private let rec go (is1 is2:intervals)
  : Pure intervals
         (requires True)
         (ensures (fun ris ->
            ( Cons? ris /\ Cons? is1 /\ Cons? is2 ==>
             (hd ris).from >= max (hd is1).from (hd is2).from  )
         /\ ( Nil? is1 \/ Nil? is2 ==> Nil? ris )))
         (decreases %[List.length is1 + List.length is2; needs_reorder is1 is2]) =
  match is1, is2 with
  | _, [] -> []
  | [], _ -> []
  | i1::is1, i2::is2 ->
    begin
      let f' = max (i1.from) (i2.from) in
      // reorder for symmetry
      if i1.to < i2.to then go (i2::is2) (i1::is1)
      // // disjoint
      else if i1.from >= i2.to then go (i1::is1) is2
      // subset
      else if i1.to = i2.to then I f' (I?.to i1) :: go is1 is2
      // overlapping
      else  I f' (i2.to) ::
        go (I (i2.to) (i1.to) :: is1) is2
    end

let intersect (is1 is2:intervals) = 
  // let rec f (i:nat) : Pure nat (requires True) (ensures (fun r -> r=0)) = if i=0 then 0 else f (i-1) in 
  go is1 is2


let rangeGT (f t:int): GTot (Set.set int)
  =
  Set.intension (fun z -> f <= z && z < t)

let rec range (f:int) (t:int): Tot (r:Set.set int{r==rangeGT f t})
  (decreases %[t-f])
  =
  if f>=t then ( 
    Set.lemma_equal_elim (rangeGT f t) Set.empty; 
    Set.empty 
  ) else (
    Set.lemma_equal_elim (rangeGT f t) (Set.union (Set.singleton f) (rangeGT (f+1) t )); 
    Set.union (Set.singleton f) ( range (f+1) t ) 
  )

let semI (i : interval) : Set.set int =
  range i.from i.to

let rec sem (is : intervals) : Set.set int =
  match is with
  | [] -> Set.empty #int
  | (i :: is) -> Set.union (semI i) (sem is)

let lemma_disjoint_intro (#a:eqtype) (s1 s2:Set.set a)
  : Lemma
    (requires Set.equal (Set.intersect s1 s2) Set.empty)
    (ensures Set.disjoint s1 s2)
    [SMTPat (Set.disjoint s1 s2)]
 = ()

let rec lemma_intersection_range_semLIs_empty (f t:int) (is:intervals) (lb:int)
  : Lemma 
    (requires goodLIs is lb /\ t <= lb)
    (ensures Set.intersect (range f t) (sem is) == Set.empty)
  =
  if (Cons? is) then
      lemma_intersection_range_semLIs_empty f t (tl is) (hd is).to
  else ();
  Set.lemma_equal_elim (Set.intersect (range f t) (sem is)) Set.empty

let lemma_intervals_disjoint (is:intervals{Cons? is})
  : Lemma
    (ensures (Set.disjoint (semI (hd is)) (sem (tl is))))
  =
  if (Cons? (tl is)) then (
    let h::t = is in
    lemma_intersection_range_semLIs_empty h.from h.to t h.to
  ) else ()


let lemma_disjoint_prefix (is1:intervals{Cons? is1})  (is2:intervals{Cons? is2})
  : Lemma 
    (requires (hd is1).from >= (hd is2).to )
    (ensures (Set.intersect (sem is1) (sem is2) == Set.intersect (sem (is1)) (sem (tl is2))))
  =
  let h2 = (hd is2) in
  lemma_intervals_disjoint (h2::is1);
  Set.lemma_equal_elim (Set.intersect (sem is1) (sem is2)) (Set.intersect (sem (is1)) (sem (tl is2)))


#set-options "--z3rlimit 15"
let rec lemma_overlapping_prefix (is1:intervals{Cons? is1}) (is2:intervals{Cons? is2})
  : Lemma
    (requires (hd is1).to > (hd is2).to /\ (hd is1).from < (hd is2).to)
    (ensures (
        let h1::t1 = is1 in let h2::t2 = is2 in
        let f' = max h1.from h2.from in
        Set.intersect (sem is1) (sem is2) ==
        Set.union (semI (I f' h2.to))
                  (Set.intersect (Set.union (range (h2.to) (h1.to)) (sem t1))
                                 (sem t2)) ))
  =
  let h1::t1 = is1 in
  let h2::t2 = is2 in
  let f' = max h1.from h2.from in
/// (h1 u t1) n (h2 u t2) = (h1 n (h2 u t2)) u (t1 n (h2 u t2))
///                         = (h1 n h2) u (h1 n t2) u (t1 n h2) u (t1 n t2)
  let is1_n_is2 = Set.intersect (sem is1) (sem is2) in
  assert (Set.equal is1_n_is2
                    (Set.union (Set.union (Set.intersect (semI h1) (semI h2))
                                          (Set.intersect (semI h1) (sem t2)))
                               (Set.union (Set.intersect (semI h2) (sem t1))
                                          (Set.intersect (sem t1) (sem t2)))));
///  h1 n h2 = [f', h2.to]
  assert (Set.equal (Set.intersect (semI h1) (semI h2)) (semI (I f' h2.to)));
///  h1 n t2 = [h2.to h1.to] n t2
  lemma_intersection_range_semLIs_empty h1.from h2.to t2 h2.to;
  Set.lemma_equal_elim (range h1.from h1.to)
                       (Set.union (range h1.from h2.to) (range h2.to h1.to));
  Set.lemma_equal_elim (Set.intersect (range h1.from h1.to) (sem t2))
                       (Set.intersect (range h2.to h1.to) (sem t2));
///  h2 n t1 = empty
  lemma_intervals_disjoint (h2::t1);
  Set.lemma_equal_elim is1_n_is2
                       (Set.union (semI (I f' h2.to))
                                  (Set.intersect (Set.union (range (h2.to) (h1.to))
                                                            (sem t1))
                                                 (sem t2)) )

#reset-options
let rec lemma_intersection_spec (is1:intervals) (is2:intervals)
  : Lemma
    (ensures (Set.equal ( sem (intersect is1 is2) ) (Set.intersect (sem is1) (sem is2))))
    (decreases %[List.length is1 + List.length is2; needs_reorder is1 is2])
  =
  match is1, is2 with
  | [], [] -> ()
  | _, [] -> ()
  | [], _ -> ()
  | i1::is1, i2::is2 ->
    begin
       let f' = max (i1.from) (i2.from) in
       // reorder for symmetry
       if i1.to < i2.to then lemma_intersection_spec (i2::is2) (i1::is1)
       // disjoint i2.from i2.to, i1.from, i1.to
       else if i1.from >= i2.to then (
         lemma_intersection_spec (i1::is1) is2;
         assert (Set.disjoint (semI i1) (semI i2));
         lemma_disjoint_prefix (i1::is1) (i2::is2)
       )
       // subset min (i1.from) (i2.from), f', i1.to=i1.to,
       else if i1.to = i2.to then (
         assert (Set.equal (Set.intersect (semI i1) (semI i2)) (semI (I f' i1.to)));
         lemma_intervals_disjoint (i2::is1);
         lemma_intervals_disjoint (i1::is2);
         lemma_intersection_spec is1 is2
       )
       // overlapping
       else  (
         lemma_overlapping_prefix (i1::is1) (i2::is2);
         lemma_intersection_spec (I (i2.to) (i1.to) :: is1) is2
       )
    end

/// A simple print and test function confirme the code can be executed.
open FStar.All
open FStar.IO
open FStar.Printf

let rec print_intervals is: ML unit =
  match is with
  | [] -> stdout <| "."
  | i::is ->
    stdout <| sprintf "[%d, %d] " i.from i.to;
    print_intervals is

let main = print_intervals (intersect [I 3 10; I 11 15] [I 1 4; I 10 14])
