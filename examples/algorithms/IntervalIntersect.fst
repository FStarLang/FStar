module IntervalIntersect

(*** Can F* replace Haskell and Coq? *)
/// Is F* ready for its first "F* vs 'pick your favorite language or proof
/// assistant'" flame war? Can it take on heavyweights such as Haskell and Coq?
///
/// Its list of supported features is full of fancy words such as polymorphism,
/// dependent types, user-defined monadic effects, refinement types, weakest
/// precondition calculus, predicative hierarchy of universes with universe
/// polymorphism, rich type-level computation, proofs by reification ..., but
/// does F* solve real world problems and do you need a PhD in type theory to
/// use it? Is F* ready for prime time?
///
/// Of course the answer to this question will always depend on who you are and
/// what you want to do? I will talk a bit more about what I am doing and how I
/// got to work on F* in the first place, but let it suffice to say that my PhD
/// is in cryptography, not type theory and involved models and proofs mostly
/// done on paper. Which means that my programming skills usually are a bit
/// [Rust|https://www.rust-lang.org]y, no pun intended.
///
/// As to the 'what'. About a week ago I came accross [Joachim Breitner's nice
/// blog
/// post|https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it]
/// on finding bugs in Haskell code by proving it. It is an excellent post.
/// Pitched at the right level for both the applied Haskell programmer and
/// someone like me curious about Haskell and Coq in theory---without a lot of
/// exposure to them in practice. What is nice about these two languages is that
/// general knowledge of mathematical notation and functional programming goes
/// some way with understanding the gist of the code. Moreover, the style to
/// program was written was a good fir for dusting off my F* skills. So
/// instead of parsing all of the Haskell and Coq code in detail, I decided to rewrite
/// it the example in F* to expore the example.
///
/// Most of the code is about lists of integers. Luckily there is already good
/// library support for both in F*. As explained by Joachim, verification loves
/// termination. We use a list library of pure and total operations that
/// can be used in specifications. In particular list operations are provably
/// terminating.

open FStar.List.Tot
open FStar.Math.Lib

/// As in its Haskell version, I represent intervals as a datatype constructor.
///  Note that [from] is inclusive and [to] is not inclusive. 
type interval = | I: from:int -> to:int -> interval
/// F* automatically generates accessor functions for the named arguments of the
/// dependently typed constructor. Given [i:interval], [I?.from i] returns the
/// start of the interval. Datatypes with a single constructor, also allow for
/// the usual '.' notation, e.g., [i.from], which makes them a convenient
/// alternative to records.
///
/// We define the goodness of [interval list]s in the same way as Joachim did in
/// Coq. A [good interval list] is orderd and consists of non-empty intervals.
/// 
let rec goodLIs (is:list interval) (lb:int) =
  match is with
  | [] -> true
  | I f t :: is -> lb <= f && f< t && goodLIs is t

let good is =
  match is with
  | [] -> true
  | I f t :: _ -> goodLIs is f

/// Coq is then used to prove that the [intersect] of two [good] [interval
/// list]s is itself a [good interval list]. Upon investigation, this invariant
/// should in fact hold at all times, so I make good use of F^*'s refinement
/// types, to add the requirement to the [intervals].
let intervals = is:list interval{good is}

/// This is a first example of how F* closely intertwines programming and
/// verification. Often Z3 can prove refinements automatically by discharging
/// them as SMT constraint queries.

/// The following function is needed in the termination argument for the
/// [intersect] function. I will get back to it in a bit.
let needs_reorder (is1 is2:intervals) : nat =
 match is1, is2 with
  | I f1 t1 :: _, I f2 t2 :: _ -> if t1 < t2 then 1 else 0
  | _, _ -> 0

/// Joachim is right, the code of [intersect] is the kind of functional code
/// that is pleasant to write: A small local recursive function, a few guards to
/// do case analysis, done. That is when you have the power of Haskell at your
/// hand. Unfortunately, [when] clauses are [not yet
/// supported|https://github.com/FStarLang/FStar/issues/64] by F* for
/// verification. But they will be one day, so for now I am using nested [if]
/// expressions. Oh horror.
///
/// Another difference from the Haskell code is that I lifted local functions to
/// the top level where they can be used in lemmas and instead declare them as
/// private. Also, as I learned the hard way, while in principle supported,
/// local functions are still somewhat
/// [buggy|https://github.com/FStarLang/FStar/issues/1361].

private let rec go (is1 is2:intervals)
  : Pure intervals
         (requires True)
         (ensures (fun ris ->
           ( is1=[] \/ is2=[] ==> ris=[])
         /\ ( Cons? is1 /\ Cons? is1 /\ Cons? ris  ==> 
             (hd ris).from >= max (hd is1).from (hd is2).from  )
         ))
         (decreases %[List.length is1 + List.length is2; needs_reorder is1 is2]) =
/// The termination argument uses the lexicographic ordering of two values: the
/// joint length of the lists and a bit indicating whether a reordering is
/// necessary. To prove that the function terminates, at every
/// recursive call either the first value decrease or the second value decreases
/// while the first stays equal.
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
  go is1 is2

/// We have now implemented [intersect], but at the same time we have also
/// defined and proven the [good] invariant on [intervals]. In the Coq proof
/// script this is achieved by the `intersect_good` lemma and about 70 lines of
/// proof scripts. Not only do we not have to write this lemma, but F*'s
/// automation really shines in this example. All it needs is the much simpler
/// post-condition that the result intervals are either empty, or start from a
/// value that is the maximum of the two input interval lists. It is easy enough
/// to convince oneself that this invariant holds, but why is it sufficient for
/// Z3 to complete the proof? As Arthur C. Clark famously said: Any sufficiently
/// advanced technology is indistinguishable from magic.

(**** Proving functional correctness *)

/// I could have stopped here and declare victory.

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

(***** Why functional programming and types *)

/// Today there are many areas in which bugs in programs have become so
/// expensive, that programmers are willing to walk an extra mile to avoid bug
/// infested code.
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
