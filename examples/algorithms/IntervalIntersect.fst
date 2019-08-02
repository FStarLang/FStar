/// ==================================
///  Can F\* replace Haskell and Coq?
/// ==================================
///
/// Is F\* ready for its first F\* vs 'pick your favourite language or proof
/// assistant' flame war? Can it take on heavyweights such as Haskell and Coq?
///
/// Its list of supported features is full of imaginative PL jargon such as
/// polymorphism, dependent types, user-defined monadic effects, refinement
/// types, weakest precondition calculus, predicative hierarchy of universes
/// with universe polymorphism, rich type-level computation, proofs by
/// reification and so forth, but does F\* solve real world problems (TM) or does
/// one need a PhD in type theory to use it?
///
///   Is F\* ready for prime time?
///
/// Of course the answer to this question will always depend on *who* you are
/// and what you want to do? I could write another post about *what* I am doing
/// and *how* I got to work on F\* in the first place, but let it suffice to say
/// that my PhD is in cryptography, not type theory and involved mathematical
/// models and proofs mostly done on paper. See `project everest`_
/// on how to encode such models in F\*. This means that my programming skills
/// usually are a bit `Rust`_\y, no pun intended.
///
/// As to the *what*. About a week ago I came across `Joachim Breitner's inspiring
/// post`_ on *finding bugs in Haskell code by proving it*. Pitched at the right
/// level, it is an excellent post for both the applied Haskell programmer and
/// someone like me curious about Haskell and Coq in theory---without a lot of
/// exposure to them in practice. What is nice about these two languages (and F\*
/// too) is that general knowledge of mathematical notation and functional
/// programming goes some way towards understanding the gist of the code. Its
/// concise and engaging programming style motivated me to dust off my F\* skills.
/// So instead of parsing all of the Haskell and Coq code and installing all the
/// tools to play with it, I decided to explore the example by re-verifying it in
/// F\*.
///
/// .. _`project everest`: https://project-everest.github.io
/// .. _`Rust`: https://www.rust-lang.org
/// .. _`Joachim Breitner's inspiring post`: https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it
///
/// ----
///
/// This ended up being a lengthy post. Here is the synopsis to enable cherry picking.
///
/// The two threads of the post are sandwitched between general F\* background
/// on datatypes and input/output. The first threat treats the actual interval
/// intersection code and the invariant Joachim proves about it. The second
/// thread proves functional correctness using a set semantic for intervals.
///
///  * `The importance of libraries`_
///  * `Part 1: Proving the intervals invariant`_
///  * `Part 2: Proving functional correctness`_
///
///    - `The mathematical representation of intervals`_
///    - `The heart of the proof`_
///    - `Taking stock: intrinsic vs. extrinsic, intensional vs extensional`_
///
///  * `Extraction and testing`_
///  * `And the winner is!`_
///
///    - `Developer efficiency & code to proof ratio`_
///    - `Useability, maturity, and trusted computing base`_
///
/// ----

module IntervalIntersect

/// Activates the new `two phase commit`_ feature.
/// .. _`two phase commit` https://github.com/FStarLang/FStar/issues?utf8=%E2%9C%93&q=label%3Acomponent%2Ftwo-phase-tc+
///
/// The importance of libraries
/// ===========================
///
/// Most of the code is about lists of integers. Luckily, F* has a decent list
/// library. Instead of mathematical integers, I use OCaml's native Int63 for
/// the best performance. As explained by Joachim, verification loves
/// termination. Se we use a list library of pure and total operations for both
/// implementation and specifications. In particular list operations are
/// provably terminating.

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Int64 // change to re-verify with different machine integer

type offset = t

/// As in its Haskell version, I represent intervals as a datatype constructor.
/// Note that `from` is inclusive and `to` is exclusive.

type interval = | I: from:offset -> to:offset -> interval

/// F\* automatically generates accessor functions for the named arguments of the
/// dependently typed constructor. Given `i:interval`, `I?.from i` returns the
/// start of the interval. Datatypes with a single constructor, also allow for
/// the usual '.' notation, e.g., `i.from`, which makes them a convenient
/// alternative to records.
///
/// Part 1: Proving the intervals invariant
/// =======================================
///
/// We define the goodness of `interval list`\s in the same way as Joachim did in
/// Coq. A `good interval list` is ordered and consists of non-empty disjoint
/// intervals.

let rec goodLIs (is:list interval) (lb:offset) =
  match is with
  | [] -> true
  | I f t :: is -> lb <=^ f && f <^ t && goodLIs is t

/// Contrary to Joachim's informal claims, already in his Coq development
/// intervals are however not necessarily non-adjacent. This is a good example
/// for a divergence between formal spec and human intuitive expectations. Just
/// because we verified something, doesn't necessarily mean that we get what we
/// want. Something has to give, either we remove the informal non-adjacency
/// requirement, or strengthen the `goodLIs` predicate to require `lb < f`.

let good is =
  match is with
  | [] -> true
  | I f t :: _ -> goodLIs is f

/// Coq is then used to prove that the `intersect` of two `good` `interval
/// list`\s is itself a `good interval list`. Upon investigation, this invariant
/// should in fact hold at all times, so I make good use of F*'s refinement
/// types, to add the requirement to the `intervals`.

let intervals = is:list interval{good is}

/// This is a first example for F\*'s closely intertwined programming and
/// verification style. Often the Z3_ SMT solver can prove refinements automatically by
/// discharging them as SMT-LIB queries.

/// The following function is needed in the termination argument for the
/// `intersect` function. I will get back to it in a bit.

let needs_reorder (is1 is2:intervals) : nat =
 match is1, is2 with
  | I f1 t1 :: _, I f2 t2 :: _ -> if t1 <^ t2 then 1 else 0
  | _, _ -> 0

/// Joachim is right, the code of `intersect` is the kind of functional code
/// that is pleasant to write: A small local recursive function, a few guards to
/// do case analysis, done. That is when you have the power of Haskell at your
/// hand. Unfortunately, `when` clauses are not yet
/// supported (issue64_) by F\* for
/// verification. But they will be one day, so for now I am using nested `if`
/// expressions. Oh horror.
///
/// Another difference from the Haskell code is that I lifted local functions to
/// the top level where they can be used in lemmas and instead declare them as
/// private. Also, as I learned the hard way, while in principle supported,
/// local functions are still somewhat buggy (issue1361_).
///
/// .. _Z3: https://github.com/Z3Prover/z3/wiki
/// .. _issue64: https://github.com/FStarLang/FStar/issues/64
/// .. _issue1361: https://github.com/FStarLang/FStar/issues/1361

let max a b = int_to_t (max (v a) (v b))

//#set-options "--z3rlimit 40 --max_ifuel 7"

private let rec go (is1 is2:intervals)
  : Pure intervals
         (requires True)
         (ensures (fun ris ->
          ( is1=[] \/ is2=[] ==> ris=[])
        /\ ( Cons? is1 /\ Cons? is1 /\ Cons? ris  ==>
            (hd ris).from >=^ max (hd is1).from (hd is2).from  )
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
      let f' = max i1.from i2.from in
      // reorder for symmetry
      if i1.to <^ i2.to then  go (i2::is2) (i1::is1)
      // disjoint
      else if i1.from >=^ i2.to then go (i1::is1) is2
      // subset
      else if i1.to = i2.to then I f' i1.to :: go is1 is2
      // overlapping
      else I f' (i2.to) ::
        go (I (i2.to) (i1.to) :: is1) is2
    end

let intersect (is1 is2:intervals) =
  go is1 is2

/// We have now implemented `intersect`, but at the same time we have also
/// defined and proven the `good` invariant on `intervals`. In the Coq proof
/// script this is achieved by the `intersect_good` lemma and about 70 lines of
/// proof scripts. Not only do we not have to write this lemma, but F\*'s
/// automation really shines in this example. All it needs is the much simpler
/// post-condition that the result intervals are either empty, or start from a
/// value that is the maximum of the two input interval lists. It is easy enough
/// to convince oneself that this invariant holds, but why is it sufficient for
/// Z3 to complete the proof? As Arthur C. Clark famously said: Any sufficiently
/// advanced technology is indistinguishable from magic.
///
/// I am cryptographer and we like to give paper proofs of results that seem
/// almost magical. Naturally, the proof is by induction. So after a recursive
/// call to `go`, the induction hypothesis is available, and we know that the
/// returned `intervals` are good. The SMT solver can also prove locally that
/// the interval prepended to this result is non-empty, what remains to be shown
/// is that together they are ordered. That is where knowing that the `from` of
/// the first result intervals is the `max` saves the day.
///
/// Part 2: Proving functional correctness
/// ======================================
///
/// I could stop and declare victory here, 1:0 for FStar. Arguable there are a
/// few blemishes, like the F\* bug with local functions that I discovered, or
/// the low priority given to a weakes precondition calculus supporting `when`
/// clauses, but overall I was positively surprised by the speed at which I
/// could translate the Haskell and Coq code to F\* and by how little I had to
/// do in terms of writing proofs.
///
/// Mindful of Clarke's second law that the only way of discovering the limits
/// of the possible is to venture a little way past them into the impossible, I
/// wont stop when its easy. The second property Joachim proved about his
/// `intersect` function was that it corresponds to its corresponding function.
/// This sounds a bit tautological. What is meant here is that it corresponds to
/// another way of representing intervals and another way of implementing
/// intersection in that representation. Ideally this alternative way is *in
/// some sense* more pure and mathematical.
///
/// The mathematical representation of intervals
/// ============================================
///
/// In mathematics, intervals are of course traditionally represented as sets, and
/// interval intersection simply becomes set intersection. Luckily, the
/// `FStar.Set` module already provides us with set operations proven to be pure
/// and total.
///
/// However, unlike `Coq.Sets.Ensembles` the representation of `set a` as a function
/// `a -> bool` is abstract in F\*. Consequently, we cannot define `range` using a
/// lambda expression. This is what is lost, what do we then gain by hiding the
/// representation of sets behind an abstraction? We can change the way sets are
/// represented in `FStar.Set` under the hood, without affecting users of the
/// library. Indeed F\* libraries often have two implementations, one acting as a
/// model to prove that the pre- and post-conditions of the API do not allow to
/// prove `False`, and an actual implementation for running the actual program. In
/// fact different extraction targets, such as OCaml and F# would typically provide
/// different implementations, e.g. the OCaml implementation of many libraries
/// modules is based on Batteries_. [#]_
///
/// .. _Batteries: http://batteries.forge.ocamlcore.org/
///
/// .. [#] For verification to be meaningful, it is important that these
///    alternative implementations are correct. In fact, while developing this post
///    I observed that the `BatSet`-based OCaml implementation of `FStar.Set` assumed
///    that set elements were compareable, which can be a source of unsoundness.
///    Another F\* bug that I could fix.
///
/// The declarative definition of a set using a predicate that all set members
/// need to satisfy is known in mathematics as an intensional definition.
/// Certain sets, for example the set of even numbers can only be defined
/// intensionally. My intuition is that intensional definitions are more concise
/// and better suited for proof, conversely, extensional definitions
/// explicitly guarantee that sets are finite.
///
/// To get the best of both worlds, I give both an intensional and an
/// extensional description of integer ranges, but make the intensional
/// definition ghost. This means that it never has to be extracted to OCaml code.

let rangeGT (f t:offset): GTot (Set.set offset) = Set.intension (fun z -> f <=^ z &&
  z <^ t)

let mem_rangeGT (f t:offset) (x:offset)
: Lemma
  (Set.mem x (rangeGT f t) == (f <=^ x && x <^ t))
  [SMTPat (Set.mem x (rangeGT f t))]
= Set.mem_intension x (fun z -> f <=^ z && z <^ t)

/// Because of the immaturity of F\* and the need for abstraction to
/// simultaneously support verification and extraction, I had to fix and extend
/// the `FStar.Set` library itself, rather than just add additional lemmas in a
/// separate file as in the Coq development. I use the ghostly intensional
/// definition to specify the logical properties of the extensional definition.

let rec range (f:offset) (t:offset): Tot (r:Set.set offset{r==rangeGT f t})
  (decreases %[v t- v f])
  =
  if f>=^t then (
    Set.lemma_equal_elim (rangeGT f t) Set.empty;
    Set.empty
  ) else (
    Set.lemma_equal_elim (rangeGT f t) (Set.union (Set.singleton f) (rangeGT (f+^ int_to_t 1) t ));
    Set.union (Set.singleton f) ( range (f+^ int_to_t 1) t )
  )

/// The proof that the extensionally defined set is the same as the
/// intensionally defined set uses induction, and the set equality `[f,t] = {f}
/// u [f+1,t]`.
///
/// Using `range` and following the Coq code, the `semI` and `sem` functions
/// define the semantic of bounds based interval representations in terms of
/// integer sets.

let semI (i : interval) : Set.set offset =
  range i.from i.to

let rec sem (is : intervals) : Set.set offset =
  match is with
  | [] -> Set.empty
  | (i :: is) -> Set.union (semI i) (sem is)

/// This simple lemma should move to `FStar.Set`, but this allows me to
/// explain some of F\*'s automation power. The body of the lemma is straightforward
/// and the proof is by definition. But the SMT pattern 'reminds' the SMT solver to
/// prove disjointness whenever the intersection of two sets is empty. Below I
/// commented out two invocations of the lemma that are triggered by the pattern.

let lemma_disjoint_intro (#a:eqtype) (s1 s2:Set.set a)
  : Lemma
    (requires Set.equal (Set.intersect s1 s2) Set.empty)
    (ensures Set.disjoint s1 s2)
    [SMTPat (Set.disjoint s1 s2)]
  = ()


/// I use the lemma to prove that an interval is disjoint from an interval list
/// whenever their concatenation is `good`. The local lemma is inspired
/// by Joachim's `Intersection_range_semLIs_empty` lemma. It expresses the same
/// idea and follows by induction on an increasing lower bound.

let lemma_semI_sem_disjoint (i:interval) (is:intervals)
  : Lemma
    (requires good (i::is))
    (ensures (Set.disjoint (semI i) (sem is)))
  =
  let rec lemma_semI_sem_lb_disjoint (i:interval) (is:intervals) (lb:offset)
    : Lemma
      (requires goodLIs is lb /\ i.to <=^ lb)
      (ensures Set.disjoint (semI i) (sem is))
    =
    if (Cons? is) then
       lemma_semI_sem_lb_disjoint i (tl is) (hd is).to
    else ();
    Set.lemma_equal_elim (Set.intersect (semI i) (sem is)) Set.empty in
  lemma_semI_sem_lb_disjoint i is i.to
  // ; lemma_disjoint_intro (semI h) (sem t) //needed if SMTPat is removed


/// The heart of the proof
/// ----------------------
///
/// We now get into the heart of the correctness proof for `intersect`. Recall
/// that Joachim's algorithm (after switching) distinguishes three cases about
/// the head elements of two interval lists:
///
///  1. the heads are disjoint
///  2. the second head is a subset of the first
///  3. the two heads are overlapping
///
/// We prove a lemma for each case.
///
/// The first lemma states that if the heads are disjoint, then the head with
/// the smaller `to` can be dropped from the `intersect` computation.

let lemma_disjoint_prefix (is1:intervals{Cons? is1})  (is2:intervals{Cons? is2})
  : Lemma
    (requires (hd is1).from >=^ (hd is2).to )
    (ensures (Set.intersect (sem is1) (sem is2) == Set.intersect (sem (is1)) (sem (tl is2))))
  =
  let h2 = hd is2 in
  lemma_semI_sem_disjoint h2 is1;
  Set.lemma_equal_elim (Set.intersect (sem is1) (sem is2)) (Set.intersect (sem (is1)) (sem (tl is2)))

/// The second lemma states that if the second head is a subset of the first,
/// then the result of `intersect` is the union of that subset and the
/// `intersect` computation with both heads dropped.

let lemma_subset_prefix (is1:intervals{Cons? is1}) (is2:intervals{Cons? is2})
  : Lemma
    (requires (hd is1).to = (hd is2).to /\ (hd is1).from <^ (hd is2).to)
    (ensures (
      let h1::t1, h2::t2 = is1,is2 in
      let f' = max h1.from h2.from in
      Set.intersect (sem is1) (sem is2) ==
      Set.union (semI (I f' h2.to))
                (Set.intersect ( sem t1)
                               ( sem t2)) ))
  =
  let h1::t1,h2::t2 = is1, is2 in
  let f' = max h1.from h2.from in
  lemma_semI_sem_disjoint h2 t1;
  lemma_semI_sem_disjoint h1 t2;
  Set.lemma_equal_elim (Set.intersect (sem is1) (sem is2))
                       (Set.union (semI (I f' h2.to))
                                  (Set.intersect ( sem t1)
                                                 ( sem t2)) )

/// This is the hardest of the three cases and we ramp up the SMT solvers
/// timeout to prove it.

#set-options "--z3rlimit 15"

/// No, unfortunately this is not a panacea and should only be used when
/// verification is unstable. In other situations, it is a proven recipe for
/// spending too much time idlying just to get the infamous "could not prove
/// post-condition" error. Time that one should instead spend on thinking about the
/// nature of the proof.
///
/// To shortcut the thinking a bit, I looked at the Coq proof script. While most
/// of it was pretty obfuscated without a detailed knowledge of Coq tactics
/// and the ability to see the proof state, it revealed some crucial hints.
///
/// One was the equivalent of the `lemma_semI_sem_lb_disjoint` lemma and its
/// proof. The other was the importance of set operation distributivity for the
/// proof.

let rec lemma_overlapping_prefix (is1:intervals{Cons? is1}) (is2:intervals{Cons? is2})
  : Lemma
    (requires (hd is1).to >^ (hd is2).to /\ (hd is1).from <^ (hd is2).to)
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

/// The `assert` below expresses the outcome of the repeated application of set
/// distributive law to state the following equality:
///
/// (h1 u t1) n (h2 u t2) = (h1 n (h2 u t2)) u (t1 n (h2 u t2))
///                       = (h1 n h2) u (h1 n t2) u (t1 n h2) u (t1 n t2)
///
/// ----

  let is1_n_is2 = Set.intersect (sem is1) (sem is2) in
  assert (Set.equal is1_n_is2
                    (Set.union (Set.union (Set.intersect (semI h1) (semI h2))
                                          (Set.intersect (semI h1) (sem t2)))
                               (Set.union (Set.intersect (semI h2) (sem t1))
                                          (Set.intersect (sem t1) (sem t2)))));
///  The rest of the proof simplifies the first three of the four intersects:
///  1. h1 n h2 = [f', h2.to]

  assert (Set.equal (Set.intersect (semI h1) (semI h2)) (semI (I f' h2.to)));
///  2. h1 n t2 = [h2.to h1.to] n t2

  lemma_semI_sem_disjoint (I h1.from h2.to) t2;
  assert (Set.equal (range h1.from h1.to)
                    (Set.union (range h1.from h2.to) (range h2.to h1.to)));
  assert (Set.equal (Set.intersect (range h1.from h1.to) (sem t2))
                    (Set.intersect (range h2.to h1.to) (sem t2)));
///  3. h2 n t1 = empty

  lemma_semI_sem_disjoint h2 t1;

/// The proof now applies the distributive law in the other direction to combine
/// the 3rd and 4th intersect:

  Set.lemma_equal_elim is1_n_is2
                       (Set.union (semI (I f' h2.to))
                                  (Set.intersect (Set.union (range (h2.to) (h1.to))
                                                            (sem t1))
                                                 (sem t2)) )

/// The final proof is by case analysis, in each step relying on the induction
/// hypothesis and one of the lemmas. Again the `assert`\s document document the
/// proof.

let rec lemma_intersection_spec (is1:intervals) (is2:intervals)
  : Lemma
    (ensures (Set.equal ( sem (intersect is1 is2) ) (Set.intersect (sem is1) (sem is2))))
    (decreases %[List.length is1 + List.length is2; needs_reorder is1 is2])
  =
  match is1, is2 with
  | _, [] -> ()
  | [], _ -> ()
  | i1::is1, i2::is2 ->
    begin
       let f' = max (i1.from) (i2.from) in
       // reorder for symmetry
       if i1.to <^ i2.to then lemma_intersection_spec (i2::is2) (i1::is1)
       // disjoint: i2.from < i2.to <= i1.from < i1.to
       else if i1.from >=^ i2.to then (
         // lemma_disjoint_intro (semI i1) (semI i2); //needed if SMTPat is removed
         assert (Set.disjoint (semI i1) (semI i2));
         lemma_intersection_spec (i1::is1) is2;
         lemma_disjoint_prefix (i1::is1) (i2::is2)
       )
       // subset: min (i1.from) (i2.from) <= f' <= i1.to=i2.to,
       else if i1.to = i2.to then (
         assert (Set.equal (Set.intersect (semI i1) (semI i2)) (semI (I f' i1.to)));
         lemma_intersection_spec is1 is2;
         lemma_subset_prefix (i1::is1) (i2::is2)
       )
       // overlapping: min (i1.from) (i2.from) <= f' <= i2.to < i1.to
       else  (
         lemma_intersection_spec (I (i2.to) (i1.to) :: is1) is2;
         lemma_overlapping_prefix (i1::is1) (i2::is2)
       )
    end

/// The following pragma resets the SMT solver to its original resource limit (roughly 5 seconds):

  #reset-options

/// Taking stock: intrinsic vs. extrinsic, intensional vs extensional
/// -----------------------------------------------------------------
///
/// Clearly the second part of verifying `intersect` was much harder. While in the
/// first we used F\* essentially as a programming language with stronger types and
/// great automation, in the second we relied on hand-written lemmas and
/// proofs.
///
/// The two parts are also examples of what in F\* jargon are called intrinsic and
/// extrinsic verification styles. In the intrinsic verification style, the property
/// is expressed in the function definition itself, e.g., by refining operand and
/// return types, while in the extrinsic verification style, the property is
/// expressed as a lemma and proved separately.
///
/// The code/definition to proof ratio is larger in part 2, but is still
/// substantially smaller than in the Coq development. In addition to the proof
/// scripts, Joachim's development relied on about 160 lines of lemma code about Coq
/// ensembles, compared to the additional 10 additional lines in `FStar.Set` to
/// support intensional set definitions, and the `lemma_disjoint_intro` lemma.
/// Arguably this is not what Jachim optimised for. True to the title of the blog
/// his priority was to prove the code and find bugs, rather than find the most
/// elegant proof.
///
/// I in turn dedicated some time to cleaning up the code and to makeing it
/// robust to the unpredictability of the SMT solver. I claim that well written
/// F\* code is easier to maintain and adapt than Coq proof scripts. The
/// `hs-to-coq` authors understood the importance of proofs evolving with
/// programs, not the lease because programs often change. The concise and
/// closely integrated F\* proof makes maintaining programs easier, not the
/// least because no translation is needed. Moreover, it acts as verified
/// documentation that, like good wine, keeps its value as code is handed down
/// through generations of programmers.
///
/// To validate my claim, I changed the representation of intervals from
/// mathematical integers to machine integers and this was indeed painfree.
///
/// Extraction and testing
/// ======================
///
/// *Testing* too is crucial to program longevity and it is not something F\*
/// has traditionally been good at. Like Haskell and Coq, F\* has a bit of an
/// *if it typechecks it runs*, or even more extreme a *why run?* ethos. Just as
/// with a Coq proof, actually running an F\* program can sometimes feel like an
/// unnecessary chore.
///
/// Lately however, as we ramp up the inter-operability testing of miTLS and
/// shipped `production code developed using F\*`_ testing has become more important
///
/// .. _`production code developed using F\*`: https://blog.mozilla.org/security/2017/09/13/verified-cryptography-firefox-57/
///
/// A simple print and test function confirm that the code can be executed.

open FStar.All
open FStar.IO
open FStar.Printf

/// The single most successful debugging tool---and maybe the most iconic *C*
/// feature after `++`---is `printf`. See `this post`_
/// for a celebration of its arrival in F*.
///
/// .. _`this post`: https://fstarlang.github.io/general/2017/11/22/sprintfstar.html

let ppInterval (I f t) = sprintf "0x%d-0x%d" (v f) (v t)

/// I give two implementations for printing `intervals`. The first defines the function recursively, while the second uses a higher-order fold function.

let rec ppIntervals' (is:intervals): ML unit =
  match is with
  | [] -> stdout <| "."
  | i::is ->
      stdout <| ppInterval i;
      stdout <| " ";
      ppIntervals' is

let toI f t = I (int_to_t f) (int_to_t t)

let ppIntervals is = FStar.List.Tot.fold_left (sprintf "%s %s") "" (FStar.List.map ppInterval is)
let main = stdout <| ppIntervals (intersect [toI 3 10; toI 10 15] [toI 1 4; toI 10 14])

/// And the winner is!
/// ==================
///
/// A strange attachment bonds programmers and the language they program in. It
/// is as if the language becomes an extension of their arms, fingers, eyes, and
/// minds. Others have noted the addictive nature of programming and theorem
/// proving. The dopamine rush when a program compiles, runs, or verifies. The
/// language preference is thus a matter of taste. We are no golems, and won't
/// cut off our arm lightly to replace it with a stronger version. Rather we are
/// like junkies who will go back to what we know to get our next fix.
///
/// The title of the post is thus more tongue in cheek. Nevertheless, there are
/// a few dimensions that one could look at if one wanted to do an objective
/// comparison, e.g., developer efficiency, the code to proof ratio, useability
/// and maturity of the system, and the size of the trusted computing base.
///
/// Developer efficiency & code to proof ratio
/// ------------------------------------------
///
/// I measure the success of a project more by the pleasure I get out of it than
/// by the time I put into it. So it won't come as a surprise that I am not a
/// big fan of filling in time sheets. I am interested in surveillance and
/// anti-surveillance, and some day I might be tempted to use Joachim's arbtt_ tool
/// suggestion for a self study on the effects of (self-)surveillance on
/// productivity. Until then I will keep it qualitative.
///
/// I worked on the blog on-off, for about a week, partly on a holiday to get
/// some much needed sun that I found beneficial for both coding and writing. I
/// was positively surprised, if not amazed, by the ease at which F\* could be
/// used to verify side-effect free programs. I have used F\* to verify stateful
/// programs in the past, but that felt substantially harder, likely because it
/// is simply a harder problem.
///
/// I am willing to concede that an experienced Coq expert will get the job done
/// faster than an F\* programmer with only some experience, and, for now the
/// former will be easier to find.
///
/// I would argue that F\* wins hands down when it comes to automation and proof
/// burdon. Coq enthusiasts could argue that automation tactics can bring down
/// the burdon, and that explicit proof scripts have their value. However, it is
/// my impression that F\* gets a lot of leverage from being designed from the
/// ground up for automation---and F\* tactics_ are on their way.
///
/// .. _arbtt: http://arbtt.nomeata.de/
/// .. _tactics: https://github.com/FStarLang/FStar/wiki/Efficient-execution-of-F*-tactics
///
/// Useability, maturity, and trusted computing base
/// ------------------------------------------------
///
/// There are many areas in which bugs in programs have become so expensive,
/// that programmers are willing to walk an extra mile to avoid bug infested
/// code. Modern programming languages and program verification both reduce
/// programming mistakes, and this can justify the effort of learning a new
/// tool.
///
/// There are similarities and synergies between the two. Modern languages,
/// such as strictly typed functional programming languages, ease (mathematical)
/// reasoning about programs and program verification. There are also differences:
/// The expressiveness and abstraction offered by a programming language like
/// Haskell make code more readable. Supporting these in a verification tool may get
/// in the way of automation and can result in a large trusted computing base. The
/// established wisdom here is to have a small core language, and to translate more
/// complex human readable code to the core.
///
/// Ultimately, however, programming is engineering and
/// trade-offs are unavoidable. F\* exposes the full power of
/// the language to programmers/verifiers for as long as possible, and
/// translates into lower-level languages only for execution and proof automation.
/// verification engineers rarely look at the gigabytes of SMT queries produced
/// by F\*, just like programmers rarely have to look at assembly code.
///
/// Of course there is an exception to every rule. `Jonathan Protzenko`_ developed a
/// powerful extraction mechanism called KreMLin_ from a subset of F\* to C. C is
/// the lingua-franca for, among others, efficient cryptographic code. An important
/// property of that translation is that it preserves comments and readability. This
/// is necessary as cryptographic code has to be audited, and the experts with the
/// necessary domain knowledge are unlikely to switch to F\* any time soon.
///
/// However, never say never. Clarke's third and last rule goes as follows:
///
///   When a distinguished but elderly scientist states that something is possible,
///   they are almost certainly right. When they state that something is impossible,
///   they are very probably wrong.
///
/// .. _`Jonathan Protzenko`: https://jonathan.protzenko.fr/
/// .. _KreMLin: https://github.com/FStarLang/kremlin/
/// 
