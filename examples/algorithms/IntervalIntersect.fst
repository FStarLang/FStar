module IntervalIntersect

#set-options "--use_two_phase_tc true"

(*** Can F* replace Haskell and Coq? *)
/// Is F\* ready for its first "F* vs 'pick your favourite language or proof
/// assistant'" flame war? Can it take on heavyweights such as Haskell and Coq?
///
/// Its list of supported features is full of fanciful words such as polymorphism,
/// dependent types, user-defined monadic effects, refinement types, weakest
/// precondition calculus, predicative hierarchy of universes with universe
/// polymorphism, rich type-level computation, proofs by reification and so forth,
/// but does F/* solve real world problems and does one need a PhD in type theory to
/// use it? Is F\* ready for prime time?
///
/// Of course the answer to this question will always depend on *who* you are and
/// what you want to do? I will talk a bit more about *what* I am doing and *how* I
/// got to work on F\* in the first place, but let it suffice to say that my PhD
/// is in cryptography, not type theory and involved mathematical models and proofs mostly
/// done on paper. This means that my programming skills usually are a bit
/// [Rust|https://www.rust-lang.org]y, no pun intended.
///
/// As to the *what*. About a week ago I came across [Joachim Breitner's inspiring
/// blog
/// post|https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it]
/// on finding bugs in Haskell code by proving it. It is an excellent post.
/// Pitched at the right level for both the applied Haskell programmer and
/// someone like me curious about Haskell and Coq in theory---without a lot of
/// exposure to them in practice. What is nice about these two languages is that
/// general knowledge of mathematical notation and functional programming goes
/// some way towards understanding the gist of the code. Its concise and engaging
/// programming style motivated me to dust off my F* skills. So instead of
/// parsing all of the Haskell and Coq code in detail, I decided to rewrite
/// the example in F/* to explore the example.
///
/// This ended up being quite a lengthy post, so let me prepare you a bit as to what
/// to expect in case you want to do some cherry picking.
///
///  * The importance of libraries
///  * Part 1: Proving the intervals invariant
///  * Part 2: Proving functional correctness
///    - The mathematical representation of intervals
///    - The heart of the proof
///    - Taking stock: intrinsic vs. extrinsic, intensional vs extensional
///  * Extraction and testing
///  * And the winner is!
///    - Efforts and gains
///    - Why functional programming and types

/// (**** The importance of libraries *)
///
/// Most of the code is about lists of integers. Luckily there is decent
/// library support for both integers and lists in F\*. As explained by Joachim,
/// verification loves termination. Se we use a list library of pure and total
/// operations for both implementation and specifications. In particular list operations
/// are provably terminating.

open FStar.List.Tot
open FStar.Math.Lib

type offset = int

/// As in its Haskell version, I represent intervals as a datatype constructor. Note
///  that [from] is inclusive and [to] is exclusive.

type interval = | I: from:offset -> to:offset -> interval

/// F/* automatically generates accessor functions for the named arguments of the
/// dependently typed constructor. Given [i:interval], [I?.from i] returns the
/// start of the interval. Datatypes with a single constructor, also allow for
/// the usual '.' notation, e.g., [i.from], which makes them a convenient
/// alternative to records.

(**** Part 1: Proving the intervals invariant *)

/// We define the goodness of [interval list]s in the same way as Joachim did in
/// Coq. A [good interval list] is ordered and consists of non-empty disjoint
/// intervals.

let rec goodLIs (is:list interval) (lb:offset) =
  match is with
  | [] -> true
  | I f t :: is -> lb <= f && f < t && goodLIs is t

/// Contrary to Joachim's informal claims, already in his Coq development
/// intervals are however not necessarily non-adjacent. This is a good example
/// for a divergence between formal spec and human intuitive expectations. Just
/// because we verified something, doesn't necessarily mean that we get what we
/// want. Something has to give, either we remove the informal non-adjacency
/// requirement, or strengthen the [goodLIs] predicate to require [lb < f].

let good is =
  match is with
  | [] -> true
  | I f t :: _ -> goodLIs is f

/// Coq is then used to prove that the [intersect] of two [good] [interval
/// list]s is itself a [good interval list]. Upon investigation, this invariant
/// should in fact hold at all times, so I make good use of F^*'s refinement
/// types, to add the requirement to the [intervals].

let intervals = is:list interval{good is}

/// This is a first example for F*'s closely intertwines programming and
/// verification style. Often Z3 can prove refinements automatically by
/// discharging them as SMT constraint queries.

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
      else I f' (i2.to) ::
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
///
/// I am cryptographer and we like to give paper proofs of results that seem
/// almost magical. Naturally, the proof is by induction. So after a recursive
/// call to [go], the induction hypothesis is available, and we know that the
/// returned [intervals] are good. The SMT solver can also prove locally that
/// the interval prepended to this result is non-empty, what remains to be shown
/// is that together they are ordered. That is where knowing that the [from] of
/// the first result intervals is the [max] saves the day.
///
///    (**** Part 2: Proving functional correctness *)
///
/// I could have stopped here and declare victory, 1:0 for FStar. Arguable there
/// are few blemishes, like the F* bug with local functions that I discovered, orq
/// the low priority given to a weakes precondition calculus supporting [when]
/// clauses, but overall I was positively surprised by the speed at which I
/// could translate the Haskell and Coq code to F* and by how little I had to
/// do in terms of writing proofs.
///
/// Mindful of Clarke's second law that the only way of discovering the limits
/// of the possible is to venture a little way past them into the impossible, we
/// wont stop when its easy. The second property that Joachim proved about the
/// [intersect] function is that it corresponds to its corresponding function.
/// This sounds a bit tautological. What is meant here is that it corresponds to
/// another way of representing intervals and another way of implementing
/// intersection in that representation. Ideally this alternative way is in
/// some sense be more pure and mathematical.
///
(***** The mathematical representation of intervals *)
///
/// In traditional mathematics, intervals are of course represented as sets, and
/// interval intersection simply becomes set intersection. Luckily, the
/// [FStar.Set] module already provides us with set operations proven to be pure
/// and total.
///
/// However, unlike `Coq.Sets.Ensembles` the representation of [set a] as a function
/// [a -> bool] is abstract in F/*. Consequently, we cannot define [range] using a
/// lambda expression. This is what is lost, what do we then gain by hiding the
/// representation of sets behind an abstraction? We can change the way sets are
/// represented in [FStar.Set] under the hood, without affecting users of the
/// library. Indeed F* libraries often have two implementations, one acting as a
/// model to prove that the pre- and post-conditions of the API do not allow to
/// prove [False], and an actual implementation for running the actual program. In
/// fact different extraction targets, such as OCaml and F# would typically provide
/// different implementations, e.g. the OCaml implementation is based on
/// [Batteries|http://batteries.forge.ocamlcore.org/].
///
/// The declarative definition of a set using a predicate that all set members
/// need to satisfy is known in mathematics as an intensional definition.
/// Certain sets, for example the set of even numbers can only be defined
/// intensionally. My intuition is that intensional definitions are more concise
/// and better suited for proof, conversely, extensional definitions are more
/// explicit guaranteeing that sets are finite.
///
/// To get the best of both worlds, I give both an intensional and an
/// extensional description of integer ranges, but make the intensional
/// definition ghost. This means that it never has to be extracted to [BatSet]
/// based OCaml code.

let rangeGT (f t:offset): GTot (Set.set offset) = Set.intension (fun z -> f <= z &&
  z < t)

/// The fact that I had to extend the [FStar.Set] library, rather than extend in
/// a separate file as in the Coq development stems from the immayturity of F*
/// and the need for abstraction to simultaneously support verification and
/// extraction. I use the ghostly intensional definition to specify the logical
/// properties of the extensional definition.

let rec range (f t:offset): Tot (r:Set.set offset{r==rangeGT f t})
  (decreases %[t-f])
  =
  if f>=t then (
    Set.lemma_equal_elim (rangeGT f t) Set.empty;
    Set.empty
  ) else (
    Set.lemma_equal_elim (rangeGT f t) (Set.union (Set.singleton f) (rangeGT (f+1) t ));
    Set.union (Set.singleton f) ( range (f+1) t )
  )

/// The proof that the extensionally defined set is the same as the
/// intensionally defined set uses induction, and the set equality `[f,t] = {f}
/// u [f+1,t]`.
///
/// Using [range] and following the Coq code, the [semI] and [sem] functions
/// define the semantic of bounds based interval representations in terms of
/// integer sets.

let semI (i : interval) : Set.set offset =
  range i.from i.to

let rec sem (is : intervals) : Set.set offset =
  match is with
  | [] -> Set.empty
  | (i :: is) -> Set.union (semI i) (sem is)

/// This simple lemma should likely move to the [FStar.Set], but it gives me the
/// opportunity explain some of F* automation power. The body of the lemma is
/// straightforward and the proof is by definition. What the SMT pattern lemma
/// does is to 'remind' the SMT solver that it can prove disjointness whenever
/// the intersection of two sets is empty. Below I commented out two invocations
/// of the lemma where the lemma is now automatically applied because of the
/// pattern.

let lemma_disjoint_intro (#a:eqtype) (s1 s2:Set.set a)
  : Lemma
    (requires Set.equal (Set.intersect s1 s2) Set.empty)
    (ensures Set.disjoint s1 s2)
    [SMTPat (Set.disjoint s1 s2)]
 = ()


/// I use the lemma to prove that an interval is disjoint from an interval list
/// whenever their concatenaton is [good].

let lemma_semI_sem_disjoint (i:interval) (is:intervals)
  : Lemma
    (requires good (i::is))
    (ensures (Set.disjoint (semI i) (sem is)))
  =
///  The following local lemma is inspired by Joachim's
///  `Intersection_range_semLIs_empty` lemma. It expresses the same idea and is
///  proven by induction on an increasing lower bound.

  let rec lemma_semI_sem_lb_disjoint (i:interval) (is:intervals) (lb:offset)
    : Lemma
      (requires goodLIs is lb /\ i.to <= lb)
      (ensures Set.disjoint (semI i) (sem is))
    =
    if (Cons? is) then
       lemma_semI_sem_lb_disjoint i (tl is) (hd is).to
    else ();
    Set.lemma_equal_elim (Set.intersect (semI i) (sem is)) Set.empty in
  lemma_semI_sem_lb_disjoint i is i.to
  // ; lemma_disjoint_intro (semI h) (sem t) //needed if SMTPat is removed

(***** The heart of the proof *)

/// We now get into the heart of the correctness proof for [intersect]. Recall that Joachim's algorithm (after switching) distinguishes three cases about the head elements of two interval lists:
///  1. the heads are disjoint
///  2. the second head is a subset of the first
///  3. the tho heads are overlapping
/// We prove a lemma for each case.
///
/// The first lemma states that if the heads are disjoint, then the head with
/// the smaller [to] can be dropped from the [intersect] computation.

let lemma_disjoint_prefix (is1:intervals{Cons? is1})  (is2:intervals{Cons? is2})
  : Lemma
    (requires (hd is1).from >= (hd is2).to )
    (ensures (Set.intersect (sem is1) (sem is2) == Set.intersect (sem (is1)) (sem (tl is2))))
  =
  let h2 = hd is2 in
  lemma_semI_sem_disjoint h2 is1;
  Set.lemma_equal_elim (Set.intersect (sem is1) (sem is2)) (Set.intersect (sem (is1)) (sem (tl is2)))

/// The second lemma states that if the second head is a subset of the first,
/// then the result of [intersect] is the union of that subset and the
/// [intersect] computation with both heads dropped.

let lemma_subset_prefix (is1:intervals{Cons? is1}) (is2:intervals{Cons? is2})
  : Lemma
    (requires (hd is1).to = (hd is2).to /\ (hd is1).from < (hd is2).to)
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

/// No, unfortunately this is not a panacea. Rather, it is a proven recipe for
/// spending too much time idlying just to get the infamous "(Error) could not
/// prove post-condition" error. Time that one should instead spend on thinking
/// about the nature of what needs to be proven.
///
/// To shortcut the thinking a bit, I looked at the Coq proof script. While most
/// of it was pretty well obfuscated without a detailed knowledge of Coq tactics
/// and the ability to see the proof state, it revealed some crucial hints.
///
/// One was the equivalent of the [lemma_semI_sem_lb_disjoint] lemma and its
/// proof. The other was the importance of set operation distributivity for the
/// proof.

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
/// The [assert] below expresses the outcome of the repeated application of set
/// distributive law to state the following equality:
///
/// (h1 u t1) n (h2 u t2) = (h1 n (h2 u t2)) u (t1 n (h2 u t2))
///                       = (h1 n h2) u (h1 n t2) u (t1 n h2) u (t1 n t2)

  let is1_n_is2 = Set.intersect (sem is1) (sem is2) in
  assert (Set.equal is1_n_is2
                    (Set.union (Set.union (Set.intersect (semI h1) (semI h2))
                                          (Set.intersect (semI h1) (sem t2)))
                               (Set.union (Set.intersect (semI h2) (sem t1))
                                          (Set.intersect (sem t1) (sem t2)))));
///
///  The rest of the proof simplifies the first three of the four intersects:
///  1. h1 n h2 = [f', h2.to]
///
  assert (Set.equal (Set.intersect (semI h1) (semI h2)) (semI (I f' h2.to)));
///  2. h1 n t2 = [h2.to h1.to] n t2

  lemma_semI_sem_disjoint (I h1.from h2.to) t2;
  assert (Set.equal (range h1.from h1.to)
                    (Set.union (range h1.from h2.to) (range h2.to h1.to)));
  assert (Set.equal (Set.intersect (range h1.from h1.to) (sem t2))
                    (Set.intersect (range h2.to h1.to) (sem t2)));
///  3. h2 n t1 = empty
///
  lemma_semI_sem_disjoint h2 t1;
///
/// The proof now applies the distributive law in the other direction to combine the 3rd and 4th intersect:

  Set.lemma_equal_elim is1_n_is2
                       (Set.union (semI (I f' h2.to))
                                  (Set.intersect (Set.union (range (h2.to) (h1.to))
                                                            (sem t1))
                                                 (sem t2)) )

/// The following pragma resets the SMT solver to its original resource limit (roughly 5 seconds):

#reset-options

#set-options "--use_two_phase_tc true"

/// The final proof is by case analysis, in each step relying on the induction
/// hypothesis and one of the lemmas. Again the [assert]s document document the
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
       if i1.to < i2.to then lemma_intersection_spec (i2::is2) (i1::is1)
       // disjoint: i2.from < i2.to <= i1.from < i1.to
       else if i1.from >= i2.to then (
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

(***** Taking stock: intrinsic vs. extrinsic, intensional vs extensional *)

/// Clearly the second part of verifying [intersect] was much harder. While in the
/// first we used F* essentially as a programming language with stronger types and
/// great automation, in the second we relied on hand-written lemmas and
/// proofs.
///
/// The two parts are also examples of what in F* jargon are called intrinsic and
/// extrinsic verification styles. In the intrinsic verification style, the property
/// is expressed in the function definition itself, e.g., by refining operand and
/// return types, while in the extrinsic verification style, the property is
/// expressed as a lemma and proved separately.
///
/// The code/definition to proof ratio is larger in part 2, but is still
/// substantially smaller than in the Coq development. In addition to the proof
/// scripts, Joachim's development relied on about 160 lines of lemma code about Coq
/// ensembles, compared to the additional 10 additional lines in [FStar.Set] to
/// support intensional set definitions, and the [lemma_disjoint_intro] lemma.
/// Arguably this is not what Jachim optimised for. True to the title of the blog
/// his priority was to prove the code and find bugs, rather than find the most
/// elegant proof.
///
/// I in turn dedicated some time to cleaning up the code and to make it robust to
/// with regards to the unpredictability of the SMT solver. This is to support a
/// claim I want to make about the F* code being easier to maintain and adapt. The
/// `hs-to-coq` authors understood the importance of proofs evolving with programs,
/// not the lease because programs often change. The concise and closely integrated
/// F\* proof makes maintaining programs easier. It acts as verified documentation
/// that like good wine keeps its value over time as code is handed
/// down through generations of programmers.
///
(**** Extraction and testing *)
///
/// Another crucial to program longevity is *testing*. This is not something F/* has
/// traditionally been good at. Both Haskell and Coq follow the *typecheck first*,
/// of *just typecheck* ethos. Actually running an F* program can sometimes feel
/// like an unnecessary chore.
///
/// Lately however, as we ramp up the inter-operability testing of miTLS.
/// A simple print and test function confirm the code can be executed.

open FStar.All
open FStar.IO
open FStar.Printf


let ppInterval (I f t) = sprintf "0x%d-0x%d" f t

let rec ppIntervals' (is:intervals): ML unit =
  match is with
  | [] -> stdout <| "."
  | i::is ->
      stdout <| ppInterval i;
      stdout <| " ";
      ppIntervals' is


let ppIntervals is = FStar.List.fold_left (sprintf "%s %s") "" (FStar.List.map ppInterval is)
let main = stdout <| ppIntervals (intersect [I 3 10; I 10 15] [I 1 4; I 10 14])

(**** And the winner is! *)

let a = ()
///
(***** Efforts and gains *)
/// I measure the success of a project more by the pleasure I get out of it than
/// by the time I put into it. So it won't come as a surprise that I am not a
/// big fan of filling in time sheets. I am interested in surveillance and
/// anti-surveillance, and I am tempted to use Joachim's tool suggestion for a
/// self study on the effects of (self-)surveillance on my productivity. Until
/// then I will keep it qualitative.
///
/// I worked on the blog on off, for about a week, partly on a holiday to get
/// some much needed sun that I found beneficial for both coding and writing. I
/// wast positively surprised, if not amazed, by the ease at which F/* could be
/// used to verify side-effect free programs. I have used F/* to verify stateful
/// programs in the past, but that felt substantially harder, likely because it
/// is simply a harder problem.
let b = ()

(***** Why functional programming and types *)
///
/// There are many areas in which bugs in programs have become so
/// expensive, that programmers are willing to walk an extra mile to avoid bug
/// infested code.
///
/// Two popular approaches for this are the use of modern programming languages
/// and program verification.
///
/// There are some similarities and synergies between the two. Modern languages,
/// such as strictly typed functional programming languages, ease (mathematical)
/// reasoning about programs and program verification. There are also differences:
/// The expressiveness and abstraction offered by a programming language such as
/// Haskell make code more readable. Supporting these in a verification tool may get
/// in the way of automation and can result in a large trusted computing base. The
/// established wisdom here is to have a small core language, and to translate more
/// complex human readable code to that core.
///
/// Ultimately, however, programming development is about engineering, and
/// trade-offs need to be made. F/*'s philosophy is to expose the full power of the
/// language to programmers/verifiers for as long as possible, and to translate to
/// lower-level languages only for execution and for the automation of verification.
/// verification engineers don't have to look at the gigabytes of SMT queries
/// produced by F\* to gain the utility of automation, just like programmers rarely
/// have to look at assembly code.
///
/// Of course there is an exception to every rule, and the F\* team is currently
/// developing a powerful extraction mechanism from a subset of F/* to C, the
/// lingua-franca for, among others, efficient cryptographic code. An important
/// property of that translation is that it preserves comments and readability, as C
/// programmers with the necessary domain knowledge to audit the code are unlikely
/// to switch to F\* any time soon.
///
/// However, never say never. Clarke's third and last rule goes as follows: When
/// a distinguished but elderly scientist states that something is possible,
/// they are almost certainly right. When they state that something is
/// impossible, they are very probably wrong.
///
let the_end = ()
