/// An F* version of the hs-to-coq example by Joachim Breitner (https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it)
module IntervalIntersect
open FStar.All
open FStar.List.Tot
open FStar.IO
open FStar.Printf
open FStar.Math.Lib

///[from] is inclusive, [to] is not inclusive
type interval = | I: from:int -> to:int{from<to} -> interval

let rec goodLIs (is:list interval) (lb:int) =
  match is with
  | [] -> true
  | I f t :: is -> lb <= f
                 //&& f < t  NS: unnecessary
                 && goodLIs is t

let good is =
  match is with
  | [] -> true
  | I f t :: _ -> goodLIs is f

let intervals = is:list interval{good is}

let needs_reorder (is1 is2:intervals) : nat =
  match is1, is2 with
  | I f1 t1 :: _, I f2 t2 :: _ -> if t1 < t2 then 1 else 0
  | _, _ -> 0

let rec go (is1 is2:intervals)
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

let intersect (is1 is2:intervals) = go is1 is2

let rec print_intervals is: ML unit =
  match is with
  | [] -> stdout <| "."
  | i::is ->
    stdout <| sprintf "[%d, %d] " i.from i.to;
    print_intervals is

let main = print_intervals (intersect [I 3 10; I 11 15] [I 1 4; I 10 14])

let range (f t:int): Set.set int =
  Set.intension (fun z -> f <= z && z < t)

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

let lemma_intersection_range_range (f1 t1 f2 t2:int)
  : Lemma
    (ensures (Set.intersect (range f1 t1) (range f2 t2) == range (max f1 f2) (min t1 t2)))
  = Set.lemma_equal_elim (Set.intersect (range f1 t1) (range f2 t2))
                         (range (max f1 f2) (min t1 t2))

let lemma_intersection_range_range_empty (f1 t1 f2 t2:int)
  : Lemma
    (requires (t1 <= f2) \/ (t2 <= f1))
    (ensures Set.intersect (range f1 t1) (range f2 t2) == Set.empty)
  = Set.lemma_equal_elim ( Set.intersect (range f1 t1) (range f2 t2) ) Set.empty

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
  if (Cons? (tl is)) then
    begin
      let h::t = is in
      lemma_intersection_range_semLIs_empty h.from h.to t h.to
    end
  else ()


let lemma_disjoint_prefix (is1:intervals{Cons? is1})  (is2:intervals{Cons? is2})
  : Lemma 
    (requires (hd is1).from >= (hd is2).to )
    (ensures (Set.intersect (sem is1) (sem is2) == Set.intersect (sem (is1)) (sem (tl is2))))
  =
  let h2 = (hd is2) in
  lemma_intervals_disjoint (h2::is1);
  assert(Set.disjoint (semI (h2)) (sem (is1)));
  Set.lemma_equal_elim (Set.intersect (sem is1) (sem is2)) (Set.intersect (sem (is1)) (sem (tl is2)))


let rec lemma_overlapping_prefix (is1:intervals{Cons? is1}) (is2:intervals{Cons? is2})
  : Lemma
    (requires (hd is1).to > (hd is2).to /\ (hd is1).from < (hd is2).to)
    (ensures (
        let h1::t1 = is1 in
        let h2::t2 = is2 in
        let f_max = max h1.from h2.from in
        Set.equal  (Set.intersect (sem is1) (sem is2))
                   (Set.union (semI (I f_max h2.to))
                              (Set.intersect (Set.union (range (h2.to) (h1.to)) (sem t1)) 
                                             (sem t2)) )))
  =
  let h1::t1 = is1 in
  let h2::t2 = is2 in
  let f_max = max h1.from h2.from in
/// (i1 u is1) n (i2 u is2) = (i1 n (i2 u is2)) u (is1 n (i2 u is2)) 
///                         = (i1 n i2) u (i1 n is2) u (is1 n i2) u (is1 n is2)
  assert (Set.equal (Set.intersect (sem is1) (sem is2))
                    (Set.union
                      (Set.union (Set.intersect (semI h1) (semI h2)) (Set.intersect (semI h1) (sem t2)))
                      (Set.union (Set.intersect (semI h2) (sem t1)) (Set.intersect (sem t1) (sem t2)))
                    ));
  assert (Set.equal (Set.intersect (semI h1) (semI h2)) (semI (I f_max h2.to)));
  lemma_intersection_range_semLIs_empty h1.from h2.to t2 h2.to;
  assert (Set.disjoint (range h1.from h2.to) (sem t2));
  assert (Set.equal (range h1.from h1.to) (Set.union (range h1.from h2.to) (range h2.to h1.to)));
  assert (Set.equal (Set.intersect (range h1.from h1.to) (sem t2)) (Set.intersect (range h2.to h1.to) (sem t2)));
  lemma_intervals_disjoint (h2::t1)

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
       let f_max = max (i1.from) (i2.from) in
       let f_min = min (i1.from) (i2.from) in
       // reorder for symmetry
       if i1.to < i2.to then lemma_intersection_spec (i2::is2) (i1::is1)
       // disjoint i2.from, i2.to, i1.from, i1.to
       else if i1.from >= i2.to then (
         lemma_intersection_spec (i1::is1) is2;
         assert (Set.disjoint (semI i1) (semI i2));
         lemma_disjoint_prefix (i1::is1) (i2::is2);
         ()
       )
       // subset f_min, f_max, i1.to=i1.to,
       else if i1.to = i2.to then (
         assert (Set.equal (Set.intersect (semI i1) (semI i2)) (semI (I f_max i1.to)));
         lemma_intervals_disjoint (i2::is1);
         lemma_intervals_disjoint (i1::is2);
         lemma_intersection_spec is1 is2;
         ()
       )
       // overlapping
       else  (
         lemma_overlapping_prefix (i1::is1) (i2::is2);
         lemma_intersection_spec (I (i2.to) (i1.to) :: is1) is2
       )
    end





