/// An F* version of the hs-to-coq example by Joachim Breitner (https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it)
module IntervalIntersect
open FStar.All
open FStar.List.Tot
open FStar.IO
open FStar.Printf

///[from] is inclusive, [to] is not inclusive
type interval = | I: from:int -> to:int -> interval

let rec goodLIs (is:list interval) (lb:int) =
  match is with
  | [] -> true
  | (I f t :: is) -> lb <= f && f < t && goodLIs is t

let good is = 
  match is with
  | [] -> true
  | (I f t :: _) -> goodLIs is f 

let intervals = is:(list interval){good is}

let needs_reorder (is1:intervals) (is2:intervals): nat =
  match is1, is2 with
  | (I f1 t1 :: _), (I f2 t2 :: _) -> if (t1 < t2) then 1 else 0
  | _, _ -> 0

val go: is1:intervals -> is2:intervals -> Pure (ris:intervals) 
  (requires True)
  (ensures (fun ris -> True
    /\ ( Cons? ris /\ Cons? is1 /\ Cons? is2 ==> 
        (hd ris).from >= Math.Lib.max ((hd is1).from) ((hd is2).from)  )
    /\ ( Nil? is1 \/ Nil? is2 ==> Nil? ris )))
  (decreases %[List.length is1 + List.length is2; needs_reorder is1 is2])
let rec go is1 is2 =
  match is1, is2 with
  | _, [] -> []
  | [], _ -> []
  | (i1::is1), (i2::is2) ->
    begin
      let f' = Math.Lib.max (i1.from) (i2.from) in
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

val intersect: is1:intervals -> is2:intervals -> ris:intervals
let intersect is1 is2 =
  go is1 is2

let rec print_intervals is: ML unit =
  match is with
  | [] -> (print_string ".")
  | (i::is) ->
    begin
      print_string (sprintf "[%d, %d] " i.from i.to);
      print_intervals is
    end

let main = print_intervals (intersect [I 3 10; I 11 15] [I 1 4; I 10 14])

let range (f:int) (t:int): Set.set int =
  Set.intension #int (fun z -> (f <= z) && (z < t))

let semI (i : interval) : Set.set int =
  range i.from i.to

let rec semLIs (is : intervals) : Set.set int =
  match is with
  | [] -> Set.empty #int
  | (i :: is) -> Set.union #int (semI i) (semLIs is)

val lemma_intersection_spec: is1:intervals -> is2 : intervals -> Lemma
  (requires True)
  (ensures (Set.equal ( semLIs (intersect is1 is2) ) (Set.intersect #int (semLIs is1) (semLIs is2))))
  (decreases %[List.length is1 + List.length is2; needs_reorder is1 is2])

val lemma_disjoint_intro: #a:eqtype -> s1:Set.set a -> s2:Set.set a -> Lemma
  (requires Set.equal (Set.intersect s1 s2) Set.empty)
  (ensures Set.disjoint s1 s2)
  [SMTPat (Set.disjoint s1 s2)]
let lemma_disjoint_intro #a s1 s2 = ()

val lemma_disjoint: is1:intervals{Cons? is1} -> is2:intervals{Cons? is2} -> Lemma
  (requires Set.disjoint #int (semI (hd is1)) (semI (hd is2)))
  (ensures (Set.equal (Set.intersect #int (semLIs (is1)) (semLIs (tl is2))) (Set.intersect #int (semLIs is1) (semLIs is2)) ))
let lemma_disjoint is1 is2 = admit()

let rec lemma_intersection_spec is1 is2 = 
  match is1, is2 with
  | [], [] -> ()
  | _, [] -> () 
  | [], _ -> ()
  | (i1::is1), (i2::is2) -> 
    begin 
       let f_max = Math.Lib.max (i1.from) (i2.from) in
       let f_min = Math.Lib.min (i1.from) (i2.from) in
       // reorder for symmetry
       if i1.to < i2.to then lemma_intersection_spec (i2::is2) (i1::is1)
       // disjoint
       else if i1.from >= i2.to then ( 
         lemma_intersection_spec (i1::is1) is2;
         assert (Set.disjoint #int (semI i1) (semI i2));
         lemma_disjoint (i1::is1) (i2::is2);
         //assert (False);
         () )
       // subset
       else if i1.to = i2.to then ( 
         ignore (I f_max (i1.to)); 
         lemma_intersection_spec is1 is2; 
         assert (Set.disjoint #int (semI (I i1.from f_max)) (semI (I i2.from f_max)));
         if i1.from >= i2.from then (
           if (Cons? is1) then
             () 
           else
             ();
           admit() 
         )
         else 
          admit()
       )
       // overlapping
       else  ( 
         ignore (I f_max (i2.to)); 
         lemma_intersection_spec (I (i2.to) (i1.to) :: is1) is2; 
         assert (Set.disjoint #int (semI (I i1.from f_max)) (semI (I i2.from f_max)));
//         lemma_disjoint ((I i1.from f_max)::is1 ) ((I i2.from f_max)::is2);
         admit() )
   end
