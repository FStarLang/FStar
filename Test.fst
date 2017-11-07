module Test

// let rec false_elim (#a:Type) (u:unit{false}) : Tot a = false_elim ()

// let a n :nat = 1
// let f (ls:list nat) :nat =
//   let rec aux (xs:list nat) :nat = a 0
//   in
//   0

// assume type t (n:nat) :Type0
// assume val foo: #n:nat{n > 0} -> t n -> Tot unit

// let bar (k:nat) (x:t k) = if k > 0 then foo x else ()


let rec fact (a:Type u#a) (x:nat) :nat = if x = 0 then 0 else x + fact a (x - 1)

let foo (a:Type u#a) = assert_norm (fact a 2 = 3)

//let rec sum (a:Type) (x:nat) :Tot nat = if x = 0 then 1 else sum a (x - 1)



// assume type predicate: Type0

// assume val bar (x:int{predicate}) :Tot unit

// let foo (x:int) :Lemma (requires True) (ensures predicate) [SMTPat (bar x)] = admit ()

// let baz () :Lemma (requires True) (ensures (predicate)) = foo 0

// let fa_intro_lem (p:int -> Type0) (f:(x:int -> squash (p x))) :Lemma (forall (x:int). p x)
//   = FStar.Classical.forall_intro #int #p (fun x -> (f x <: Lemma (p x)))
