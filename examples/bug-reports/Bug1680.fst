module Bug1680

open FStar.Tactics
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality

(* All assertions below should succeed. This used to not work
 * since `F.on_dom` was not marked as `unfold`. *)

type dim = i:int{i > 0} // type for matrix dimensions
let knat (k:dim) = i:nat{i < k} // bounded nats for indices

type matrix 'a (m:dim) (n:dim) = knat m & knat n ^-> 'a
type vector 'a (l:dim) = knat l ^-> 'a

let row (#a:Type) (#m #n:dim) (x:matrix a m n) (i:knat m) : Tot (vector a n) =
  F.on (knat n) (fun j -> x (i,j))

let col (#a:Type) (#m #n:dim) (x:matrix a m n) (j:knat n) : Tot (vector a m) =
  F.on (knat m) (fun i -> x (i,j))

// sum over vector
private
let rec sum_i (#l:dim) (v:vector int l) (i:knat l)
  : Tot int (decreases (l-i))
  = if i = l - 1 then (v i) else (v i) + (sum_i v (i+1))

let sum (#l:dim) (v:vector int l) = sum_i v 0

open FStar.Mul

// vector product (dot product)
private
let vec_prod_pointwise (#l:dim) (v1 v2:vector int l) : vector int l
  = F.on (knat l) (fun i -> (v1 i) * (v2 i))

let vec_prod (#l:dim) (v1 v2:vector int l) : int
  = sum (vec_prod_pointwise v1 v2)

// matrix multiplication
let matrix_mul (#m #n #p:dim) (x1:matrix int m n) (x2:matrix int n p)
  : matrix int m p
  = F.on (knat m & knat p)
         (fun (i,j) -> vec_prod (row x1 i) (col x2 j))

// transpose
let transpose (#a:Type) (#m #n:dim) (x:matrix a m n)
  : matrix a n m
  = F.on (knat n & knat m) (fun (i,j) -> x (j,i))

// Now we wanted to define a particular matrix, and assert different
// facts about its entries.

let x : matrix int 2 2 =
  F.on (knat 2 & knat 2)
       (fun (i,j) -> if j = i then 0 else 1)
let xt = transpose x
let xtx = matrix_mul xt x

let _ = assert (xtx (0,0) == 1)
let _ = assert (xtx (0,1) == 0)
let _ = assert (xtx (1,0) == 0)
let _ = assert (xtx (1,1) == 1)

// It seems like all these assertions should be easy to solve with
// unfolding and function application, but the second assert will fail
// unless you include the by compute(). If we manually unfold the
// definition of matrix multiplication (xtx_unfolded below), then all
// assertions succeed.

let xtx_unfolded = F.on (knat 2 & knat 2) (fun (i,j) -> vec_prod (row xt i) (col x j))

let _ = assert (xtx_unfolded (0,0) == 1)
let _ = assert (xtx_unfolded (0,1) == 0)
let _ = assert (xtx_unfolded (1,0) == 0)
let _ = assert (xtx_unfolded (1,1) == 1)
