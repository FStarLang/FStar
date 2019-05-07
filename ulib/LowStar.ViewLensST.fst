(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module LowStar.ViewLensST

open FStar.HyperStack.ST

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.ViewLens

effect LensST (a:Type)
           (#roots:Type0)
           (#v:Type0)
           (l:hs_view_lens roots v)
           (pre: v -> Type)
           (post: v -> a -> v -> Type) =
       STATE a
            (fun (k:a -> HS.mem -> Type)
               (h0:HS.mem) ->
               inv l h0 /\               //Require the lens invariant
               pre (view l h0) /\        //Require the pre-condition on the view
               (forall (x:a) (h1:HS.mem).
                 inv l h1 /\                          //Ensure the lens invariant
                 B.modifies (as_loc (fp l)) h0 h1 /\  //Ensure that only lens's footprint is modified
                 post (view l h0) x (view l h1) ==>   //Ensure the post-condition on the view
                 k x h1))                             //prove the  continuation under this hypothesis

let star_pre_t (#v:Type) (#v':Type) (pre:v -> Type0) (x:v * v') : Type0 = 
  pre (fst x)

let star_post_t (#a:Type) (#v:Type) (#v':Type)
                (post:v -> a -> v -> Type0) (x:v * v') (y:a) (z:v * v') : Type0 =
  post (fst x) y (fst z)

let frame (#a:Type) (#roots:Type) (#v:Type) (#roots':Type) (#v':Type)
          (#pre:v -> Type0) (#post:v -> a -> v -> Type0)
          (l:hs_view_lens roots v) 
          (l':hs_view_lens roots' v'{B.loc_disjoint (as_loc l.fp) (as_loc l'.fp)})
          (f:unit -> LensST a l pre post)
        : LensST a (l <*> l') (star_pre_t pre) (star_post_t post) = 
  f ()



(* `for_n`: A simple for-loop example, for i in [0 .. n) *)
let for_n (#a #b:_) (#lens:hs_view_lens a b)
          (n:nat)
          (inv: (i:nat{i<=n} -> b -> prop))
          (f: (i:nat{i<n}
              -> LensST unit lens
                (requires fun b -> inv i b)
                (ensures fun b0 _ b1 -> inv (i + 1) b1)))
   : LensST unit lens
     (requires fun b0 -> inv 0 b0)
     (ensures fun b0 _ b1 -> inv n b1)
   = let rec aux (i:nat{i <= n})
       : LensST unit lens
           (inv i)
           (fun _ _ -> inv n)
       = if i = n then ()
         else (f i; aux (i + 1))
     in
     aux 0


