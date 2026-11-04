module ArrayMetadata
#lang-pulse
open Pulse
open Pulse.Lib.Send
module A = Pulse.Lib.Array.Core

let subview_metadata (#t: Type) (arr: A.array t)
    (i: nat) (j: nat { i <= j /\ j <= A.length arr })
    : Lemma (
      A.loc_id_of_array (A.gsub arr i j) == A.loc_id_of_array arr /\
      A.visibility_of_array (A.gsub arr i j) == A.visibility_of_array arr) =
  A.loc_id_of_array_gsub arr i j;
  A.visibility_of_array_gsub arr i j

ghost fn move_empty_mask u#a (#t: Type u#a) (arr: A.array t)
    (f: perm) (v: Seq.seq (option t)) (l1 l2: loc_id)
  requires on l1 (A.pts_to_mask arr #f v (fun _ -> False))
  ensures on l2 (A.pts_to_mask arr #f v (fun _ -> False))
{
  placeless_move (A.pts_to_mask arr #f v (fun _ -> False)) l1 l2;
}

ghost fn localize_empty_mask u#a (#t: Type u#a) (arr: A.array t)
    (f: perm) (v: Seq.seq (option t)) (l: loc_id)
  requires on l (A.pts_to_mask arr #f v (fun _ -> False))
  ensures A.pts_to_mask arr #f v (fun _ -> False)
{
  placeless_on_elim (A.pts_to_mask arr #f v (fun _ -> False)) l;
}

[@@expect_failure [228]]
ghost fn nonempty_mask_is_not_placeless u#a (#t: Type u#a) (arr: A.array t)
    (f: perm) (v: Seq.seq (option t)) (l1 l2: loc_id)
  requires pure (0 < A.length arr)
  requires on l1 (A.pts_to_mask arr #f v (fun _ -> True))
  ensures on l2 (A.pts_to_mask arr #f v (fun _ -> True))
{
  placeless_move (A.pts_to_mask arr #f v (fun _ -> True)) l1 l2;
}

[@@expect_failure [228]]
ghost fn cannot_fabricate_empty_mask u#a (#t: Type u#a) (arr: A.array t)
    (f: perm) (v: Seq.seq (option t))
  ensures A.pts_to_mask arr #f v (fun _ -> False)
{}
