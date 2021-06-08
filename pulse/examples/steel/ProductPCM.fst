module ProductPCM

/// We define a PCM for structs with two fields {a; b} by defining a
/// PCM for tuples (a & b) in terms of (potentially user-defined) PCMs
/// for a and b.

val comp : pcm 'a -> pcm 'b -> 'a & 'b -> prop
let comp p q (xa, xb) (ya, yb) = composable p xa xb /\ composable q ya yb

val combine : pcm 'a -> pcm 'b -> x: 'a & 'b -> y: 'a & 'b {comp x y} -> 'a & 'b
let combine p q (xa, xb) (ya, yb) = (op p xa ya, op q xb yb)

let pcm_t #a #b (p:pcm a) (q:pcm b) : pcm (t a b) = FStar.PCM.({
  p = {
    composable=comp p q;
    op=combine p q;
    one=(one, one)
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun (xa, xb) -> refine p xa /\ refine q xb) (* TODO check *)
})

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

let pcm_all_or_none #a : pcm (option a) = FStar.PCM.({
  p = {
    composable=fun #a #b x y -> match x, y with None, _ | _, None -> True | _, _ -> False;
    op=fun #a #b x y -> match x, y with None, x | x, None -> x;
    one=None
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun x -> True)
})

/// (pcm_t pcm_all_or_none pcm_all_or_none) defines carrier type
///   option a & option b
/// with
///   composable (xa, xb) (ya, yb)
///   = composable xa ya /\ composable xb yb
///   = match (xa, xb), (ya, yb) with
///     | (None, None), _ | _, (None, None)
///     | (Some _, None), (None, Some _)
///     | (None, Some _), (Some _, None) -> True
///     | _ -> False
/// and
///   op (xa, xb) (ya, yb)
///   = (op xa xb, op ya yb)
///   = match (xa, xb), (ya, yb) with
///     | (None, None), z | z, (None, None) -> z
///     | (Some a, None), (None, Some b) -> (Some a, Some b)
///     | (None, Some b), (Some a, None) -> (Some a, Some b)
/// which corresponds directly to the PCM defined in examples/steel/StructUpdate:
///   Both x y = (Some x, Some y)
///   First x = (Some x, None)
///   Second y = (None, Some y)
///   Neither = (None, None)
///
/// Example custom PCM: use
///   fractional a & fractional b
/// for fractional permissions on a struct with fields {a; b},
/// where fractional is as defined in ulib/experimental/Steel.HigherReference.
/// - (xa, xb) and (ya, yb) are composable when the sums of each component's shares are at most 1
/// - The product of (xa, xb) and (ya, yb) is (xa <> ya, xb <> yb), where (<>) merges shares
/// - The unit is (None, None), a struct where one does not have access to either field
