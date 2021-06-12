module Arrays

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
open Steel.CStdInt

/// Some examples using Steel arrays

let access ()
  : SteelT unit emp (fun _ -> emp)
  = let r = malloc 0ul (mk_size_t 2ul) in
    if is_null r _
    then begin
      noop ();
      assert_null r _
    end else begin
      assert_not_null r _;
      let x = index r (mk_size_t 0ul) in
      upd r (mk_size_t 0ul) x;
      free r
    end
