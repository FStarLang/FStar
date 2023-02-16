module SteelSLDump
open Steel.SLDump

assume val p (idx: string) ([@@@smt_fallback] _ : int) : vprop

assume val inc (#n: int) (idx: string) : SteelT unit (p idx n) (fun _ -> p idx (n + 1))

let test () : SteelT unit (p "foo" 0 `star` p "bar" 18) (fun _ -> p "foo" 3 `star` p "bar" 19) =
  inc "foo";
  sldump "test 1" ();
  inc "foo";
  inc "bar";
  sldump "test 2" ();
  inc "foo";
  return ()
