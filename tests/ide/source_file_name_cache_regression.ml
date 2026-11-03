let expect label expected actual =
  if actual <> expected then
    failwith (Printf.sprintf "%s: expected %S, got %S" label expected actual)

let () =
  let root = Sys.argv.(1) in
  let nested_root = Filename.concat root "a" in
  let source = Filename.concat nested_root "b/c.fst" in
  let sibling_source = Filename.concat root "ab/c.fst" in
  FStarC_Find.set_no_default_includes true;
  FStarC_Find.set_file_list [];
  FStarC_Find.set_include_path [root];
  expect "first" "a/b/c.fst" (FStarC_Find.source_file_name source);
  expect "cached" "a/b/c.fst" (FStarC_Find.source_file_name source);
  FStarC_Find.set_include_path [root; nested_root];
  expect "longest overlapping root" "b/c.fst"
    (FStarC_Find.source_file_name source);
  FStarC_Find.set_include_path [nested_root];
  expect "include invalidation" "b/c.fst"
    (FStarC_Find.source_file_name source);
  expect "path boundary" "c.fst"
    (FStarC_Find.source_file_name sibling_source);
  expect "unresolved dot fallback" "."
    (FStarC_Find.source_file_name
      (Filename.concat root "absent/."));
  expect "unresolved dotdot fallback" ".."
    (FStarC_Find.source_file_name
      (Filename.concat root "absent/.."));
  FStarC_Find.set_include_path [];
  FStarC_Find.set_file_list [source];
  expect "file-list invalidation" "c.fst"
    (FStarC_Find.source_file_name source);
  FStarC_Find.set_file_list [];
  FStarC_Find.set_include_path [root];
  expect "restored" "a/b/c.fst" (FStarC_Find.source_file_name source);
  print_endline "source_file_name cache regression: ok"
