(* If FSTAR_MEM_REPORT is set, register an at_exit handler that writes
   the peak OCaml heap size (in bytes) to the given file path. This
   reports F*-only memory excluding Z3 subprocesses, which makes
   memory benchmarks more deterministic. *)
let setup () =
  match Sys.getenv_opt "FSTAR_MEM_REPORT" with
  | Some fn ->
    at_exit (fun () ->
      try
        let stat = Gc.quick_stat () in
        let peak_bytes = stat.Gc.top_heap_words * (Sys.word_size / 8) in
        let oc = open_out fn in
        Printf.fprintf oc "fstar.mempeak %d\n" peak_bytes;
        close_out oc
      with _ -> ()
    )
  | None -> ()
