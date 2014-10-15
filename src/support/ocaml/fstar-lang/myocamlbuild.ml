open Ocamlbuild_plugin

let _ = dispatch begin function
   | After_options ->
       Options.ocamlc   := S[!Options.ocamlc  ; A"-rectypes"];
       Options.ocamlopt := S[!Options.ocamlopt; A"-rectypes"];

   | After_rules ->
       (* Numerical warnings *)
       begin
         let wflag error mode wid =
           let mode = match mode with
             | `Enable  -> "+"
             | `Disable -> "-"
             | `Mark    -> "@"
           in
             match error with
             | false -> S[A"-w"; A(Printf.sprintf "%s%d" mode wid)]
             | true  -> S[A"-warn-error"; A(Printf.sprintf "%s%d" mode wid)]
         in
           for i = 1 to 45 do
             flag ["ocaml"; "compile"; Printf.sprintf "warn_+%d" i] & (wflag false `Enable  i);
             flag ["ocaml"; "compile"; Printf.sprintf "warn_-%d" i] & (wflag false `Disable i);
             flag ["ocaml"; "compile"; Printf.sprintf "warn_@%d" i] & (wflag false `Mark    i);
             flag ["ocaml"; "compile"; Printf.sprintf "werr_+%d" i] & (wflag true  `Enable  i);
             flag ["ocaml"; "compile"; Printf.sprintf "werr_-%d" i] & (wflag true  `Disable i);
             flag ["ocaml"; "compile"; Printf.sprintf "werr_@%d" i] & (wflag true  `Mark    i)
           done
       end;

       (* menhir & --explain/--trace/--table *)
       flag ["ocaml"; "parser"; "menhir"; "menhir_explain"] & A"--explain";
       flag ["ocaml"; "parser"; "menhir"; "menhir_trace"  ] & A"--trace";
       flag ["ocaml"; "parser"; "menhir"; "menhir_table"  ] & A"--table";

       (* Threads switches *)
       flag ["ocaml"; "pkg_threads"; "compile"] (S[A "-thread"]);
       flag ["ocaml"; "pkg_threads"; "link"] (S[A "-thread"]);

   | _ -> ()
end
