# Steel Supplementary Material

This material contains the Steel framework presented in the _Steel: Proof-oriented
Programming in a Dependently Typed Concurrent Separation Logic_ ICFP 21 paper.

All the development is done within the F\* proof assistant, which relies on the Z3 theorem prover
for semi-automated proofs.
This artifact contains a snapshot of the full F\* repository at the time of submission.
All files relevant to Steel can be found in the FStar/ulib/experimental and in the
FStar/examples/steel folders.
All other files are part of the F\* compiler and standard library, are irrelevant for this artifact.

# Building the F\* compiler

If you are using the provided VM, F\* is already installed and this section can be skipped. 

Setting up a local environment requires a working OCaml setup with OPAM.
Installation instructions for OPAM are available [here](http://opam.ocaml.org/doc/Install.html).
OCaml version from 4.04.0 to 4.12.X should work.

F\* depends on a bunch of external packages which you should install using OPAM:

```sh
$ opam install ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir sedlex ppx_deriving ppx_deriving_yojson process ppxlib=0.22.0
```

**Note:** Some of these opam packages depend on binary packages that you need to install locally
(eg, using your Linux package manager). So if the command above gives you errors like this:
```sh
[ERROR] The compilation of conf-gmp failed at "./test-win.sh".
```
You can use `depext` to install the missing binary packages, for instance:
```sh
$ opam depext -i conf-gmp
```

You will also need a particular version of Z3, namely, Z3 4.8.5.
If your system is supported, we strongly recommend using a binary available here:
https://github.com/FStarLang/binaries/tree/master/z3-tested
Make sure to add the Z3 executable to your PATH.

Once the previous steps are done, you can now build the F\* compiler by running `make 1 -j6`
from the top-level of the FStar folder.
The number after the -j option indicates how many cores to use for compilation.
You should adjust this number based on your CPU.

# Browsing the files

We recommend browsing the files using Emacs and fstar-mode, which can be installed through MELPA,
which we installed in the provided VM.

A full documentation for fstar-mode is available [here](https://github.com/FStarLang/fstar-mode.el).
For browsing F\* sources, the most useful keybindings are C-c C-n to verify the next paragraph,
and C-c RET which asks F\* to verify everything up to the current point.

# Reverifying the Steel development

To verify the Steel development, run `make -j6` from the top-level of the FStar folder,
followed by `make -j6` from the FStar/examples/steel folder.
The first command also reverifies the F\* standard library, there currently is no way
to only verify the Steel development.
Verifying the F\* standard library might print warnings; they can be safely ignored.
The entire Steel framework and examples, and the F\* standard library takes between
15 and 30 minutes to verify on an Intel i7 laptop with 4 cores.

The entire development has already been verified inside the provided VM.
To reverify the entire development, first run `make clean` before running the steps above.
You can also verify a single file, for instance Steel.Effect.fsti,
by running `fstar.exe Steel.Effect.fsti` from the command line.

# Organization of the Steel development

F\*, similarly to OCaml and F\#, distinguishes between interface files (`.fsti`) and implementation
files (`.fst`). For each module name mentioned later, you can loot at the corresponding
implementation and/or interface files. When an interface file exists for a given module,
the implementation file is hidden from clients of the module, and as such, is often less documented.

The various pragmas introduced by `#` are used to pass certain options to F\*, mostly controlling
the SMT encoding and the behavior of Z3.

The semantics and memory model of Steel are previous work inherited from SteelCore, which
the Steel framework builds upon. These files can be found in ulib/experimental, and include
`Steel.Semantics.Hoare.MST`, `Steel.Semantics.Instantiate`, `Steel.Heap`,
`Steel.FractionalPermission`, `Steel.Preorder`, and `Steel.Memory`.

The calculus presented in section 3 corresponds to the effect in `Steel.Effect.fsti`,
found in the ulib/experimental folder.
The implementation, in `Steel.Effect.fst`, ensures the soundness of the effects w.r.t.
the SteelCore semantics.
The atomic and ghost versions mentioned at the end of Section 3.4 are available
in module `Steel.Effect.Atomic`.
For presentation purposes, the paper presents in Section 3.1 the precondition R as having
type `fppred p = type_of p -> prop`, where type_of p might be a tuple if p is for instance
the separation logic predicate `p1 * p2`. For convenience, our implementation defines
`fppred = rmem p -> prop`, where `rmem p` is a function that takes as argument a subresource
of the separation logic predicate `p`, and returns its selector. This simplifies defining
accessors for extracting the selector of a given subresource out of `type_of p`.

The decision procedure presented in Section 4 can be found in `Steel.Effect.Common.fsti`, inside
of the ulib/experimental folder. The entry point of this decision procedure is the function
`init_resolve_tac`, which can be found almost at the very bottom of the file.

Module `Steel.PCMReference` provides a user-facing interface to the core Steel
PCM-based memory model. Modules `Steel.HigherReference` and `Steel.Reference` specialize
this library to use a standard fractional permission PCM. `Steel.MonotonicHigherReference`
is a variant of `Steel.HigherReference` exploring the relation between PCMs and preorders.
`Steel.Array` provides a small library for Steel arrays.

The `swap` example presented in the introduction can be found in the `Selectors.Examples` module,
inside of the examples/steel folder.

The reimplementations of SteelCore libraries presented in Section 5.1 correspond to the modules
`Steel.SpinLock`, `Steel.ForkJoin`, and `Steel.Channel.Simplex` inside the ulib/experimental
folder. We also include the original SteelCore implementations we compared against in
examples/steel/steelcore, with the same module names but the `fst(i)_old` extensions.
Note that these implementations do not verify anymore, as they correspond to an earlier
version of the Steel framework. We only include them for historical purposes.

The core definitions for the balanced trees library using selectors from Section 5.2
can be found in `Selectors.Tree.Core`, inside the examples/steel folder. Functions building
upon the core definitions, such as `height` or `insert_avl`, can be found in `Selectors.Tree`.
The examples/steel folder also contains other, similar verified Steel libraries using selectors.
In particular, `Selectors.LList` contains the core definitions of a linked list selector while
`Selectors.LList.Derived` provides basic linked list functions. 
`Selectors.PtrLList` provides a library of linked lists themselves containing pointers to values,
while `Selectors.LList2` is a more recent version of `Selectors.LList`, using combinators to simplify
proving that the user-defined selectors are self-framing.

The library of Disposable invariants from Section 5.3 is available in `Steel.DisposableInvariant`,
inside the ulib/experimental folder.

The Owicki-Gries counter implementation presented in Section 5.4 is available in `OWGCounterInv`,
inside the examples/steel folder. A variant using locks instead of using invariants is available
in the same folder, in the `OWGCounter` module.

Our development for Michael-Scott 2-Lock queues is available in the examples/steel folder, inside
the TwoLockQueue module. It relies on a Steel library for low-level queues, referred to as `Q` in
the paper, which is available in the `Queue` module inside the same folder.

Finally, our library for 2-party session types modeled using a PCM can be found in the `Duplex.PCM`
module, inside of the `examples/steel` folder. A simple protocol using this library can be found
in the same folder, in the `Duplex.PingPong` module.
A simpler version of this library, specialized to a simple Stepper protocol, can be found
in the `Steel.Stepper` module, inside ulib/examples.

# Known IDE issues

There currently are some known issues when using Emacs and fstar-mode with Steel, detailed below.
These issues do not impact our verification guarantees; this can always be confirmed by verifying
a given file from the command-line, instead of inside the IDE.

- Some features of Emacs cause F\* to crash when typechecking Steel files.
  Most Steel files disable these features through the line `#set-options "--ide_id_info_off`.
  See for instance line 28 of `Steel.Effect.Common.fsti`.
  If F\* crashes when browsing Steel files, and this option is not currently in the opened file,
  try to add it at the top, just below the open directives.

- Emacs occasionnally reports that F\* could not infer some implicits, underlining them in red
  in the file. As long as interactive verification succeeds (by using the C-c C-n keybinding
  previously described for instance), these errors are incorrectly reported by the IDE.
