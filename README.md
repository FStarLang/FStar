F*: Verification system for effectful programs
==============================================

### F\* website

More information on F\* can be found at www.fstar-lang.org

### Installation

See [INSTALL.md](https://github.com/FStarLang/FStar/blob/master/INSTALL.md)

### Tutorial

The [F\* tutorial] provides a first taste of verified programming in
F\*, explaining things by example.

[F\* tutorial]: https://www.fstar-lang.org/tutorial/

### Wiki

The [F\* wiki] contains additional, usually more in-depth, technical
documentation on F\*.

[F\* wiki]: https://github.com/FStarLang/FStar/wiki

### Editing F* code

You can edit F\* code using your favourite text editor, but Emacs,
Atom, and Vim have extensions that add special support for F\*,
including syntax highlighting and interactive development. More
details on [editor support] on the [F\* wiki].

[editor support]: https://github.com/FStarLang/FStar/wiki/Editor-support-for-F*

You can also edit simple examples directly in your browser by using
either the [online F\* editor] that's part of the [F\* tutorial] or our
new [even cooler online editor] (experimental).

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial
[even cooler online editor]: http://fstar.ht.vc

### Extracting and executing F* code

By default F* only verifies the input code, it does not compile or execute it.
To execute F* code one needs to translate it for instance to OCaml or F\#,
using F\*'s code extraction facility---this is invoked using the
command line argument `--codegen OCaml` or `--codegen FSharp`.
More details on [executing F\* code via OCaml] on the [F\* wiki].

[executing F\* code via OCaml]: https://github.com/FStarLang/FStar/wiki/Executing-F*-code

Also, code written in a C-like shalowly embedded DSL can be extracted to
[C](https://arxiv.org/abs/1703.00053)
or [WASM](https://doi.ieeecomputersociety.org/10.1109/SP.2019.00064)
by the [KreMLin tool](https://github.com/FStarLang/kremlin),
and code written in an ASM-like deeply embedded DSL can be extracted
to ASM by the [Vale tool](https://github.com/project-everest/vale).

### Chatting about F* on Zulip

Users can chat about F* or ask questions at https://fstar.zulipchat.com
([Zulip](https://zulipchat.com) is a good open source alternative to Slack)

### Community mailing list

The [fstar-club mailing list] is where
various F* announcements are made to the general public (e.g. for
releases, new papers, etc) and where users can ask questions, ask for
help, discuss, provide feedback, announce jobs requiring at least 10
years of F* experience, etc.

[List archives] are public and [searchable], but only members can post.
[Join here][fstar-club mailing list]!

[fstar-club mailing list]: http://lists.gforge.inria.fr/mailman/listinfo/fstar-club

[List archives]: https://lists.gforge.inria.fr/pipermail/fstar-club/
[searchable]: https://mail-archive.com/fstar-club@lists.gforge.inria.fr/

### Blog

The [F\* for the masses] blog is also expected to become an important
source of information and news on the F\* project.

[F\* for the masses]: https://fstarlang.github.io/

### Reporting issues

Please report issues using the [F\* issue tracker] on GitHub.
Before filing please use search to make sure the issue doesn't already exist.
We don't maintain old releases, so if possible please use the
[online F\* editor] or directly [the GitHub sources] to check
that your problem still exists on the `master` branch.

[F\* issue tracker]: https://github.com/FStarLang/FStar/issues
[online F\* editor]: https://www.fstar-lang.org/run.php
[the GitHub sources]: [https://github.com/FStarLang/FStar/blob/master/INSTALL.md#building-f-from-sources

### Contributing

See [CONTRIBUTIONS.md](https://github.com/FStarLang/FStar/blob/master/CONTRIBUTIONS.md)

### License

This new variant of F* is released under the [Apache 2.0 license];
see `LICENSE` for more details.

[Apache 2.0 license]: https://www.apache.org/licenses/LICENSE-2.0

### Towards F* version 1.0

This is a new variant of F* (carrying version 0.9.x) that is still in
development and we hope will eventually lead to a 1.0 release. This
new variant is incompatible and quite different compared to the
previously released [0.7 versions and earlier].

[0.7 versions and earlier]: https://github.com/FStarLang/FStar#old-f-versions-v071-and-earlier

### Old F* versions (v0.7.1 and earlier) ###

[F\* v0.7.1] and earlier are no longer maintained, so please do not
create any issues here about those versions.

[F\* v0.7.1]: https://github.com/FStarLang/FStar/blob/stratified_last/.old/fstar-0.7.1-alpha.zip?raw=true
