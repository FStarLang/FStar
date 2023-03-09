F*: A Proof-oriented Programming Language
=========================================

### F\* website

More information on F\* can be found at www.fstar-lang.org

### Installation

See [INSTALL.md](https://github.com/FStarLang/FStar/blob/master/INSTALL.md)

### Online book

An online book _Proof-oriented Programming In F*_ is in the works and regular updates are
posted online. The book is available as a [PDF], or you can read it while trying out
examples and exercises in your browser interface from this [tutorial page].

[tutorial page]: https://www.fstar-lang.org/tutorial/
[PDF]: http://fstar-lang.org/tutorial/proof-oriented-programming-in-fstar.pdf

### Wiki

The [F\* wiki] contains additional technical documentation on F\*, and is especially useful
for topics that are not yet covered by the book.

[F\* wiki]: https://github.com/FStarLang/FStar/wiki

### Editing F* code

You can edit F\* code using various text editor. Emacs has the best support currently,
providing syntax highlighting, code completion and navigation, and interactive development,
using [fstar-mode.el]. However, other editors also have limited support.
More details on [editor support] are available on the [F\* wiki].

[editor support]: https://github.com/FStarLang/FStar/wiki/Editor-support-for-F*
[fstar-mode.el]: https://github.com/FStarLang/fstar-mode.el

### Extracting and executing F* code

By default F* only verifies the input code, it does not compile or execute it.
To execute F* code one needs to translate it for instance to OCaml or F\#,
using F\*'s code extraction facility---this is invoked using the
command line argument `--codegen OCaml` or `--codegen FSharp`.
More details on [executing F\* code via OCaml] on the [F\* wiki].

[executing F\* code via OCaml]: https://github.com/FStarLang/FStar/wiki/Executing-F*-code

Also, code written in a C-like shallowly embedded DSL can be extracted to
[C](https://arxiv.org/abs/1703.00053)
or [WASM](https://doi.ieeecomputersociety.org/10.1109/SP.2019.00064)
by the [KaRaMeL tool](https://github.com/FStarLang/karamel),
and code written in an ASM-like deeply embedded DSL can be extracted
to ASM by the [Vale tool](https://github.com/project-everest/vale).

### Chatting about F* on Slack and Zulip

The F* developers and many users interact on this [Slack
forum](https://everestexpedition.slack.com)---you should be able to
join automatically by [clicking
here](https://aka.ms/JoinEverestSlack),
but if that doesn't work, please contact the mailing list mentioned
below.

Users can also chat about F* or ask questions at this [Zulip
forum](https://fstar.zulipchat.com).

### Mailing list

We also have a [mailing list] which we use mainly for announcements. 

[mailing list]: https://groups.google.com/g/fstar-mailing-list

### Reporting issues

Please report issues using the [F\* issue tracker] on GitHub.
Before filing please search to make sure the issue doesn't already exist.
We don't maintain old releases, so if possible please use the
[online F\* editor] or directly [the GitHub sources] to check
that your problem still exists on the `master` branch.

[F\* issue tracker]: https://github.com/FStarLang/FStar/issues
[online F\* editor]: https://www.fstar-lang.org/run.php
[the GitHub sources]: [https://github.com/FStarLang/FStar/blob/master/INSTALL.md#building-f-from-sources

### Contributing

See [CONTRIBUTING.md](https://github.com/FStarLang/FStar/blob/master/CONTRIBUTING.md)

### License

F* is released under the [Apache 2.0 license]; for more details
see [LICENSE](https://github.com/FStarLang/FStar/blob/master/LICENSE)

[Apache 2.0 license]: https://www.apache.org/licenses/LICENSE-2.0
