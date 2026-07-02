.. _PartPulse:

##################################
Agentic Proof-Oriented Programming
##################################

AI-based automation of formal proofs has received a lot of attention
in the past few years, with lots of promise but few real successes. However, 
starting in late 2025, with the availability of models such as Claude Opus 4.5 and GPT-5.2 (and beyond), 
and especially their integration within agentic coding environments such as Claude Code,
OpenAI Codex, and GitHub Copilot CLI, the promise of AI automation for proofs has largely
become a reality. It is now possible to have agents author hundreds of thousands
of lines of programs and proofs, including in F* and Pulse, but also in other
proof assistants including Lean, Coq, Verus, Dafny, and others.

For example, in a series of `blog posts <https://risemsr.github.io/blog>`_ we have reported on 
our ability to use AI agents to automatically formalize the classic "CLRS"
`Introduction to Algorithms <https://en.wikipedia.org/wiki/Introduction_to_Algorithms>`_ 
textbook in F* and Pulse, in just a few weeks of agentic coding.
Beyond just textbook algorithms, we have also been able to use agents to build a
formally `verified generational garbage collector for OCaml <https://github.com/FStarLang/pulse-verified-gc>`_
with proofs of correctness comprising more than 100,000 lines of F* and Pulse, authored
entirely by agents. The resulting verified, executable C code can be used as a 
drop-in replacement for the OCaml 4.14.0 garbage collector, and has been tested to work with
the OCaml 4.14.0 compiler and runtime system.
Going further, we have also been able to use agents to build a verified implementation of
the `TLS-1.3 protocol <https://github.com/project-everest/mitls-fstar/tree/agentic>`_, 
with implementation and proofs again exceeding 100,000 lines of F* and Pulse.
The resulting C code interoperates with OpenSSL to negotiate TLS connections and
send application traffic.
Others have reported similar successes, using agents to formalize proofs of `programming 
language metatheory <https://proofsandintuitions.net/2026/03/18/move-borrow-checker-lean/>`_, 
parts of `verified compilers <https://zoep.github.io/blog/2026/04/17/machine-generated-code-machine-checked-proofs/>`_, 
or porting `C code into Lean with proofs of correctness <https://github.com/kim-em/lean-zip>`_.

That said, agentic proof-oriented programming is an extremely new paradigm, the agents are evolving
rapidly and there are many open questions about how best to structure interactions between humans
and agents to achieve the best results. What is clear is that agents can produce software artifacts
at a scale which, if not structured correctly, can far exceed the ability of humans to review and validate
the results. The promise of proof-oriented programming in this context is that proof checkers like F*
can be used to ensures that the software matches a formal specification, but one still has to be able
to carefully check  that what is proven matches what is intended.

In this part of the book, we offer a few principles and techniques for agentic
proof-oriented programming. Thankfully, a lot of what we've come to know as good
proof-engineering practice still applies. Our main message is that humans need
to think carefully about the right abstractions for designing a system so that
agents are effective at producing proof-oriented software, and, perhaps more
importanly, that humans are able to understand the results.


.. toctree::
   :maxdepth: 1
   :caption: Contents:

   agentic_getting_started
   agentic_rubrics_templates_audits
   agentic_sorting_algorithms
   agentic_rubrics_as_templates
   agentic_state_machines
   agentic_tls
