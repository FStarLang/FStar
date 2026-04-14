.. The main file for the F* manual
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

..
   developed at `Microsoft Research
   <http://research.microsoft.com/en-us>`_, `MSR-Inria
   <http://www.msr-inria.fr/>`_, and `Inria <https://www.inria.fr/>`_.

   
.. role:: smt2(code)
   :language: smt2

Proof-oriented Programming in F*
================================


F* is a dependently typed programming language and proof
assistant. This book describes how to use F* for *proof-oriented
programming*, a paradigm in which one co-designs programs and proofs
to provide mathematical guarantees about various aspects of a
program's behavior, including properties like functional correctness
(precisely characterizing the input/output behavior of a program),
security properties (e.g., ensuring that a program never leaks certain
secrets), and bounds on resource usage.

Although a functional programming language at its core, F* promotes
programming in a variety of paradigms, including programming with
pure, total functions, low-level programming in imperative languages
like C and assembly, concurrent programming with shared memory and
message-passing, and distributed programming. Built on top of F*'s
expressive, dependently typed core logic, no matter which paradigm you
choose, proof-oriented programming in F* enables constructing programs
with proofs that they behave as intended.

**A note on authorship**: Many people have contributed to the
development of F* over the past decade. Many parts of this book too
are based on research papers, libraries, code samples, and language
features co-authored with several other people. However, the
presentation here, including especially any errors or oversights, are
due to the authors. That said, contributions are most welcome and we
hope this book will soon include chapters authored by others.


   
.. toctree::
   :maxdepth: 2
   :caption: Contents:

   structure
   intro
   part1/part1
   part2/part2
   part3/part3
   part4/part4
   part5/part5
   pulse/pulse
   under_the_hood/under_the_hood
