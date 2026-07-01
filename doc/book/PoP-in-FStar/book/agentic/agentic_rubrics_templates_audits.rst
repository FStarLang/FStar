.. _Agentic_rubrics_templates_audits:

===============================
Rubrics, Templates, and Audits
===============================

As we have already seen from our very simple first example, agents excel when
provided with closed feedback loops, allowing them to repeatedly seek feedback
on partial solutions and iterate until the task is complete. Finding ways to
structure such feedback loops is key to productive agentic programming. Where
feedback is automatable (e.g., program analysis tools), one should do so, but
there will inevitably be steps in which a human has to inspect a proposed
solution and offer some qualitative feedback. We are mostly interested in the
latter, since it is much more open ended. That said, we wil also take every
opportunity to have agents call analysis tools like proof checkers, compilers,
and test frameworks, and there is a large design space to explore for the future
of such tools, geared to towards agentic use.

We offer three principles to structure the communication between humans and
agents. These principles ought to apply to a variety of agentic automation
tasks, though we offer them primarily from our experience with proof-oriented
programming, where we have found them to be effective. The main goal of these
principles is to enable humans to:

* more easily understand and vet agentic output
* steer agents to produce effective solutions
* confirm that provided solutions match their intent

**Rubrics:** Teachers are accustomed to setting *rubrics*, which (from
Merriam-Webster) are "a guide listing specific criteria for grading or scoring
academic papers, projects, or tests". In our context, setting a rubric allows a
human to assess the quality of a agent's proposed solution to a problem. Setting
well-designed rubrics, especially while incorporating insights from the
abstractions used for modular programming and proving, is key to setting strong
feedback loops, and producing outcomes that are easy to assess.

**Templates:** A template (again, from Merriam-Webster) is "something that
establishes or serves as a pattern". Whereas rubrics provide a way for a human
to assess an agent's output, a template is provided by a human to an agent to
hint at the expected solution. Templates are part of a rich area of work in the
AI community on "in-context learning", where an agent learns to solve by a
problem based on examples provided in the prompt. Automated ways to construct
such templates are also often proposed under the banner of *retrieval
augmentation* (RAG). These techniques are very useful, though we focus primarily
on the problem of interactively crafting useful templates with the assistance of
agents.

**Audits:** Ultimately, one needs various ways to confirm that an agentic
authored artifact matches one's expectations. Rubrics serve this purpose, but
there are often aspects of solutions that cannot easily be captured by a rubric.
For such cases, one employs a range of ad hoc auditing techniques, ranging from
old-fashioned code review to testing. We discuss several auditing techniques,
including a new technique for intent confirmation that we call *small
proof-oriented tests* (SPOTs).

We start by illustrating these ideas in the context of a very simple first
example, one that doesn't quite exploit the full power of agentic programming,
but which is instructive anyway.

------------------------
Agentic Proof Automation 
------------------------

A natural first step is to use agents for traditional proof automation. Whereas
automation in various proof frameworks has traditionally employed symbolic proof
search (e.g., using SMT solvers), one can now delegate the entire
construction of a proof (e.g., a lemma body in F*) to an agent.

Going back to our first example from the previous chapter, a task could be
something like the following, including the code snippet below with a prompt to
complete the proof of ``rev_involutive``.

.. code-block:: fstar

    let rec rev_aux (#a: Type) (acc: list a) (l: list a) : Tot (list a) (decreases l) =
        match l with
        | [] -> acc
        | hd :: tl -> rev_aux (hd :: acc) tl

    let rev (#a: Type) (l: list a) : list a = rev_aux [] l

    val rev_involutive (#a: Type) (l: list a) : Lemma (ensures rev (rev l) == l)

*Rubric*: In this case, the rubric is very explicit. We have a fixed statement
of the lemma, and any well-typed definition of ``rev_involutive`` is acceptable,
where judgment against the rubric is fully automated. This is the type of
scenario is the sweet spot for programming with agents in a proof-capable
language.

*Template*: This example is simple enough that a template is not necessary---the
agents have enough background knowledge of F* to solve this problem without
further assistance. However the prompt above itself contains some template-like
information, e.g., the use of ``decreases`` annotation to prove the recursive
functions terminating, etc. However, the template could also include hints about
things surrounding the code, e.g., how to correctly invoke fstar.exe on this
file? Which flags to pass (e.g., ``--report_assumes error`` could make it a hard
error for a solution to use any escape hatch like ``assume`` or ``admit``. etc.)

*Audit*: An audit of the solution would have to judge a few things, e.g., were
any of the deifnitions and signatures above changed by the agent? Did the
agent's invocation of ``fstar.exe`` match the template? Is the definition of
``rev`` the expected one? E.g., can one prove that ``rev [1;2;3] == [3;2;1]``?

While the previous example may seem tiny and perhaps underwhelming, this style
of agentic proof automation is powerful and scales to scenarios well beyond the
small reverse-a-list style problem above. For instance, expert-human authored
rubrics formalized as dependently typed APIs enabled agents to author a `253
commit pull request <https://github.com/project-everest/everparse/pull/291>`_,
changing 100s of files. The dependently typed rubric ensured that the result is
correct. Existing proofs in the repository served as templates for the agent to
build on. And the PR was audited as usual for non-functional properties that are
not captured by the specifications, e.g., by performance benchmarking the
generated C code. 

Setting rubrics for proof automation requires knowing what one wants to prove,
and the expertise to formalize requirements in the notation of a proof
assistant


