.. _Agentic_getting_started:

================
Getting Started
================

Getting started is easy.

1. Install the latest version of F* and Pulse by doing

    .. code-block:: bash
    
        curl -fsSL https://aka.ms/install-fstar | bash -s -- --release

It installs in ~/.local/bin/fstar.exe, by default.

2. Install a coding agent of your choice, e.g., GitHub Copilot CLI, Clause Code
   etc. For example:

    .. code-block:: bash
    
        npm install -g @github/copilot

We'll base most of what follows on GitHub Copilot CLI, but the same thing should
apply to other agents.

3. You'll need a way to authenticate with GitHub to use Copilot CLI. The easiest
   way is to create a personal access token (PAT) on GitHub, and then set it in
   your environment. For example, you can add the following line to your
   ~/.bashrc file:

    .. code-block:: bash
    
        export COPILOT_GITHUB_TOKEN="your_personal_access_token_here"

At this point, you should be able to launch copilot and in chat session say something like:

    .. code-block:: text
    
        Write a pure F* function to reverse a list and prove that it is involutive.
        Write it in RevSample.fst and use fstar.exe to check that it verifies correctly.

A run that I did cost around $0.33 with Claude Sonnet 4.6, producing a 43 line
file with an implementation of ``rev`` and its proof.

.. code-block:: fstar

    module RevSample

    open FStar.List.Tot

    let rec rev_aux (#a: Type) (acc: list a) (l: list a) : Tot (list a) (decreases l) =
    match l with
    | [] -> acc
    | hd :: tl -> rev_aux (hd :: acc) tl

    let rev (#a: Type) (l: list a) : list a =
    rev_aux [] l

    (* Lemma: rev_aux acc l == (rev_aux [] l) @ acc *)
    let rec rev_aux_append (#a: Type) (acc: list a) (l: list a)
    : Lemma (ensures rev_aux acc l == rev_aux [] l @ acc) (decreases l)
    = match l with
    | [] -> ()
    | hd :: tl ->
        rev_aux_append (hd :: acc) tl;
        rev_aux_append [hd] tl;
        append_assoc (rev_aux [] tl) [hd] acc

    (* Lemma: rev (l1 @ l2) == rev l2 @ rev l1 *)
    let rec rev_append (#a: Type) (l1 l2: list a)
    : Lemma (ensures rev (l1 @ l2) == rev l2 @ rev l1) (decreases l1)
    = match l1 with
    | [] -> ()
    | hd :: tl ->
        rev_append tl l2;
        rev_aux_append [hd] (tl @ l2);
        rev_aux_append [hd] tl;
        append_assoc (rev l2) (rev tl) [hd]

    (* Main theorem: rev (rev l) == l *)
    let rec rev_involutive (#a: Type) (l: list a)
    : Lemma (ensures rev (rev l) == l) (decreases l)
    = match l with
    | [] -> ()
    | hd :: tl ->
        rev_involutive tl;
        rev_aux_append [hd] tl;
        rev_append (rev tl) [hd];
        assert (rev [hd] == [hd])

4. Optionally, one can install the `FStarLang/proof-copilot
   <https://github.com/FStarLang/proof-copilot#installation>`_ plugin. It
   contains various tips and tricks for agents to use F*, Pulse, KaRaMeL, Z3,
   and related tools. We will cover 


This example is very simple---a version of it even appears in `a previous
chapter <_Part1_intrinsic_extrinsic>`_ of this book. But, even on this example
you can see how things work. 

* Agents start with a few steps of "thinking"---natural language output that
  describes the approach to solving the problem

* Various tool calls, to read files, write files, call fstar.exe etc. (which
  need to be authorized)

* Feedback from the tool calls (e.g., error messages from failed verification
  runs), followed by attempts to fix it.

* And, eventually, after several rounds, a solution that is declared complete.

Despite being very simple, this example already raises several interesting
questions. On the one hand, that agents can automate so much is incredibly
exciting, and we have many questions around the scale of program proofs one
might attempt today with agentic automation. But, there are also some
significant challenges to address, some technical, some societal---we outline
just a few of them below.

**Intent Confirmation**: How is one to judge whether or not the task is actually
completed? In this case, we have a function called ``rev`` and a lemma
``rev_involutive`` proving that ``rev (rev l) == l``. Does this ``rev`` function
really reverse a list? And is ``rev (rev l) == l`` the involution that we had in
mind? Answering such questions effectively is perhaps the central question in
agentic programming.

**Agent Direction**: For this simple problem, we didn't need to say much. The
background knowledge of the agents was sufficient to solve the problem (likely a
version of the solution appears in the pre-training data in many forms). But,
for more complex problems, what form of assistance should one provide to the
agent to help it complete a task more effectively, e.g., with fewer attempts,
consuming fewer tokens, or producing a higher quality results that is more
likely to match a user's intent.

**Access Inequalities**: It cost me $0.33 cents to do this one example. As we do
more interesting examples, we'll start to rack up bigger bills. Not everyone has
access to such resources, and if state-of-the-art programming and proving is
gated by access to the most powerful and expensive models, this is a very
significant issue.

**Environmental Resources**: The computing resources used to train models and
serve agents is substantial. The actual impact of this resource consumption is
hard to assess properly, with many conflicting reports, but what is clear is
that if the pace of agentic AI adoption increases as expected, the resource
consumption will grow to be a substantial problem, unless better energy and
cooling technologies are developed.

**Pedagogical Issues**: With many programming and proving tasks now
substantially automatable, how will we teach the next generation these skills?
Will these skills even be necessary in the future? 

Of course, there are many more questions, spanning areas from labor issues to
cognition and psychology. We will not attempt to address most of these issues,
and instead focus primarily on the questions of *intent confirmation* and *agent
direction*, while providing the beginnings of a *pedagogy* of agentic
programming. These are the beginnings of a what we believe is a new paradigm in
which agents and proof-oriented architects work closely together to build
verified systems.