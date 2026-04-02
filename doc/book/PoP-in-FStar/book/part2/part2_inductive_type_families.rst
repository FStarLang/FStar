.. _Part2_inductives:

Inductive type definitions
==========================

An inductive type definition, sometimes called a *datatype*, has the
following general structure.

.. math::

   \mathsf{type}~T_1~\overline{(x_1:p_1)} : \overline{y_1:q_1} \rightarrow \mathsf{Type} = \overline{| D_1 : t_1} \\
   \ldots\qquad\qquad\qquad\qquad\\   
   \mathsf{and}~T_n~\overline{(x_n:p_n)} : \overline{y_n:q_n} \rightarrow \mathsf{Type} =  \overline{| D_n : t_n} \\

This defines :math:`n` mutually inductive types, named :math:`T_1 \ldots
T_n`, called the *type constructors*. Each type constructor :math:`T_i`
has a number of *parameters*, the :math:`\overline{x_i : p_i}`, and a
number of *indexes*, the :math:`\overline{y_i:q_i}`.

Each type constructor :math:`T_i` has zero or more *data constructors*
:math:`\overline{D_i:t_i}`. For each data constructor :math:`D_{ij}`, its
type :math:`t_{ij}` must be of the form :math:`\overline{z:s} \rightarrow
T_i~\bar{x_i}~\bar{e}`, i.e., it must be a function type returning an
instance of :math:`T_i` with *the same parameters*
:math:`\overline{x_i}` as in the type constructor's signature, but with
any other well-typed terms :math:`\overline{e}` for the index
arguments. This is the main difference between a parameter and an
index—a parameter of a type constructor *cannot* vary in the result
type of the data constructors, while the indexes can.

Further, in each of the arguments :math:`\overline{z:s}` of the data
constructor, none of the mutually defined type constructors
:math:`\overline{T}` may appear to the left of an arrow. That is, all
occurrences of the type constructors must be *strictly positive*. This
is to ensure that the inductive definitions are well-founded, as
explained below. Without this restriction, it is easy to break
soundness by writing non-terminating functions with ``Tot`` types.

Also related to ensuring logical consistency is the *universe* level
of an inductive type definition. We'll return to that later, once
we've done a few examples.

.. _Part2_strict_positivity:

Strictly positive definitions
+++++++++++++++++++++++++++++

As a strawman, consider embedding a small dynamically typed
programming language within F*. All terms in our language have the
same static type ``dyn``, although at runtime values could have
type ``Bool``, or ``Int``, or ``Function``.

One attempt at representing a language like this using a data type in
F* is as follows:

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: dyn$
   :end-before: //SNIPPET_END: dyn$

The three cases of the data type represent our three kinds of runtime
values: ``Bool b``, ``Int b``, and ``Function f``. The ``Function``
case, however, is problematic: The argument ``f`` is itself a function
from ``dyn -> dyn``, and the constructor ``Function`` allows promoting
a ``dyn -> dyn`` function into the type ``dyn`` itself, e.g., one can
represent the identity function in ``dyn`` as ``Function (fun (x:dyn)
-> x)``. However, the ``Function`` case is problematic: as we will see
below, it allows circular definitions that enable constructing
instances of ``dyn`` without actually providing any base case. F*
rejects the definition of ``dyn``, saying "Inductive type dyn does not
satisfy the strict positivity condition".

Consider again the general shape of an inductive type definition:

.. math::

   \mathsf{type}~T_1~\overline{(x_1:p_1)} : \overline{y_1:q_1} \rightarrow \mathsf{Type} = \overline{| D_1 : t_1} \\
   \ldots\qquad\qquad\qquad\qquad\\   
   \mathsf{and}~T_n~\overline{(x_n:p_n)} : \overline{y_n:q_n} \rightarrow \mathsf{Type} =  \overline{| D_n : t_n} \\

This definition is strictly positive when

 * for every type constructor :math:`T \in T_1, ..., T_n`,

 * and every data constructor :math:`D : t \in \overline{D_1},
   ... \overline{D_n}`, where `t` is of the form
   :math:`x0:s_0 \rightarrow ...  \rightarrow xn:s_n  \rightarrow T_i ...`,
   and :math:`s_0, ..., s_n` are the types of the fields of :math:`D`

 * and for all instantiations :math:`\overline{v}` of the type parameters
   :math:`\overline{p}` of the type :math:`T`,

 * :math:`T` does not appear to the left of any arrow in any
   :math:`s \in (s_0, ..., s_k)[\overline{v}/\overline{p}]`.

Our type ``dyn`` violates this condition, since the defined typed
``dyn`` appears to the left of an arrow type in the ``dyn ->
dyn``-typed field of the ``Function`` constructor.

To see what goes wrong if F* were to accept this definition, we can
suppress the error reported by using the option ``__no_positivity``
and see what happens.

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: nopos_dyn$
   :end-before: //SNIPPET_END: nopos_dyn$

.. note::

   F* maintains an internal stack of command line options. The
   ``#push-options`` pragma pushes additional options at the top of
   the stack, while ``#pop-options`` pops the stack. The pattern used
   here instructs F* to typecheck ``dyn`` only with the
   ``__no_positivity`` option enabled. As we will see, the
   ``__no_positivity`` option can be used to break soundness, so use
   it only if you really know what you're doing.

Now, having declared that ``dyn`` is a well-formed inductive type,
despite not being strictly positive, we can break the soundness of
F*. In particular, we can write terms and claim they are total, when
in fact their execution will loop forever.

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: nopos_dyn_loop$
   :end-before: //SNIPPET_END: nopos_dyn_loop$

Here, the type of ``loop`` claims that it is a term that always
evaluates in a finite number of steps to a value of type ``dyn``. Yet,
reducing it produces an infinite chain of calls to ``loop'
(Function loop')``. Admitting a non-positive definition like ``dyn``
has allowed us to build a non-terminating loop.

Such loops can also allow one to prove ``False`` (breaking soundness),
as the next example shows.

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: non_positive$
   :end-before: //SNIPPET_END: non_positive$

This example is very similar to ``dyn``, except ``NP`` stores a
non-positive function that returns ``False``, which allows use to
prove ``ff : False``, i.e., in this example, not only does the
violation of strict positivity lead to an infinite loop at runtime, it
also renders the entire proof system of F* useless, since one can
prove ``False``.

Finally, in the example below, although the type ``also_non_pos`` does
not syntactically appear to the left of an arrow in a field of the
``ANP`` constructor, an instantiation of the type parameter ``f``
(e.g., with the type ``f_false``) does make it appear to the left of
an arrow---so this type too is deemed not strictly positive, and can be used
to prove ``False``.

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: also_non_positive$
   :end-before: //SNIPPET_END: also_non_positive$

We hope you are convinced that non-strictly positive types should not
be admissible in inductive type definitions. In what follows, we will
no longer use the ``__no_positivity`` option. In a later section, once
we've introduced the *effect of divergence*, we will see that
non-positive definitions can safely be used in a context where
programs are not expected to terminate, allowing one to safely model
things like the ``dyn`` type, without compromising the soundness of
F*.

.. _Part2_strictly_positive_annotations:

Strictly Positive Annotations
-----------------------------

Sometimes it is useful to parameterize an inductive definition with a
type function, without introducing a non-positive definition as we did
in ``also_non_pos`` above.

For example, the definition below introduces a type ``free f a``, a 
form of a tree whose leaf nodes contain ``a`` values, and whose
internal nodes branch according the type function ``f``. 

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: free$
   :end-before: //SNIPPET_END: free$

We can instantiate this generic ``free`` to produce various kinds of
trees. Note: when instantiating ``free list a`` in
``variable_branching_list`` below, we need to explicitly re-define the
``list`` type with a strict-positivity annotation: F* does not
correctly support rechecking type constructors to prove that they are
strictly positive when they are used at higher order.

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: free_instances$
   :end-before: //SNIPPET_END: free_instances$

However, we should only be allowed to instantate ``f`` with type
functions that are strictly positive in their argument, since otherwise
we can build a proof of ``False``, as we did with
``also_non_pos``. The ``@@@strictly_positive`` attribute on the
formal parameter of ``f`` enforces this.

If we were to try to instantiate ``free`` with a non-strictly positive
type function, 

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: free_bad$
   :end-before: //SNIPPET_END: free_bad$

then F* raises an error:

.. code-block::

    Binder (t: Type) is marked strictly positive, but its use in the definition is not
   
Unused Annotations
------------------

Sometimes one indexes a type by another type, though the index has no
semantic meaning. For example, in several F* developments that model
mutable state, the a heap reference is just a natural number modeling
its address in the heap. However, one might use the type ``let ref
(a:Type) = nat`` to represent the type of a reference, even though the
type ``a`` is not used in the definition. In such cases, it can be
useful to mark the parameter as unused, to inform F*'s positivity
checker that the type index is actually irrelevant. The snippet below
shows an example:

.. literalinclude:: ../code/Part2.Positivity.fst
   :language: fstar
   :start-after: //SNIPPET_START: unused$
   :end-before: //SNIPPET_END: unused$

Here, we've marked the parameter of ``ref`` with the ``unused``
attribute. We've also marked ``ref`` as ``irreducible`` just to
ensure for this example that F* does not silently unfold the
definition of ``ref``.

Now, knowing that the parameter of ``ref`` is unused, one can define
types like ``linked_list a``, where although ``linked_list a`` appears
as an argument to the ``ref`` type, the positivity checker accepts it,
since the parameter is unused. This is similar to the use of a
``strictly_positive`` annotation on a parameter.

However, with the ``unused`` attribute, one can go further: e.g., the
type ``neg_unused`` shows that even a negative occurrence of the
defined type is accepted, so long as it appears only as an
instantiation of an unused parameter.
