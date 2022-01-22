Inductive type definitions
==========================

An inductive type definition, sometimes called a *datatype*, has the
following general structure.

.. math::

   \mathsf{type}~T₁~\overline{(x₁:p₁)} : \overline{y₁:q₁} → \mathsf{Type} = \overline{| D₁ : t₁} \\
   \mathsf{and}~Tₙ~\overline{(xₙ:pₙ)} : \overline{yₙ:qₙ} → \mathsf{Type} =  \overline{| Dₙ : tₙ} \\

This defines :math:`n` mutually inductive types, named :math:`T₁ …
Tₙ`, called the *type constructors*. Each type constructor :math:`Tᵢ`
has a number of *parameters*, the :math:`\overline{xᵢ : pᵢ}`, and a
number of *indexes*, the :math:`\overline{yᵢ:qᵢ}`.

Each type constructor :math:`Tᵢ` has zero or more *data constructors*
:math:`\overline{Dᵢ:tᵢ}`. For each data constructor :math:`Dᵢⱼ`, its
type :math:`tᵢⱼ` must be of the form :math:`\overline{z:s} →
Tᵢ~\bar{xᵢ}~\bar{e}`, i.e., it must be a function type returning an
instance of :math:`Tᵢ` with *the same parameters*
:math:`\overline{xᵢ}` as in the type constructor's signature, but with
any other well-typed terms :math:`\overline{e}` for the index
arguments. This is the main difference between a parameter and an
index—a parameter of a type constructor *cannot* vary in the result
type of the data constructors, while the indexes can.

Further, in each of the arguments :math:`\overline{z:s}` of the data
constructor, none of the mutually defined type constructors
:math:`\overline{T}` may appear to the left of an arrow. That is, all
occurrences of the type constructors must be *strictly positive*. This
is to ensure that the inductive definitions are well-founded. As we
will see shortly, without this restriction, it is easy to break
soundness by writing non-terminating functions with ``Tot`` types.

Also related to ensuring logical consistency is the *universe* level
of an inductive type definition. We'll return to that later, once
we've done a few examples.
