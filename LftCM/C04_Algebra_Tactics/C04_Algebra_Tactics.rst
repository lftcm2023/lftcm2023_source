.. _algebra_tactics:

Algebraic computations in Lean
==============================

This is a tutorial on doing proofs with a computational flavour using the
`mathlib4 <https://github.com/leanprover-community/mathlib4>`_ library for the
`Lean 4 <https://leanprover.github.io/>`_ proof assistant.

The phrase "computational flavour" might need some explanation. These are not heavy computations
that require two hours running Mathematica, but simply the kind of mildly-painful calculation that
might take a couple of paragraphs on paper.

Currently the tutorial focuses on the brand new tactic ``polyrith`` and on ``field_simp``.  There
are several other powerful tactics which are commonly needed for "computational" proofs, notably
``norm_num``, ``norm_cast`` (and variants), and ``(n)linarith``. These other tactics are discussed
in context as the need arises, but this tutorial might eventually be extended to cover them too.

This is an intermediate-level tutorial, requiring familiarity with the syntax of Lean as covered in
approximately the first two chapters of `Mathematics in Lean
<https://leanprover-community.github.io/mathematics_in_lean/>`_.  But the focus of the exercises and
presentation is on the computations, so don't worry about understanding every detail of the syntax
if you can pick up the general idea.

This tutorial is new (July 2022) and feedback is very welcome. If you try this tutorial, come to
the Lean chat room on `Zulip <https://leanprover.zulipchat.com/>`_ and say hello!

**Acknowledgements:** I have raided the mathlib contributions of a number of people for examples in
this tutorial.  Thank you to Johan Commelin, Julian Külshammer and François
Sunatori! And particular thanks to Jeremy Avigad, for sharing the Sphinx template for the tutorial,
and Rob Lewis, for many conversations about automation in Lean. The port to Lean 4 was made in collaboration
with Marc Masdeu.
