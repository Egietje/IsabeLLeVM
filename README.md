# IsabeLLeVM

This project serves as my master's thesis at University of Twente.
I am supervised by dr. P. Lammich and E. Putti.


# Abstract

LLVM-IR is the intermediate representation at the core of LLVM, a widely used compilation toolchain.
Many source languages can be compiled to it, and it can be further compiled to many machine architectures.
As of yet, no foundational deductive verifier exists for LLVM-IR.
In this thesis, we present our implementation of a deductive verifier in Isabelle/HOL for a subset of LLVM-IR: IsabeLLeVM.

A common issue in deductive verification is that many verifiers only support a small set of programming languages.
This introduces complications when switching languages, as verification often has to be redone entirely.
Although the subset of LLVM-IR we support is limited, once extended our verifier would be able to fully verify programs written in a vast array of source-languages, given that a compiler to LLVM-IR exists.
This represents a first step to get around the issue.
From there, further work allowing the use of existing program specifications would complete the solution to this problem.

We make several contributions for the implementation of LLVM-IR verifiers:
+ we formalize the semantics of a subset of LLVM-IR (artifacts found under `formalization`);
+ we implement verification methods for partial correctness (artifacts found under `verification`);
+ we create methods which automate verification condition generation to reduce effort (artifacts found under `automation`);
+ we perform a case study demonstrating the applicability of our tool on sample programs (artifacts found under `case-study`).

We formalize the semantics of a subset of LLVM-IR consisting of a binary operation, memory operations, a comparison operation, (conditional) branching, and function calls.
Although the subset consists only of simple operations, it is enough to describe programs with relatively complex behavior like the Euclidean algorithm.

We implement verification infrastructure for partial correctness based on weakest-precondition based verification condition generation, function summarization, and Floyd's method.
With the weakest-precondition based verification condition generation we are able to verify sequential programs.
Then, we extend this verification to cover programs with function calls using function summarization.
Finally, we apply Floyd-style reasoning to lift the verification to programs with arbitrary control-flow.
Because we implement this infrastructure in the Isabelle/HOL theorem prover, we fully verify that the techniques guarantee program correctness with respect to our formalized semantics. 

We create proof automation methods using Isabelle's Eisbach infrastructure.
These methods automatically apply the correct predicate transformations to generate verification conditions.

Finally, we perform our case study on three sample programs implemented using different features such as for-loops, function calls, and mutual recursion.
Here, we demonstrate that our verifier is able to effectively verify common benchmark programs with all of the supported features in our subset of LLVM-IR.
