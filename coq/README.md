# Adapting Verified Compilation for Target-Language Errors #

This is the Coq development that accompanies the paper Adapting
Verified Compilation for Target-Language Errors, submitted to CC
2022. It contains an implementation of a small verified compiler from
a simple imperative language to a stack machine featuring
nondeterministic interruption.

## Checking the proofs ##

Our proofs were developed using Coq version 8.13.2 and only uses
modules contained within the Coq standard library.

To compile the Coq code and check the proofs, run:
```
make -f CoqMakefile
```

## Structure of the Coq development ##

The Coq development is structured as follows:

- `Sequences.v`: a library of definitions and lemmas about finite and
  infinite sequences of small-step transitions.
- `IMP.v`: defines the abstract syntax and operational semantics of
  the source language, `IMP`.
- `Compil.v`: defines the abstract syntax of the target stack machine
  and the translation function from source to target.
- `MachDeterm.v`: defines the operational semantics of the
  deterministic subset of the target language, and proves backward
  simulation between IMP and the stack machine when executed under
  these semantics.
- `MachFull.v`: adds nondeterministic interruption to the target
  language, and proves the prefix-correct theorem (see Section 3.1)
  for the compiler when the target is executed under the full semantics.

## Acknowledgements ##

This development is based on Xavier Leroy's [EUTypes 2019 compiler
correctness tutorial](https://xavierleroy.org/courses/EUTypes-2019/).
We added explicit traces of externally visible events and
nondeterministic interruption in the target language. We also changed
most of the proof to use the proof technique described in Section 3.1.1
of our submission.

Parts of the file Sequences.v contain code adapted from the [Coq
development](https://github.com/secure-compilation/different_traces)
of the paper: [Trace-relating compiler correctness and secure
compilation.](https://arxiv.org/abs/1907.05320) Carmine Abate, Roberto
Blanco, Ștefan Ciobâcă, Adrien Durier, Deepak Garg, Cătălin Hriţcu,
Marco Patrignani, Éric Tanter, and Jérémy Thibault. ESOP 2020.

