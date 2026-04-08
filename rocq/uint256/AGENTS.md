This project tries to prove correctness of the uint256 arithmetic implemented in ../../category/core/runtime/uint256.hpp and ../../category/core/runtime/uint256.cpp.
First, the C++ implementation has been converted to Gallina using Claude-code, asking it to not use pure math numbers but to use finite-width models mirroring C++ and to ensure that the gallina functions do the operations in the same order.
It is very important that this translation be dump and as faithful as possible to C++.
For example, the Gallina model of the c++ mult function is in RuntimeMul.v
For division, it is in Division.v
The proof of the correctness of division is WIP in DivisionProofs.v

This project has a dune-based buils system. You can do `dune b DivisionProofs.v` to compile it.
While doing proofs, it may be helpful to look at the corresponding place in the C++ file and any explanatory comments there.
Also, proofs of similar algorithms have been discussed in standard  textbooks: relevant chapters are Knuth 4.3.1, Volume 2, and Hacker's Delight Chapter 9.
The latter book can be dowloaded from https://ptgmedia.pearsoncmg.com/images/9780321842688/samplepages/0321842685.pdf

If you every notice that the Gallina model of the C++ function is unfaithful, you must stop and report it.
For big proof files like DivisionProofs.v, edit/check them interactively using the API described in ~/fv-workspace/rocq-emacs-for-cli-agents/AGENTS.md


