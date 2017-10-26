# REA
A set of [MAGMA][] functions for computations within the reflection equation algebra for GL_N.

This code was delevoped by D. Jordan and N. White while working on the paper [The center of the reflection equation algebra via quantum minors][paper].

## Use of the code

Before loading, the user should set a variable `N`. Loading the code will produce the reflection equation algebra for GL_N.

## Organisation of the code

The code is organised as follows.

1. Simple helper functions
2. Setup of the REA algebra
3. Implement PBW relations for REA
4. Setup of the FRT algebra
5. Implement PBW relations for FRT
6. The R-matrix
7. Twisting of the REA multiplication to FRT
8. Inverse of the twist map
9. The adjoint action on the REA
10. The invariants
11. Truncated minors, DL minors and REA minors
12. The quantum Cayley Hamilton identity

The code is mostly undocumented and the user should be aware that it has not been thoroughly checked for errors. Questions and comments are welcome. Please let us know if you find the code useful.

[paper]: https://arxiv.org/abs/1709.09149
[MAGMA]: http://magma.maths.usyd.edu.au/magma/
