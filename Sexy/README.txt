This is a Haskell software code to implement cup products for Hilbert schemes of points on K3 surfaces.
To start, you may run HilbK3.hs in an interactive Haskell compiler such as ghci.


The code is divided into 4 files depending on each other:

HilbK3.hs
This is our main module. We implement the algebraic model developped by Lehn and Sorger
and the change of base due to Qin and Wang. The cup product on the Hilbert
scheme is computed by the function cupInt.

K3.hs
Here the hyperbolic
and the E_8 lattice and the bilinear form on the cohomology of a K3 surface are
defined. Furthermore, cup products and their adjoints are implemented.

Partitions.hs
This module defines the data structures
and elementary methods to handle partitions. We define both partitions written
as descending sequences of integers (lambda-notation) and as sequences of multiplicities
(alpha-notation).

SymmetricFunctions.hs
This module provides
nothing but the base change matrices 
from Definition 1.2.
