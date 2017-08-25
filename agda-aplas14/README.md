Strong normalization of simply-typed lambda-calculus in Agda
============================================================

Proof extracted from:

> Andreas Abel and Andrea Vezzosi:
> A Formalized Proof of Strong Normalization for Guarded Recursive Types.
> APLAS 2014: 140-158

To check run:
```
  agda Soundness.agda
```
The Agda standard library must be installed.

The proof uses evaluation contexts, which might be a bit of an
overkill for pure lambda-calculus.  In the original proof, more term
former are present, such as for products and guarded types.
