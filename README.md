# WildCat

## Prerequisites

To get dev version of HoTT library

```shell
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```

Install dependencies

```shell
opam install . --deps-only
```

## Building library

Running `make` will call `dune`. No need to specify number of jobs.


TODO:

Develop a wildcat library dependent on the hott library without needing to disturb upstream development.

We want to consider:

 * Ease of use
 * Efficiency of typeclass search
 * Elaboration by coq
 * Flexivility of constructions
 * Example: Definitionally involutive op
 * Having more cells, coinductive/globular appraoch or specified
 * Various levels of coherence
 
 
