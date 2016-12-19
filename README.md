# VeriCUDA
A verifier for CUDA.

## Requirements

OCaml 4.03.0 and the libraries:

* cil 1.7.3
* why3 0.87.2
* extlib 1.7.0

SMT solvers:

* Alt-Ergo
* CVC3
* CVC4
* E Theorem Prover
* Z3

The list of solvers is currently hard coded.  If you do not want to
use some of them and/or want to use other solvers, you can do so by
modifying the definition of `prover_name_list` in the middle of
`verifier.ml`.

## Install

```
$ git clone https://github.com/SoftwareFoundationGroupAtKyotoU/Vericuda.git
$ make
```

### Installing OCaml and libraries

The easiest way is to install opam, and then

```
$ opam switch 4.03.0
$ eval `opam config env`
$ opam install why3 extlib cil alt-ergo
```

During installation, you might need to install
`libgtksourceview2.0-dev` package:

```
$ sudo apt-get install libgtksourceview2.0-dev
```

### Configuring Why3

In addition, you need to configure why3 (after installing all the SMT
solvers used by VeriCUDA).

```
$ why3 config --detect
```

and then add load paths by editing `$HOME/.why3.conf`:

```
loadpath = “$HOME/.opam/4.03.0/share/why3/theories”
loadpath = “$HOME/.opam/4.03.0/share/why3/modules”
loadpath = “/ptah/to/VeriCUDA/directory”
```

## Usage

```
./vericuda.opt [options] filename funcname
```

`./vericuda.opt --help` prints the list of options.

## Samples

See `samples/`.
