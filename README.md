[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![build](https://github.com/meelgroup/arjun/workflows/build/badge.svg)

# Arjun
A minimal independent set calculator and CNF minimizer that uses a combination
of steps to simplify a CNF such that its count stays the same. Name is taken
from the Hindu myth where [Arjun](https://en.wikipedia.org/wiki/Arjuna) is
known for being the "one who concentrates the most". This system is also used
as a preprocessor for our tool
[ApproxMC](https://github.com/meelgroup/ApproxMC) and should be used in front
of [GANAK](https://github.com/meelgroup/ganak). For the paper, see
[here](http://www.msoos.org/wordpress/wp-content/uploads/2022/08/arjun.pdf).

Note that the simplification part of Arjun contains code from SharpSAT-TD by
Tuukka Korhonen and Matti Jarvisalo, see [this
PDF](https://raw.githubusercontent.com/Laakeri/sharpsat-td/main/description.pdf)
and [this code](https://github.com/Laakeri/sharpsat-td) for details. Note that
treewidth-decomposition is _not_ part of Arjun, instead it is
[here](https://github.com/meelgroup/treedecomp/).

## How to Build
It is strongly recommended to not build, but to use the precompiled
binaries as in our [release](https://github.com/meelgroup/arjun/releases).
The second best thing to use is Nix. Simply [install
nix](https://nixos.org/download/) and then:
```shell
nix shell github:meelgroup/arjun
```

Then you will have `arjun` binary available and ready to use.

### Building from source

**Quickest build (auto-fetch the FetchContent-capable deps):

```shell
mkdir build && cd build
cmake ..
make -j8
```

### Building statically

To build a static binary, you first need to build GMP with static library support:

```shell
wget https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz
tar xf gmp-6.3.0.tar.xz
cd gmp-6.3.0
./configure --enable-static --enable-cxx --enable-shared --with-pic
make -j8
sudo make install
cd ..
```

Then point CMake to the installed GMP static libraries (note: use `/usr/local/lib/`,
not a custom build directory, as those may be compiled for the wrong architecture):

```shell
mkdir build && cd build
cmake -DBUILD_SHARED_LIBS=OFF \
    -DGMPXX_LIBRARY=/usr/local/lib/libgmpxx.a \
    -DGMP_INCLUDE_DIR=/usr/local/include \
    ..
make -j8
```

## How to Use to Preprocess
Run it on your instance and it will write a simplified CNF with a reduced
independent set:

```plain
$ ./arjun input.cnf output.cnf
c o [arjun] Input file: input.cnf
c o [arjun] Output file: output.cnf
[...]
c o [arjun] dumped simplified problem to 'output.cnf'
c o [arjun] All done. T: 1.04
```

All of Arjun's own log lines start with `c o ` (comment + `o` for "output").
The simplified CNF written to `output.cnf` will contain (among other things) a
line such as:

```plain
c p show 1 4 5 20 31 0
c p optshow 1 4 5 20 31 7 0
c MUST MULTIPLY BY 1024 0
```

`c p show` is the reduced independent / projection set (see the *Headers*
section below). The `c MUST MULTIPLY BY 1024 0` line says the count of the
simplified CNF must be multiplied by 1024 in order to get the correct count of
the original formula. **If you forget to multiply, the count will be wrong.**

## Only extracting the independent set
In case you are only interested in a reduced independent set (no simplified CNF
output), omit the output file:

```plain
$ ./arjun input.cnf
[...]
c o [arjun] final set size:       5 percent of original:  1.000 %
c p show 1 4 5 20 31 0
c p optshow 1 4 5 20 31 7 0
c MUST MULTIPLY BY 1
c o [arjun] All done. T: 1.04
```

Arjun does not write an output file in this mode; the reduced projection set
is printed to stdout as `c p show ... 0`.

## Headers / DIMACS extensions
Beyond the standard `p cnf` header and clauses, Arjun's DIMACS parser
understands the following comment-style extensions:

| Header                       | Meaning                                                                                                  |
| ---------------------------- | -------------------------------------------------------------------------------------------------------- |
| `c p show v1 v2 ... 0`       | Projection / independent set (modern, preferred).                                                        |
| `c p optshow v1 v2 ... 0`    | Optional / extended sampling set (a superset of `c p show` that the solver may use as a hint).           |
| `c p weight LIT VALUE`       | Weight of a literal (for weighted counting). Requires `--mode 1`.                                        |
| `c t mc \| pmc \| wmc \| pwmc` | Counting task type: `mc` = model counting, `pmc` = projected MC, `wmc` = weighted MC, `pwmc` = projected weighted MC. |
| `c MUST MULTIPLY BY N`       | Existing count multiplier carried into Arjun (Arjun will combine it with the multiplier it produces).    |
| `c ind v1 v2 ... 0`          | Legacy independent-set syntax. Still accepted, but prefer `c p show`. |

### Modes
Arjun supports several top-level modes, selected via command-line flags:

- **Default (unweighted model counting preprocessing)** — minimize the
  independent set and simplify the CNF while preserving its model count.
- **Weighted counting** — pass `--mode 1`. Required if your input uses
  `c p weight` lines or `c t wmc` / `c t pwmc`. Weights are tracked through
  simplification.
- **ApproxMC preset** — pass `--appmc`. Sets simplification defaults tuned for
  use as an [ApproxMC](https://github.com/meelgroup/ApproxMC) front-end
  (different oracle / Puura iteration settings).
- **Synthesis (`--synth`)** — instead of producing a simplified
  CNF, compute a Boolean function for each defined (non-input) variable in
  terms of the projection-set variables (Manthan-style
  counterexample-guided repair). When an output path is given, Arjun writes a
  Verilog file with the synthesized functions:

  ```shell
  ./arjun --synth input.cnf output.v
  ```
## How to Use to Synthesize
Simply use `--synth` and then you can get a Verilog for the skolem functions by passing a 2nd argument as a output.v for verilog:

```bash
./arjun --synth myfile.dimacs skolems.v
```
