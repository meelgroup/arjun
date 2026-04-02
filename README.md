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

Note that the simplification part of Arjun contains code from SharpSAT-td by
Tuukka Korhonen and Matti Jarvisalo, see [this
PDF](https://raw.githubusercontent.com/Laakeri/sharpsat-td/main/description.pdf)
and [this code](https://github.com/Laakeri/sharpsat-td) for details. Note that
treewidth-decomposition is _not_ part of Arjun.

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

Arjun depends on [CaDiCaL](https://github.com/meelgroup/cadical),
[CryptoMiniSat](https://github.com/meelgroup/cryptominisat),
[SBVA](https://github.com/meelgroup/SBVA), and
[treedecomp](https://github.com/meelgroup/treedecomp).

**Automatic download and build (easiest):** if you do not specify where any
dependency lives, CMake will automatically clone and build it inside the `deps/`
subdirectory of your build directory:

```shell
mkdir build && cd build
cmake ..
make -j8
```

**Using pre-built dependencies:** pass `-D<dep>_DIR=<path>` for any dependency
you have already built. CMake will then use that copy instead of fetching it:

```shell
mkdir build && cd build
cmake .. \
    -Dcadical_DIR=/path/to/cadical/build \
    -Dcryptominisat5_DIR=/path/to/cryptominisat/build \
    -Dsbva_DIR=/path/to/sbva/build \
    -Dtreedecomp_DIR=/path/to/treedecomp/build
make -j8
```

You can mix and match: omit any `-D<dep>_DIR` flag and that dependency will be
fetched and built automatically.

For CaDiCaL you can also set `-Dcadical_SRC_DIR=<path>` to point to the
CaDiCaL source directory (needed for `cadical.hpp`) if it differs from
`<cadical_DIR>/../src`.

## How to Use
Run it on your instance and it will give you a reduced independent set:

```plain
$ ./arjun input.cnf output.cnf
c [arjun] original sampling set size: 500
c ind 1 4 5 20 31 0
[...]
c [arjun] Done dumping. T: 1.0406
```
This means that your input independent set of your input formula `input.cnf`,
which had a size of 500 has been reduced to 5, which is ony 1% of the original
set. The simplified formula with the smaller independent set has been output to
`output.cnf`. The final simplified will contain a line such as:
```plain
c MUST MULTIPLY BY 1024
```

This means that the final count of the CNF must be multiplied by 2^10 (i.e.
1024) in order to get the correct count. Note that if you forget to multiply,
the count will be wrong. So you must multiply.

## Only extracting independent set
In case you are only interested in a reduced independent set, use:
```plain
$ ./arjun input.cnf
c [arjun] original sampling set size: 500
c ind 1 4 5 20 31 0
```

This will not write an output file, but only display the reduced independent set.
