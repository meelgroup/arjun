# Arjun

A minimal independent set calculator using a combination of explicit and implicit search, together with implicit gate detection, etc. Name is taken from the Hindu myth where [Arjun](https://en.wikipedia.org/wiki/Arjuna) is known for being the "one who concentrates the most". This system is also used as a preprocessor for our tool [ApproxMC](https://github.com/meelgroup/ApproxMC) to concentrate on counting only over the independent set. For the paper, see [here](http://www.msoos.org/wordpress/wp-content/uploads/2022/08/arjun.pdf).

Note that the simplification part of Arjun contains code from SharpSAT-td by Tuukka Korhonen and Matti Jarvisalo, see [this PDF](https://raw.githubusercontent.com/Laakeri/sharpsat-td/main/description.pdf) and [this code](https://github.com/Laakeri/sharpsat-td) for details. Note that treewidth-decomposition is _not_ part of Arjun.


## How to Build
To build on Linux, you will need the following:
```
sudo apt-get install build-essential cmake
sudo apt-get install zlib1g-dev libboost-program-options-dev
```

Then, build CryptoMiniSat, Louvain-Community, and Arjun:
```
git clone https://github.com/msoos/cryptominisat
cd cryptominisat
mkdir build && cd build
cmake ..
make
sudo make install
sudo ldconfig

cd ../..
git clone https://github.com/meelgroup/louvain-community
cd louvain-community
mkdir build && cd build
cmake ..
make -j4
sudo make install
sudo ldconfig

cd ../..
git clone https://github.com/meelgroup/arjun
cd arjun
mkdir build && cd build
cmake ..
make
sudo make install
sudo ldconfig
```

## How to Use

Run it on your instance and it will give you a reduced independent set:

```
./arjun input.cnf output.cnf
c [arjun] original sampling set size: 500
c ind 1 4 5 20 31 0
[...]
c [arjun] Done dumping. T: 1.0406
```
This means that your input independent set of your input formula `input.cnf`, which had a size of 500 has been reduced to 5, which is ony 1% of the original set. The simplified formula with the smaller independent set has been output to `output.cnf`.


## Empty occurrences

Empty occurrences are when a variable is ostensibly part of the CNF, but actually doesn't show up in it at all. This happens often after simplification. Obviously, all solution numbers need to be multiplied by 2**n for such cases. Arjun can remove these variables via `--empty 1`:
```
./arjun --empty 1 input.cnf output.cnf
c [arjun] original sampling set size: 500
c [arjun] Done dumping. T: 1.9211
```

Now the file `output.cnf` will also contain a comment:
```
grep "MUST" output.cnf
c MUST MUTIPLY BY 2**10
```

This means that the final count of the CNF must be multiplied by 2^10 (i.e. 1024) in order to get the correct count. Note that if you forget to multiply, the count will be wrong. So you must multiply. Otherwise, just use the default setting, i.e. without `--empty 1`.

## Only extracting independent set
In case you are only interested in a reduced independent set, use:
```
./arjun input.cnf
c [arjun] original sampling set size: 500
c ind 1 4 5 20 31 0
```

This will not write an output file, but only display the reduced independent set.


