# Arjun

A minimal independent set calculator using a combination of explicit and implicit search, together with implicit gate detection, etc. Name is taken from the Hindu myth where [Arjun](https://en.wikipedia.org/wiki/Arjuna) is known for being the "one who concentrates the most". This system is also used as a preprocessor for our tool [ApproxMC](https://github.com/meelgroup/ApproxMC) to concentrate on counting only over the independent set. For the paper, see [here](https://arxiv.org/abs/2110.09026).


## How to Build
To build on Linux, you will need the following:
```
sudo apt-get install build-essential cmake
sudo apt-get install zlib1g-dev libboost-program-options-dev libm4ri-dev
```

Then, build CryptoMiniSat, Arjun:
```
git clone https://github.com/msoos/cryptominisat
cd cryptominisat
mkdir build && cd build
cmake ..
make
sudo make install

cd ../..
git clone https://github.com/meelgroup/arjun
cd arjun
mkdir build && cd build
cmake ..
make
sudo make install
```

## How to Use


### To only get a reduced independent set

Run it on your instance and it will give you a reduced independent set:

```
./arjun input.cnf output.cnf
c [arjun] original sampling set size: 500
c ind 1 4 5 20 31 0
[...]
c [arjun] Done dumping. T: 1.0406
```
This means that your input independent set of your input formula `input.cnf`, which had a size of 500 has been reduced to 5, which is ony 1% of the original set. The simplified formula with the smaller independent set has been output to `output.cnf`.



