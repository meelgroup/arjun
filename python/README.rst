===========================================
pyarjun: bindings to Arjun independent set minimizer
===========================================

This directory provides Python bindings to Arjun on the C++ level,
i.e. when importing pycryptosat, Arjun becomes part of the
Python process itself.

Compiling
-----
The pycryptosat python package compiles separately from the CryptoMiniSat library,
so if you have special flags included with CryptoMiniSat, it will NOT be reflected
in the python package.

In order to compile, install the python developer tools:

```
apt-get install python-dev
```

After this, cmake then indicate that pycryptosat will be compiled:

```
cd arjun/python
make
sudo make install
```

Usage
-----

The ``pycryptosat`` module has one object, ``Arjun`` that has two functions
``get_indep_set`` and ``add_clause``.

The funcion ``add_clause()`` takes an iterable list of literals such as
``[1, 2]`` which represents the truth ``1 or 2 = True``. For example,
``add_clause([1])`` sets variable ``1`` to ``True``.

The function ``get_indep_set()``, minimizes the independent set of variables
it is given. If it is given the empty set, it takes all variables in the problem
as indepenent:

   >>> from pycryptosat import Solver
   >>> s = Solver()
   >>> s.add_clause([1, 2])
   >>> s.add_clause([-1, -2])
   >>> indep = s.get_indep_set()
   >>> print indep
   [1]

