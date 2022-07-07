/*************
Python bindings to Arjun (github.com/meelgroup/arjun)

Copyright (c) 2013, Ilan Schnell, Continuum Analytics, Inc.
              2014, Mate Soos
              2017, Pierre Vignet

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
**********************************/

#include <vector>
#include <limits>
#include <cassert>
#include <algorithm>
#include "arjun.h"

#include <Python.h>
#include <structmember.h>


#define MODULE_NAME "pyarjun"
#define MODULE_DOC "Arjun independent set minimizer"

// Compatibility between Python 2 and 3
#define IS_INT(x)  PyLong_Check(x)

#define MODULE_INIT_FUNC(name) \
    PyMODINIT_FUNC PyInit_ ## name(void); \
    PyMODINIT_FUNC PyInit_ ## name(void)

typedef struct {
    PyObject_HEAD
    /* Type-specific fields go here. */
    ArjunNS::Arjun* arjun;
    std::vector<CMSat::Lit> tmp_cl_lits;

    int verbose;
    int simp;
    int get_indep_called = 0;
} Arjun;

static const char solver_create_docstring[] = \
"Arjun(verbose=0, time_limit=max_numeric_limits, confl_limit=max_numeric_limits, threads=1)\n\
Create Arjun object.\n\
\n\
:param verbose: Verbosity level: 0: nothing printed; 15: very verbose.\n\
:param time_limit: Propagation limit: abort after this many seconds has elapsed.\n\
:param confl_limit: Propagation limit: abort after this many conflicts.\n\
    Default: never abort.\n\
:param threads: Number of threads to use.\n\
:type verbose: <int>\n\
:type time_limit: <double>\n\
:type confl_limit: <long>\n\
:type threads: <int>";

static void setup_solver(Arjun *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"verbose", "simp", NULL};

    self->arjun = NULL;
    self->verbose = 0;

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|ii", kwlist, &self->verbose, &self->simp))
    {
        return;
    }

    if (self->verbose < 0) {
        PyErr_SetString(PyExc_ValueError, "verbosity must be at least 0");
        return;
    }
    if (self->simp < 0) {
        PyErr_SetString(PyExc_ValueError, "simp must be at least 0");
        return;
    }

    self->arjun = new ArjunNS::Arjun;
    self->arjun->set_verbosity(self->verbose);
    self->arjun->set_simp(self->simp);

    return;
}

static int convert_lit_to_sign_and_var(PyObject* lit, long& var, bool& sign)
{
    if (!IS_INT(lit))  {
        PyErr_SetString(PyExc_TypeError, "integer expected !");
        return 0;
    }

    long val = PyLong_AsLong(lit);
    if (val == 0) {
        PyErr_SetString(PyExc_ValueError, "non-zero integer expected");
        return 0;
    }
    if (val > std::numeric_limits<int>::max()/2
        || val < std::numeric_limits<int>::min()/2
    ) {
        PyErr_Format(PyExc_ValueError, "integer %ld is too small or too large", val);
        return 0;
    }

    sign = (val < 0);
    var = std::abs(val) - 1;

    return 1;
}

static int parse_clause(
    Arjun *self
    , PyObject *clause
    , std::vector<CMSat::Lit>& lits
) {
    PyObject *iterator = PyObject_GetIter(clause);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "iterable object expected");
        return 0;
    }

    PyObject *lit;
    long int max_var = 0;
    while ((lit = PyIter_Next(iterator)) != NULL) {
        long var;
        bool sign;
        int ret = convert_lit_to_sign_and_var(lit, var, sign);
        Py_DECREF(lit);
        if (!ret) {
            Py_DECREF(iterator);
            return 0;
        }
        max_var = std::max(var, max_var);

        lits.push_back(CMSat::Lit(var, sign));
    }

    if (!lits.empty() && max_var >= (long int)self->arjun->nVars()) {
        self->arjun->new_vars(max_var-(long int)self->arjun->nVars()+1);
    }

    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return 0;
    }

    return 1;
}

static int parse_xor_clause(
    Arjun *self
    , PyObject *clause
    , std::vector<uint32_t>& vars
) {
    PyObject *iterator = PyObject_GetIter(clause);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "iterable object expected");
        return 0;
    }

    PyObject *lit;
    while ((lit = PyIter_Next(iterator)) != NULL) {
        long var;
        bool sign;
        int ret = convert_lit_to_sign_and_var(lit, var, sign);
        Py_DECREF(lit);
        if (!ret) {
            Py_DECREF(iterator);
            return 0;
        }
        if (sign) {
            PyErr_SetString(PyExc_ValueError, "XOR clause must contiain only positive variables (not inverted literals)");
            Py_DECREF(iterator);
            return 0;
        }

        if (var >= self->arjun->nVars()) {
            for(long i = (long)self->arjun->nVars(); i <= var ; i++) {
                self->arjun->new_var();
            }
        }

        vars.push_back(var);
    }
    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return 0;
    }

    return 1;
}

static int _add_clause(Arjun *self, PyObject *clause)
{
    self->tmp_cl_lits.clear();
    if (!parse_clause(self, clause, self->tmp_cl_lits)) {
        return 0;
    }
    self->arjun->add_clause(self->tmp_cl_lits);

    return 1;
}

PyDoc_STRVAR(add_clause_doc,
"add_clause(clause)\n\
Add a clause to the solver.\n\
\n\
:param clause: A clause contains literals (ints)\n\
:type clause: <list>\n\
:return: None\n\
:rtype: <None>"
);

static PyObject* add_clause(Arjun *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"clause", NULL};
    PyObject *clause;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O", kwlist, &clause)) {
        return NULL;
    }

    if (_add_clause(self, clause) == 0 ) {
        return NULL;
    }

    Py_INCREF(Py_None);
    return Py_None;
}

template <typename T>
static int _add_clauses_from_array(Arjun *self, const size_t array_length, const T *array)
{
    if (array_length == 0) {
        return 1;
    }
    if (array[array_length - 1] != 0) {
        PyErr_SetString(PyExc_ValueError, "last clause not terminated by zero");
        return 0;
    }
    size_t k = 0;
    long val = 0;
    std::vector<CMSat::Lit>& lits = self->tmp_cl_lits;
    for (val = (long) array[k]; k < array_length; val = (long) array[++k]) {
        lits.clear();
        long int max_var = 0;
        for (; k < array_length && val != 0; val = (long) array[++k]) {
            long var;
            bool sign;
            if (val > std::numeric_limits<int>::max()/2
                || val < std::numeric_limits<int>::min()/2
            ) {
                PyErr_Format(PyExc_ValueError, "integer %ld is too small or too large", val);
                return 0;
            }

            sign = (val < 0);
            var = std::abs(val) - 1;
            max_var = std::max(var, max_var);

            lits.push_back(CMSat::Lit(var, sign));
        }
        if (!lits.empty()) {
            if (max_var >= (long int)self->arjun->nVars()) {
                self->arjun->new_vars(max_var-(long int)self->arjun->nVars()+1);
            }
            self->arjun->add_clause(lits);
        }
    }
    return 1;
}

static int _add_clauses_from_buffer_info(Arjun *self, PyObject *buffer_info, const size_t itemsize)
{
    PyObject *py_array_length = PyTuple_GetItem(buffer_info, 1);
    if (py_array_length == NULL) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: could not get array length");
        return 0;
    }
    long array_length = PyLong_AsLong(py_array_length);
    if (array_length < 0) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: could not get array length");
        return 0;
    }
    PyObject *py_array_address = PyTuple_GetItem(buffer_info, 0);
    if (py_array_address == NULL) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: could not get array address");
        return 0;
    }
    const void *array_address = PyLong_AsVoidPtr(py_array_address);
    if (array_address == NULL) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: could not get array address");
        return 0;
    }
    if (itemsize == sizeof(int)) {
        return _add_clauses_from_array(self, array_length, (const int *) array_address);
    }
    if (itemsize == sizeof(long)) {
        return _add_clauses_from_array(self, array_length, (const long *) array_address);
    }
    if (itemsize == sizeof(long long)) {
        return _add_clauses_from_array(self, array_length, (const long long *) array_address);
    }
    PyErr_Format(PyExc_ValueError, "invalid clause array: invalid itemsize '%ld'", itemsize);
    return 0;
}

static int _check_array_typecode(PyObject *clauses)
{
    PyObject *py_typecode = PyObject_GetAttrString(clauses, "typecode");
    if (py_typecode == NULL) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: typecode is NULL");
        return 0;
    }

    PyObject *typecode_bytes = PyUnicode_AsASCIIString(py_typecode);
    Py_DECREF(py_typecode);
    if (typecode_bytes == NULL) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: could not get typecode bytes");
        return 0;
    }

    const char *typecode_cstr = PyBytes_AsString(typecode_bytes);
    if (typecode_cstr == NULL) {
        Py_DECREF(typecode_bytes);
        PyErr_SetString(PyExc_ValueError, "invalid clause array: could not get typecode cstring");
        return 0;
    }
    const char typecode = typecode_cstr[0];
    if (typecode == '\0' || typecode_cstr[1] != '\0') {
        PyErr_Format(PyExc_ValueError, "invalid clause array: invalid typecode '%s'", typecode_cstr);
        Py_DECREF(typecode_bytes);
        return 0;
    }
    Py_DECREF(typecode_bytes);
    if (typecode != 'i' && typecode != 'l' && typecode != 'q') {
        PyErr_Format(PyExc_ValueError, "invalid clause array: invalid typecode '%c'", typecode);
        return 0;
    }
    return 1;
}

static int add_clauses_array(Arjun *self, PyObject *clauses)
{
    if (_check_array_typecode(clauses) == 0) {
        return 0;
    }
    PyObject *py_itemsize = PyObject_GetAttrString(clauses, "itemsize");
    if (py_itemsize == NULL) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: itemsize is NULL");
        return 0;
    }
    const long itemsize = PyLong_AsLong(py_itemsize);
    Py_DECREF(py_itemsize);
    if (itemsize < 0) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: could not get itemsize");
        return 0;
    }
    PyObject *buffer_info = PyObject_CallMethod(clauses, "buffer_info", NULL);
    if (buffer_info == NULL) {
        PyErr_SetString(PyExc_ValueError, "invalid clause array: buffer_info is NULL");
        return 0;
    }
    int ret = _add_clauses_from_buffer_info(self, buffer_info, itemsize);
    Py_DECREF(buffer_info);
    return ret;
}

PyDoc_STRVAR(add_clauses_doc,
"add_clauses(clauses)\n\
Add iterable of clauses to the solver.\n\
\n\
:param clauses: List of clauses. Each clause contains literals (ints)\n\
    Alternatively, this can be a flat array.array (typecode 'i', 'l', or 'q')\n\
    of zero separated and terminated clauses of literals (ints).\n\
:type clauses: <list> or <array.array>\n\
:return: None\n\
:rtype: <None>"
);

static PyObject* add_clauses(Arjun *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"clauses", NULL};
    PyObject *clauses;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O", kwlist, &clauses)) {
        return NULL;
    }

    if (
        PyObject_HasAttr(clauses, PyUnicode_FromString("buffer_info")) &&
        PyObject_HasAttr(clauses, PyUnicode_FromString("typecode")) &&
        PyObject_HasAttr(clauses, PyUnicode_FromString("itemsize"))
    ) {
        int ret = add_clauses_array(self, clauses);
        if (ret == 0 || PyErr_Occurred()) {
            return 0;
        }
        Py_INCREF(Py_None);
        return Py_None;
    }

    PyObject *iterator = PyObject_GetIter(clauses);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "iterable object expected");
        return NULL;
    }

    PyObject *clause;
    while ((clause = PyIter_Next(iterator)) != NULL) {
        _add_clause(self, clause);
        /* release reference when done */
        Py_DECREF(clause);
    }

    /* release reference when done */
    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return NULL;
    }

    Py_INCREF(Py_None);
    return Py_None;
}

static PyObject* add_xor_clause(Arjun *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"xor_clause", "rhs", NULL};
    PyObject *rhs;
    PyObject *clause;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "OO", kwlist, &clause, &rhs)) {
        return NULL;
    }
    if (!PyBool_Check(rhs)) {
        PyErr_SetString(PyExc_TypeError, "rhs must be boolean");
        return NULL;
    }
    bool real_rhs = PyObject_IsTrue(rhs);

    std::vector<uint32_t> vars;
    if (!parse_xor_clause(self, clause, vars)) {
        return 0;
    }

    self->arjun->add_xor_clause(vars, real_rhs);

    Py_INCREF(Py_None);
    return Py_None;
}

PyDoc_STRVAR(nb_vars_doc,
"nb_vars()\n\
Return the number of literals in the solver.\n\
\n\
:return: Number of literals\n\
:rtype: <int>"
);

static PyObject* nb_vars(Arjun *self)
{
    return PyLong_FromLong(self->arjun->nVars());
}

static PyObject* get_indep_set(Arjun *self, PyObject *args, PyObject *kwds)
{
    if (self->get_indep_called > 0) {
        PyErr_SetString(PyExc_SystemError, "get_indep_set can only be called ONCE per Arjun object");
        return NULL;
    }
    self->get_indep_called++;

    static char* kwlist[] = {"indep_vars", NULL};
    PyObject *vars;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O", kwlist, &vars)) {
        return NULL;
    }

    PyObject *iterator = PyObject_GetIter(vars);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "interable object expected");
        return 0;
    }

    std::vector<uint32_t> out_vars;
    PyObject *lit;
    while ((lit = PyIter_Next(iterator)) != NULL) {
        long var;
        bool sign;
        int ret = convert_lit_to_sign_and_var(lit, var, sign);
        Py_DECREF(lit);
        if (!ret) {
            Py_DECREF(iterator);
            return NULL;
        }

        if (var >= self->arjun->nVars()) {
            Py_DECREF(iterator);
            PyErr_Format(PyExc_ValueError, "Variable %ld not used in clauses", var+1);
            return NULL;
        }

        if (sign != false) {
            Py_DECREF(iterator);
            PyErr_Format(PyExc_ValueError, "Variable %ld is negated in independent set, but independent set contains variables, not literals", var+1);
            return NULL;
        }

        out_vars.push_back(var);
    }
    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return NULL;
    }

    if (out_vars.empty()) {
        self->arjun->start_with_clean_sampling_set();
    } else {
        self->arjun->set_starting_sampling_set(out_vars);
    }

    std::vector<uint32_t> ret = self->arjun->get_indep_set();
    PyObject* reto = PyList_New(0);
    if (!reto) {
        Py_DECREF(reto);
        return NULL;
    }
    for(const auto& v: ret) {
        int ret = PyList_Append(reto, PyLong_FromLong(v));
        if (ret != 0) {
            Py_DECREF(reto);
            return NULL;
        }
    }

    return reto;
}

PyDoc_STRVAR(get_indep_set_doc,
"get_indep_set(variables)\n\
Return smaller independent set than given. If empty array given, all variables are taken\n\
as independent. Otherwise, the input array determines what set needs to be minimized. \n\
\n\
This function can only be called ONCE per Arjun object. In other words, you must first\n\
add all the clauses you want to, then you should call this function.\n\
\n\
:return: Smaller independent set\n\
:rtype: <array <Longs>>"
);

/*************************** Method definitions *************************/

static PyMethodDef Arjun_methods[] = {
    {"get_indep_set",     (PyCFunction) get_indep_set, METH_VARARGS | METH_KEYWORDS, get_indep_set_doc},
    {"add_clause",(PyCFunction) add_clause,  METH_VARARGS | METH_KEYWORDS, add_clause_doc},
    {"add_clauses", (PyCFunction) add_clauses,  METH_VARARGS | METH_KEYWORDS, add_clauses_doc},
    {"add_xor_clause",(PyCFunction) add_xor_clause,  METH_VARARGS | METH_KEYWORDS, "adds an XOR clause to the system"},
    {"nb_vars", (PyCFunction) nb_vars, METH_VARARGS | METH_KEYWORDS, nb_vars_doc},
    {NULL,        NULL}  /* sentinel - marks the end of this structure */
};

static void
Arjun_dealloc(Arjun* self)
{
    delete self->arjun;
    Py_TYPE(self)->tp_free ((PyObject*) self);
}

static int
Arjun_init(Arjun *self, PyObject *args, PyObject *kwds)
{
    if (self->arjun != NULL) {
        delete self->arjun;
    }

    setup_solver(self, args, kwds);
    if (!self->arjun) {
        return -1;
    }
    return 0;
}

static PyTypeObject pyarjun_ArjunType = {
    PyVarObject_HEAD_INIT(NULL, 0) /*ob_size*/
    "pyarjun.Arjun",       /*tp_name*/
    sizeof(Arjun),             /*tp_basicsize*/
    0,                          /*tp_itemsize*/
    (destructor)Arjun_dealloc, /*tp_dealloc*/
    0,                          /*tp_print*/
    0,                          /*tp_getattr*/
    0,                          /*tp_setattr*/
    0,                          /*tp_compare*/
    0,                          /*tp_repr*/
    0,                          /*tp_as_number*/
    0,                          /*tp_as_sequence*/
    0,                          /*tp_as_mapping*/
    0,                          /*tp_hash */
    0,                          /*tp_call*/
    0,                          /*tp_str*/
    0,                          /*tp_getattro*/
    0,                          /*tp_setattro*/
    0,                          /*tp_as_buffer*/
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE, /*tp_flags*/
    solver_create_docstring,    /* tp_doc */
    0,                          /* tp_traverse */
    0,                          /* tp_clear */
    0,                          /* tp_richcompare */
    0,                          /* tp_weaklistoffset */
    0,                          /* tp_iter */
    0,                          /* tp_iternext */
    Arjun_methods,             /* tp_methods */
    0,                          /* tp_members */
    0,                          /* tp_getset */
    0,                          /* tp_base */
    0,                          /* tp_dict */
    0,                          /* tp_descr_get */
    0,                          /* tp_descr_set */
    0,                          /* tp_dictoffset */
    (initproc)Arjun_init,      /* tp_init */
};

MODULE_INIT_FUNC(pyarjun)
{
    PyObject* m;

    pyarjun_ArjunType.tp_new = PyType_GenericNew;
    if (PyType_Ready(&pyarjun_ArjunType) < 0) {
        // Return NULL on Python3 and on Python2 with MODULE_INIT_FUNC macro
        // In pure Python2: return nothing.
        return NULL;
    }

    static struct PyModuleDef moduledef = {
        PyModuleDef_HEAD_INIT,  /* m_base */
        MODULE_NAME,            /* m_name */
        MODULE_DOC,             /* m_doc */
        -1,                     /* m_size */
        NULL,                   /* m_methods */
        NULL,                   /* m_reload */
        NULL,                   /* m_traverse */
        NULL,                   /* m_clear */
        NULL,                   /* m_free */
    };

    m = PyModule_Create(&moduledef);

    // Return NULL on Python3 and on Python2 with MODULE_INIT_FUNC macro
    // In pure Python2: return nothing.
    if (!m) {
        return NULL;
    }

    // Add the version string so users know what version of Arjun
    // they're using.
    if (PyModule_AddStringConstant(m, "__version__", "1.0.0") == -1) {
        Py_DECREF(m);
        return NULL;
    }

    // Add the Arjun type.
    Py_INCREF(&pyarjun_ArjunType);
    if (PyModule_AddObject(m, "Arjun", (PyObject *)&pyarjun_ArjunType)) {
        Py_DECREF(m);
        return NULL;
    }

    return m;
}
