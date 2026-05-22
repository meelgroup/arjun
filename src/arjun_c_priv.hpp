/******************************************
Copyright (C) 2024 Authors of Arjun, see AUTHORS file

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
***********************************************/

/*
 * Internal C++ definitions backing arjun_c.h.
 *
 * This header is installed alongside arjun_c.h but is only meant for
 * consumers that also implement a C wrapper layered on top of Arjun
 * (e.g. ganak_c). End users should use the C API in arjun_c.h.
 */

#ifndef ARJUN_C_PRIV_HPP
#define ARJUN_C_PRIV_HPP

#include "arjun.h"
#include "arjun_c.h"

#include <cryptominisat5/solvertypesmini.h>
#include <memory>

struct arjun_fgen {
    std::unique_ptr<CMSat::FieldGen> fg;
    arjun_field_kind                 kind;
};
struct arjun_field {
    std::unique_ptr<CMSat::Field> f;
    arjun_field_kind              kind;
};
struct arjun_simpcnf {
    ArjunNS::SimplifiedCNF* cnf;
    arjun_field_kind        kind;
};
struct arjun_arjun {
    ArjunNS::Arjun* a;
};

#endif /* ARJUN_C_PRIV_HPP */
