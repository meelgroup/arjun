/*
 Arjun

 Copyright (c) 2020, Mate Soos

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
 */

#pragma once

#include "metasolver.h"
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>
#include <cadical.hpp>
#include <memory>
#include <vector>
#include <cassert>

namespace ArjunInt {

class MetaSolver2 {
public:
    explicit MetaSolver2(SolverType type = SolverType::cadical) : solver_type(type) {
        solver[0] = std::make_unique<MetaSolver>(type);
        solver[1] = std::make_unique<MetaSolver>(type);
    }

    void set_verbosity(int v) {
        solver[0]->set_verbosity(v);
        solver[1]->set_verbosity(v);
    }

    // Variable management
    void new_var() {
        solver[0]->new_var();
        solver[1]->new_var();
    }

    void new_vars(uint32_t num) {
        solver[0]->new_vars(num);
        solver[1]->new_vars(num);
    }

    uint32_t nVars() const {
        assert(solver[0]->nVars() == solver[1]->nVars());
        return solver[0]->nVars();
    }

    // Clause management
    void add_clause(const std::vector<CMSat::Lit>& cl, bool only_to_solver_0 = false) {
        solver[0]->add_clause(cl);
        if (!only_to_solver_0) solver[1]->add_clause(cl);
    }

    void add_red_clause(const std::vector<CMSat::Lit>& cl, bool only_to_solver_0 = false) {
        solver[0]->add_red_clause(cl);
        if (!only_to_solver_0) solver[1]->add_red_clause(cl);
    }

    // Solving
    CMSat::lbool solve(uint32_t num = 0) {
        return solver[num]->solve();
    }

    CMSat::lbool solve(std::vector<CMSat::Lit>* assumps, uint32_t num = 0) {
        return solver[num]->solve(assumps);
    }

    const std::vector<CMSat::lbool>& get_model(uint32_t num = 0) const {
        assert(num < 2);
        return solver[num]->get_model();
    }

    std::vector<CMSat::Lit> get_conflict(uint32_t num = 0) const {
        assert(num < 2);
        return solver[num]->get_conflict();
    }

    void simplify(std::vector<CMSat::Lit>* assumps) {
        solver[0]->simplify(assumps);
        solver[1]->simplify(assumps);
    }

    SolverType get_solver_type() const { return solver_type; }

private:
    std::array<std::unique_ptr<MetaSolver>,2> solver;
    SolverType solver_type;
};

} // namespace ArjunInt
