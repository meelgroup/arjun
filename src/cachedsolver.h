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
#include <map>
#include <algorithm>

namespace ArjunInt {

class CachedSolver {
public:
    explicit CachedSolver(SolverType type = SolverType::cms)
        : solver(std::make_unique<MetaSolver>(type)) {}

    void set_verbosity(int v) {
        solver->set_verbosity(v);
    }

    void new_var() {
        clear_cache();
        solver->new_var();
    }

    void new_vars(uint32_t num) {
        clear_cache();
        solver->new_vars(num);
    }

    uint32_t nVars() const {
        return solver->nVars();
    }

    void add_clause(const std::vector<CMSat::Lit>& cl) {
        clear_cache();
        solver->add_clause(cl);
    }

    void add_red_clause(const std::vector<CMSat::Lit>& cl) {
        clear_cache();
        solver->add_red_clause(cl);
    }

    CMSat::lbool solve() {
        return solver->solve();
    }

    CMSat::lbool solve(std::vector<CMSat::Lit>* assumps) {
        if (assumps == nullptr) {
            return solver->solve();
        }

        std::vector<CMSat::Lit> key = *assumps;
        std::sort(key.begin(), key.end());

        auto it = cache.find(key);
        if (it != cache.end()) {
            cached_result = it->second;
            return cached_result.result;
        }

        CMSat::lbool result = solver->solve(assumps);

        CachedResult entry;
        entry.result = result;
        if (result == CMSat::l_True) {
            entry.model = solver->get_model();
        } else if (result == CMSat::l_False) {
            entry.conflict = solver->get_conflict();
        }
        cache[key] = entry;
        cached_result = entry;

        return result;
    }

    const std::vector<CMSat::lbool>& get_model() const {
        if (!cached_result.model.empty()) {
            return cached_result.model;
        }
        return solver->get_model();
    }

    std::vector<CMSat::Lit> get_conflict() const {
        if (!cached_result.conflict.empty()) {
            return cached_result.conflict;
        }
        return solver->get_conflict();
    }

    void simplify(std::vector<CMSat::Lit>* assumps) {
        clear_cache();
        solver->simplify(assumps);
    }

    SolverType get_solver_type() const {
        return solver->get_solver_type();
    }

    CMSat::SATSolver* get_cms() {
        return solver->get_cms();
    }

    CaDiCaL::Solver* get_cadical() {
        return solver->get_cadical();
    }

    void clear_cache() {
        cache.clear();
        cached_result = CachedResult();
    }

    size_t cache_size() const {
        return cache.size();
    }

private:
    struct CachedResult {
        CMSat::lbool result = CMSat::l_Undef;
        std::vector<CMSat::lbool> model;
        std::vector<CMSat::Lit> conflict;
    };

    std::unique_ptr<MetaSolver> solver;
    std::map<std::vector<CMSat::Lit>, CachedResult> cache;
    mutable CachedResult cached_result;
};

} // namespace ArjunInt
