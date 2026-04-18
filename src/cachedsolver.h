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

#include <cryptominisat5/solvertypesmini.h>
#include "metasolver.h"
#include <random>
#include <vector>
#include <memory>

namespace ArjunInt {

class CachedSolver {
public:
    explicit CachedSolver(SolverType type = SolverType::cadical, size_t _max_cache_size = 10000)
        : solver(std::make_unique<MetaSolver>(type)), rng(42),
        max_cache_size(_max_cache_size) {}

    void set_verbosity(int v) { solver->set_verbosity(v); }
    void new_var() {
        clear_cache();
        solver->new_var();
    }

    void new_vars(uint32_t num) {
        clear_cache();
        solver->new_vars(num);
    }

    uint32_t nVars() const { return solver->nVars(); }
    void add_clause(const std::vector<CMSat::Lit>& cl) {
        clear_cache();
        solver->add_clause(cl);
    }

    void add_red_clause(const std::vector<CMSat::Lit>& cl) {
        clear_cache();
        solver->add_red_clause(cl);
    }

    std::vector<CMSat::lbool>* add_solution(const std::vector<CMSat::lbool>& model) {
        if (max_cache_size == 0) {
            cache.resize(1);
            cache[0] = model;
            return &cache[0];
        }
        if (cache.size() >= max_cache_size) {
            std::shuffle(cache.begin(), cache.end(), rng);
            cache.resize(max_cache_size / 2);
        }
        std::vector<CMSat::lbool> sol(model);
        cache.push_back(std::move(sol));
        return &cache.back();
    }

    CMSat::lbool solve() {
        return solve(nullptr);
    }

    bool find_in_cache(std::vector<CMSat::Lit>* assumps) {
        if (max_cache_size == 0) return false;
        if (assumps == nullptr || assumps->empty()) {
            if (!cache.empty()) {
                solution = &cache[0];
                cache_hits++;
                return true;
            }
            return false;
        }

        for (auto& sol : cache) {
            bool match = true;
            for (const auto& l : *assumps) {
                if (sol[l.var()] != CMSat::boolToLBool(!l.sign())) {
                    match = false;
                    break;
                }
            }
            if (match) {
                solution = &sol;
                cache_hits++;
                return true;
            }
        }
        cache_misses++;
        return false;
    }

    CMSat::lbool solve(std::vector<CMSat::Lit>* assumps) {
        if (find_in_cache(assumps)) {
            return CMSat::l_True;
        }

        solution = nullptr;
        auto ret = solver->solve(assumps);
        if (ret == CMSat::l_True) {
            solution = add_solution(solver->get_model());
        }
        return ret;

    }

    const std::vector<CMSat::lbool>& get_model() const {
        if (solution != nullptr) {
            return *solution;
        }
        return solver->get_model();
    }

    double get_cache_hit_rate() const {
        const uint64_t total = cache_hits + cache_misses;
        if (total == 0) return 0.0;
        return static_cast<double>(cache_hits) / static_cast<double>(total);
    }

    std::vector<CMSat::Lit> get_conflict() const { return solver->get_conflict(); }
    void set_max_confl(int64_t max_confl) { solver->set_max_confl(max_confl); }
    void simplify(std::vector<CMSat::Lit>* assumps) { solver->simplify(assumps); }
    SolverType get_solver_type() const { return solver->get_solver_type(); }
    void clear_cache() { cache.clear(); }
    size_t cache_size() const { return cache.size(); }

private:
    uint64_t cache_hits = 0;
    uint64_t cache_misses = 0;
    std::vector<CMSat::lbool>* solution = nullptr;
    std::vector<std::vector<CMSat::lbool>> cache;
    std::unique_ptr<MetaSolver> solver;
    std::mt19937 rng;
    size_t max_cache_size;
};

} // namespace ArjunInt
