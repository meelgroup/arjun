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

#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>
#include <cadical.hpp>
#include <memory>
#include <vector>
#include <cassert>

namespace ArjunInt {

enum class SolverType {
    cms = 0,
    cadical = 1
};

// MetaSolver wraps either CryptoMiniSat or CaDiCaL, providing a unified interface
class MetaSolver {
public:
    explicit MetaSolver(SolverType type = SolverType::cms) : solver_type(type) {
        if (solver_type == SolverType::cms) {
            cms = std::make_unique<CMSat::SATSolver>();
            cms->set_prefix("c o ");
        } else {
            cadical = std::make_unique<CaDiCaL::Solver>();
            cadical_nvars = 0;
            cadical->prefix("c o ");
        }
    }

    void set_verbosity(int v) {
        if (solver_type == SolverType::cms) cms->set_verbosity(v);
    }

    // Variable management
    void new_var() {
        if (solver_type == SolverType::cms) cms->new_var();
        else cadical_nvars++;
    }

    void new_vars(uint32_t num) {
        if (solver_type == SolverType::cms) cms->new_vars(num);
        else cadical_nvars += num;
    }

    uint32_t nVars() const {
        if (solver_type == SolverType::cms) return cms->nVars();
        else return cadical_nvars;
    }

    // Clause management
    void add_clause(const std::vector<CMSat::Lit>& cl) {
        if (solver_type == SolverType::cms) cms->add_clause(cl);
        else {
            for (const auto& l : cl) cadical->add(lit_to_cadical(l));
            cadical->add(0);
        }
    }

    void add_red_clause(const std::vector<CMSat::Lit>& cl) {
        if (solver_type == SolverType::cms) cms->add_red_clause(cl);
        else {
            // CaDiCaL doesn't distinguish redundant clauses, so skip
            /* for (const auto& l : cl) cadical->add(lit_to_cadical(l)); */
            /* cadical->add(0); */
        }
    }

    // Solving
    CMSat::lbool solve() {
        if (solver_type == SolverType::cms) return cms->solve();
        else {
            auto status = cadical->solve();
            cadical_model.clear();
            cadical_conflict.clear();
            if (status == CaDiCaL::Status::SATISFIABLE) {
                cadical_model.resize(cadical_nvars);
                for (uint32_t i = 0; i < cadical_nvars; i++) {
                    int val = cadical->val(i + 1);
                    if (val > 0) cadical_model[i] = CMSat::l_True;
                    else if (val < 0) cadical_model[i] = CMSat::l_False;
                    else cadical_model[i] = CMSat::l_Undef;
                }
                return CMSat::l_True;
            } else if (status == CaDiCaL::Status::UNSATISFIABLE) {
                return CMSat::l_False;
            }
            return CMSat::l_Undef;
        }
    }

    CMSat::lbool solve(std::vector<CMSat::Lit>* assumps) {
        if (solver_type == SolverType::cms) return cms->solve(assumps);
        else {
            if (assumps)
                for (const auto& l : *assumps) cadical->assume(lit_to_cadical(l));
            auto status = cadical->solve();
            cadical_model.clear();
            cadical_conflict.clear();
            if (status == CaDiCaL::Status::SATISFIABLE) {
                cadical_model.resize(cadical_nvars);
                for (uint32_t i = 0; i < cadical_nvars; i++) {
                    int val = cadical->val(i + 1);
                    if (val > 0) cadical_model[i] = CMSat::l_True;
                    else if (val < 0) cadical_model[i] = CMSat::l_False;
                    else cadical_model[i] = CMSat::l_Undef;
                }
                return CMSat::l_True;
            } else if (status == CaDiCaL::Status::UNSATISFIABLE) {
                if (assumps) {
                    for (const auto& l : *assumps) {
                        if (cadical->failed(lit_to_cadical(l))) cadical_conflict.push_back(~l);
                    }
                }
                return CMSat::l_False;
            }
            return CMSat::l_Undef;
        }
    }

    // Model/Conflict access
    const std::vector<CMSat::lbool>& get_model() const {
        if (solver_type == SolverType::cms) return cms->get_model();
        else return cadical_model;
    }

    std::vector<CMSat::Lit> get_conflict() const {
        if (solver_type == SolverType::cms) return cms->get_conflict();
        else return cadical_conflict;
    }

    void simplify(std::vector<CMSat::Lit>* assumps) {
        if (solver_type == SolverType::cms) cms->simplify(assumps);
    }

    SolverType get_solver_type() const { return solver_type; }

    // Access underlying solver for special operations
    CMSat::SATSolver* get_cms() {
        assert(solver_type == SolverType::cms);
        return cms.get();
    }

    CaDiCaL::Solver* get_cadical() {
        assert(solver_type == SolverType::cadical);
        return cadical.get();
    }

private:
    SolverType solver_type;
    std::unique_ptr<CMSat::SATSolver> cms;
    std::unique_ptr<CaDiCaL::Solver> cadical;
    uint32_t cadical_nvars = 0;
    mutable std::vector<CMSat::lbool> cadical_model;
    mutable std::vector<CMSat::Lit> cadical_conflict;

    // Convert CMSat::Lit to CaDiCaL int format
    // CaDiCaL uses 1-indexed variables, positive for positive literal, negative for negated
    static int lit_to_cadical(CMSat::Lit l) {
        int v = l.var() + 1;  // 1-indexed
        return l.sign() ? -v : v;
    }

    // Convert CaDiCaL int to CMSat::Lit
    static CMSat::Lit cadical_to_lit(int l) {
        uint32_t var = std::abs(l) - 1;  // 0-indexed
        return CMSat::Lit(var, l < 0);
    }
};

} // namespace ArjunInt
