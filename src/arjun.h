/******************************************
Copyright (C) 2020 Mate Soos

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

#pragma once

#include <cstdint>
#include <vector>
#include <string>
#include <mpfr.h>
#include <set>
#include <fstream>
#include <gmpxx.h>
#include "cryptominisat5/solvertypesmini.h"
#ifdef CMS_LOCAL_BUILD
#include "cryptominisat.h"
#else
#include <cryptominisat5/cryptominisat.h>
#endif
struct FHolder;

namespace ArjunNS {
    struct SimpConf {
        bool oracle_extra = true;
        bool oracle_vivify = true;
        bool oracle_vivify_get_learnts = true;
        bool oracle_sparsify = true;
        int iter1 = 2;
        int iter2 = 2;
        int bve_grow_iter1 = 0;
        int bve_grow_iter2 = 6;
        bool appmc = false;
        int bve_too_large_resolvent = 12;
        int do_subs_with_resolvent_clauses = 0;
        bool do_backbone_puura = true;
    };

    struct SimplifiedCNF {
        uint32_t last_formula_var;

        std::vector<std::vector<CMSat::Lit>> clauses;
        std::vector<std::vector<CMSat::Lit>> red_clauses;
        std::vector<uint32_t> sampl_vars;
        // for minimize this is set to orig sampling set,
        // for extend, this is extended, and the weights of the extend are set to 0.5/0.5
        std::vector<uint32_t> opt_sampl_vars;
        uint32_t nvars = 0;
        mpq_class multiplier_weight = 1;
        bool proj = false;
        bool weighted = false;
        bool backbone_done = false;
        struct Weight {mpq_class pos = 1; mpq_class neg = 1;};
        std::map<uint32_t, Weight> weights;

        uint32_t nVars() const { return nvars; }
        uint32_t new_vars(uint32_t vars) { nvars+=vars; return nvars; }
        uint32_t new_var() { nvars++; return nvars; }

        void start_with_clean_sampl_vars() {
            assert(sampl_vars.empty());
            assert(opt_sampl_vars.empty());
            for(uint32_t i = 0; i < nvars; i++) sampl_vars.push_back(i);
            for(uint32_t i = 0; i < nvars; i++) opt_sampl_vars.push_back(i);
        }
        void add_xor_clause(std::vector<uint32_t>&, bool) { exit(-1); }
        void add_xor_clause(std::vector<CMSat::Lit>&, bool) { exit(-1); }
        void add_clause(std::vector<CMSat::Lit>& cl) { clauses.push_back(cl); }
        void add_red_clause(std::vector<CMSat::Lit>& cl) { red_clauses.push_back(cl); }
        bool get_sampl_vars_set() const { return sampl_vars_set; }
        bool get_opt_sampl_vars_set() const { return opt_sampl_vars_set; }
        bool sampl_vars_set = false;
        bool opt_sampl_vars_set = false;
        template<class T>
        void set_sampl_vars(const T& vars, bool ignore = false) {
            if (!ignore) {
                assert(sampl_vars.empty());
                assert(sampl_vars_set == false);
            }
            sampl_vars.clear();
            sampl_vars_set = true;
            sampl_vars.insert(sampl_vars.begin(), vars.begin(), vars.end());
            if (!opt_sampl_vars_set) set_opt_sampl_vars(vars);
        }
        const auto& get_sampl_vars() const { return sampl_vars; }
        template<class T>
        void set_opt_sampl_vars(const T& vars) {
            opt_sampl_vars.clear();
            opt_sampl_vars_set = true;
            opt_sampl_vars.insert(opt_sampl_vars.begin(), vars.begin(), vars.end());
        }

        void set_multiplier_weight(const mpq_class& m) { multiplier_weight = m; }
        auto get_multiplier_weight() const { return multiplier_weight; }
        mpq_class get_lit_weight(CMSat::Lit lit) const {
            assert(weighted);
            assert(lit.var() < nVars());
            auto it = weights.find(lit.var());
            if (it == weights.end()) return 1;
            else {
                if (!lit.sign()) return it->second.pos;
                else return it->second.neg;
            }
        }
        void unset_var_weight(uint32_t v) {
            assert(v < nVars());
            auto it = weights.find(v);
            if (it != weights.end()) weights.erase(it);
        }
        void set_lit_weight(CMSat::Lit lit, const mpq_class& w) {
            assert(weighted);
            assert(lit.var() < nVars());
            auto it = weights.find(lit.var());
            if (it == weights.end()) {
                Weight weight;
                if (lit.sign()) {weight.neg = w;weight.pos = 1.0-w;}
                else {weight.pos = w;weight.neg = 1.0-w;}
                weights[lit.var()] = weight;
                return;
            } else {
                if (!lit.sign()) it->second.pos = w;
                else it->second.neg = w;
            }
        }
        void set_weighted(bool _weighted) { weighted = _weighted; }
        void set_projected(bool _projected) { proj = _projected; }
        bool get_weighted() const { return weighted; }
        bool get_projected() const { return proj; }
        void clear_weights_for_nonprojected_vars() {
            if (!weighted) return;
            std::set<uint32_t> tmp(sampl_vars.begin(), sampl_vars.end());
            for(uint32_t i = 0; i < nVars(); i++) {
                if (tmp.count(i) == 0) unset_var_weight(i);
            }
        }

        std::vector<CMSat::Lit>& map_cl(std::vector<CMSat::Lit>& cl, std::vector<uint32_t> v_map) {
                for(auto& l: cl) l = CMSat::Lit(v_map[l.var()], l.sign());
                return cl;
        }
        std::vector<uint32_t>& map_var(std::vector<uint32_t>& cl, std::vector<uint32_t> v_map) {
            for(auto& l: cl) l = v_map[l];
            return cl;
        }
        std::set<uint32_t> map_var(const std::set<uint32_t>& cl, std::vector<uint32_t> v_map) {
            std::set<uint32_t> new_set;
            for(auto& l: cl) new_set.insert(v_map[l]);
            return new_set;
        }

        // renumber variables such that sampling set start from 0...N
        void renumber_sampling_vars_for_ganak() {
            assert(sampl_vars.size() <= opt_sampl_vars.size());
            constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
            std::vector<uint32_t> map_here_to_there(nvars, m);
            uint32_t i = 0;
            for(const auto& v: sampl_vars) {
                assert(v < nvars);
                map_here_to_there[v] = i;
                i++;
            }

            for(const auto& v: opt_sampl_vars) {
                assert(v < nvars);
                if (map_here_to_there[v] == m) {
                    map_here_to_there[v] = i;
                    i++;
                }
            }

            // Go through the rest of the variables not in sampling set.
            for(uint32_t x = 0; x < nvars; x++) {
                if (map_here_to_there[x] == m) {
                    map_here_to_there[x] = i;
                    i++;
                }
            }
            assert(i == nvars);

            // Now we renumber
            sampl_vars = map_var(sampl_vars, map_here_to_there);
            opt_sampl_vars = map_var(opt_sampl_vars, map_here_to_there);
            for(auto& cl: clauses) map_cl(cl, map_here_to_there);
            for(auto& cl: red_clauses) map_cl(cl, map_here_to_there);
            if (weighted) {
                std::map<uint32_t, Weight> new_weights;
                for(auto& w: weights)
                    new_weights[map_here_to_there[w.first]] = w.second;
                weights = new_weights;
            } else {
                assert(weights.empty());
            }
        }


        void write_simpcnf(const std::string& fname,
                    bool red = true, bool convert = false) const
        {
            uint32_t num_cls = clauses.size();
            std::ofstream outf;
            outf.open(fname.c_str(), std::ios::out);
            outf << "p cnf " << nvars << " " << num_cls << std::endl;
            if (weighted  &&  proj) outf << "c t pwmc" << std::endl;
            if (weighted  && !proj) outf << "c t wmc" << std::endl;
            if (!weighted &&  proj) outf << "c t pmc" << std::endl;
            if (!weighted && !proj) outf << "c t mc" << std::endl;
            if (weighted) {
                for(const auto& it: weights) {
                    outf << "c p weight " << CMSat::Lit(it.first,false) << " ";
                    if (convert) {
                        mpf_class pos = it.second.pos;
                        outf << pos << " 0" << std::endl;
                    } else {
                        outf << it.second.pos << " 0" << std::endl;
                    }
                    outf << "c p weight " << CMSat::Lit(it.first,true) << " ";
                    if (convert) {
                        mpf_class neg = it.second.neg;
                        outf << neg << " 0" << std::endl;
                    } else {
                        outf << it.second.neg << " 0" << std::endl;
                    }
                }
            }

            for(const auto& cl: clauses) outf << cl << " 0\n";
            if (red) for(const auto& cl: red_clauses)
                outf << "c red " << cl << " 0\n";

            //Add projection
            outf << "c p show ";
            auto sampl = sampl_vars;
            std::sort(sampl.begin(), sampl.end());
            for(const auto& v: sampl) {
                assert(v < nvars);
                outf << v+1  << " ";
            }
            outf << "0\n";
            outf << "c p optshow ";
            sampl = opt_sampl_vars;
            std::sort(sampl.begin(), sampl.end());
            for(const auto& v: sampl) {
                assert(v < nvars);
                outf << v+1  << " ";
            }
            outf << "0\n";
            outf << "c MUST MULTIPLY BY " << multiplier_weight << std::endl;
        }

        bool weight_set(uint32_t v) const {
            return weights.count(v) > 0;
        }

        void remove_equiv_weights() {
            if (!weighted) return;

            bool debug_w = false;
            std::set<uint32_t> tmp(opt_sampl_vars.begin(), opt_sampl_vars.end());
            for(uint32_t i = 0; i < nvars; i++) {
                CMSat::Lit l(i, false);
                if (tmp.count(i) == 0) continue;

                if (weights.count(l.var()) && get_lit_weight(l) == get_lit_weight(~l)) {
                    if (debug_w)
                        std::cout << __FUNCTION__ << " Removing equiv weight for " << l
                            << " get_lit_weight(l): " << get_lit_weight(l) << std::endl;
                    multiplier_weight *= get_lit_weight(l);
                    unset_var_weight(i);
                }
            }
        }

        void fix_weights(CMSat::SATSolver* solver,
                const std::vector<uint32_t> new_sampl_vars,
                const std::vector<uint32_t>& empty_sampling_vars) {
            std::set<uint32_t> sampling_vars_set(new_sampl_vars.begin(), new_sampl_vars.end());
            std::set<uint32_t> opt_sampling_vars_set(opt_sampl_vars.begin(), opt_sampl_vars.end());
            bool debug_w = false;

            // Take units
            for(const auto& l: solver->get_zero_assigned_lits()) {
                if (l.var() >= nVars()) continue;
                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] orig unit l: " << l << " w: " << get_lit_weight(l) << std::endl;
                sampling_vars_set.erase(l.var());
                opt_sampling_vars_set.erase(l.var());
                if (get_weighted()) {
                    multiplier_weight *= get_lit_weight(l);
                    if (debug_w)
                        std::cout << __FUNCTION__ << " [w-debug] unit: " << l << " multiplier_weight: " << multiplier_weight << std::endl;
                    unset_var_weight(l.var());
                }
            }

            // Take bin XORs
            // [ replaced, replaced_with ]
            const auto eq_lits = solver->get_all_binary_xors();
            for(auto p: eq_lits) {
                if (p.first.var() >= nVars() || p.second.var() >= nVars()) continue;
                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] repl: " << p.first << " with " << p.second << std::endl;
                if (get_weighted()) {
                    auto wp2 = get_lit_weight(p.second);
                    auto wn2 = get_lit_weight(~p.second);
                    auto wp1 = get_lit_weight(p.first);
                    auto wn1 = get_lit_weight(~p.first);
                    if (debug_w) {
                        std::cout << __FUNCTION__ << " [w-debug] wp1 " << wp1 << " wn1 " << wn1 << std::endl;
                        std::cout << __FUNCTION__ << " [w-debug] wp2 " << wp2 << " wn2 " << wn2 << std::endl;
                    }
                    wp2 *= wp1;
                    wn2 *= wn1;
                    set_lit_weight(p.second, wp2);
                    set_lit_weight(~p.second, wn2);
                    if (debug_w) {
                        std::cout << __FUNCTION__ << " [w-debug] set lit " << p.second << " weight to " << wp2 << std::endl;
                        std::cout << __FUNCTION__ << " [w-debug] set lit " << ~p.second << " weight to " << wn2 << std::endl;
                    }
                    unset_var_weight(p.first.var());
                }
            }

            set_sampl_vars(sampling_vars_set, true);
            set_opt_sampl_vars(opt_sampling_vars_set);

            solver->start_getting_constraints(false);
            sampl_vars = solver->translate_sampl_set(new_sampl_vars, true);
            opt_sampl_vars = solver->translate_sampl_set(opt_sampl_vars, true);
            auto empty_sampling_vars2 = solver->translate_sampl_set(empty_sampling_vars, true);
            solver->end_getting_constraints();

            sampling_vars_set.clear();
            sampling_vars_set.insert(sampl_vars.begin(), sampl_vars.end());
            opt_sampling_vars_set.clear();
            opt_sampling_vars_set.insert(opt_sampl_vars.begin(), opt_sampl_vars.end());
            for(const auto& v: empty_sampling_vars2) {
                sampling_vars_set.erase(v);
                opt_sampling_vars_set.erase(v);

                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] empty sampling var: " << v+1 << std::endl;
                mpq_class tmp(0);
                if (get_weighted()) {
                    CMSat::Lit l(v, false);
                    tmp += get_lit_weight(l);
                    tmp += get_lit_weight(~l);
                    unset_var_weight(l.var());
                } else tmp = 2;
                multiplier_weight *= tmp;
                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] empty mul: " << tmp << " final multiplier_weight: " << multiplier_weight << std::endl;
            }

            set_sampl_vars(sampling_vars_set, true);
            set_opt_sampl_vars(opt_sampling_vars_set);

            for(uint32_t i = 0; i < nVars(); i++) {
                if (opt_sampling_vars_set.count(i) == 0) unset_var_weight(i);
            }

            if (debug_w) {
                std::cout << "w-debug FINAL sampl_vars    : ";
                for(const auto& v: sampl_vars) {
                    std::cout << v+1 << " ";
                }
                std::cout << std::endl;
                std::cout << "w-debug FINAL opt_sampl_vars: ";
                for(const auto& v: opt_sampl_vars) {
                    std::cout << v+1 << " ";
                }
                std::cout << std::endl;
            }
        }
    };

    struct ArjPrivateData;
    #ifdef _WIN32
    class __declspec(dllexport) Arjun
    #else
    class Arjun
    #endif
    {
    public:
        Arjun();
        ~Arjun();
        static std::string get_version_info();
        static std::string get_sbva_version_info();
        static std::string get_compilation_env();
        static std::string get_solver_version_info();

        // Perform indep set calculation
        void standalone_minimize_indep(SimplifiedCNF& cnf);
        void standalone_minimize_indep_synt(SimplifiedCNF& cnf);
        void standalone_extend_sampl_set(SimplifiedCNF& cnf);
        void standalone_unsat_define(SimplifiedCNF& cnf);
        void standalone_unate(SimplifiedCNF& cnf);

        struct ElimToFileConf {
            bool all_indep = false;
            bool do_extend_indep = true;
            bool do_bce = true;
            bool do_unate = false;
            int num_sbva_steps = 1;
            uint32_t sbva_cls_cutoff = 4;
            uint32_t sbva_lits_cutoff = 5;
            int sbva_tiebreak = 1;
            bool do_renumber = true;
        };
        void standalone_elim_to_file(SimplifiedCNF& cnf,
                const ElimToFileConf& etof_conf, const SimpConf& simp_conf);
        SimplifiedCNF only_get_simplified_cnf(const SimplifiedCNF& cnf, const SimpConf& simp_conf);
        void standalone_bce(SimplifiedCNF& cnf);
        void standalone_rev_bce(SimplifiedCNF& cnf);
        void standalone_backbone(SimplifiedCNF& cnf);
        void standalone_sbva(SimplifiedCNF& orig,
            int64_t sbva_steps = 200, uint32_t sbva_cls_cutoff = 2,
            uint32_t sbva_lits_cutoff = 2, int sbva_tiebreak = 1);
        SimplifiedCNF standalone_manthan(const SimplifiedCNF& cnf);

        //Set config
        void set_verb(uint32_t verb);
        void set_distill(bool distill);
        void set_intree(bool intree);
        void set_simp(int simp);
        void set_bve_pre_simplify(bool bve_pre_simp);
        void set_incidence_count(uint32_t incidence_count);
        void set_or_gate_based(bool or_gate_based);
        void set_xor_gates_based(bool xor_gates_based);
        void set_probe_based(bool probe_based);
        void set_backward(bool backward);
        void set_backw_max_confl(uint32_t backw_max_confl);
        void set_gauss_jordan(bool gauss_jordan);
        void set_find_xors(bool find_xors);
        void set_ite_gate_based(bool ite_gate_based);
        void set_do_unate(bool do_unate);
        void set_irreg_gate_based(const bool irreg_gate_based);
        //void set_polar_mode(CMSat::PolarityMode mode);
        void set_no_gates_below(double no_gates_below);
        void set_specified_order_fname(std::string specified_order_fname);
        void set_weighted(const bool);
        void set_extend_max_confl(uint32_t extend_max_confl);
        void set_backbone_only_optindep(bool backbone_only_optindep);
        void set_oracle_find_bins(int oracle_find_bins);
        void set_num_samples(int num_samples);
        void set_cms_mult(double cms_mult);

        //Get config
        uint32_t get_verb() const;
        bool get_do_unate() const;
        std::string get_specified_order_fname() const;
        double get_no_gates_below() const;
        int get_simp() const;
        bool get_distill() const;
        bool get_intree() const;
        bool get_bve_pre_simplify() const;
        uint32_t get_incidence_count() const;
        bool get_or_gate_based() const;
        bool get_xor_gates_based() const;
        bool get_probe_based() const;
        bool get_backward() const;
        uint32_t get_backw_max_confl() const;
        bool get_gauss_jordan() const;
        bool get_find_xors() const;
        bool get_ite_gate_based() const;
        bool get_irreg_gate_based() const;
        uint32_t get_extend_max_confl() const;
        bool get_backbone_only_optindep() const;
        int get_num_samples() const;
        int get_oracle_find_bins() const;
        double get_cms_mult() const;

    private:
        ArjPrivateData* arjdata = nullptr;
    };
}
