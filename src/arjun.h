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
#include <memory>
#include <vector>
#include <string>
#include <map>
#include <set>
#include <fstream>
#include <gmpxx.h>
#include "cryptominisat5/solvertypesmini.h"
#include <cryptominisat5/cryptominisat.h>
struct FHolder;


enum AIGT {t_and, t_lit, t_const};
struct AIG {
    AIG(uint64_t _id = 0) : id(_id) {}
    AIG() = delete;
    AIGT type = t_const;
    uint32_t var = std::numeric_limits<uint32_t>::max();
    bool neg = false;
    AIG* l = nullptr;
    AIG* r = nullptr;
    uint64_t id = 0;

    bool invariants() const {
        if (type == t_lit) {
            return l == nullptr && r == nullptr && var != std::numeric_limits<uint32_t>::max();
        }
        if (type == t_const) {
            return l == nullptr && r == nullptr && var == std::numeric_limits<uint32_t>::max();
        }
        if (type == t_and) {
            return l != nullptr && r != nullptr && var == std::numeric_limits<uint32_t>::max();
        }
        assert(false && "Unknown AIG type");
    }
};

inline bool evaluate(const std::vector<CMSat::lbool>& vals, const AIG* aig, const std::map<uint32_t, AIG*>& defs) {
    assert(aig->invariants());
    if (aig->type == t_lit) {
        if (defs.find(aig->var) != defs.end()) {
            // NOTE: this is highly inefficient, because this should be cached
            assert(vals.size() < aig->var || vals[aig->var] == CMSat::l_Undef); // Must not be part of input
            return aig->neg ^ evaluate(vals, defs.at(aig->var), defs);
        } else {
            assert(aig->var < vals.size());
            assert(vals[aig->var] != CMSat::l_Undef);
            bool ret = vals[aig->var] == CMSat::l_True;
            ret ^= aig->neg;
            return ret;
        }
    }

    if (aig->type == t_const) return aig->neg == false;

    if (aig->type == t_and) {
        const bool l = evaluate(vals, aig->l, defs);
        const bool r = evaluate(vals, aig->r, defs);
        bool ret = l && r;
        if (aig->neg) ret = !ret;
        return ret;
    }
    assert(false && "Unknown AIG type");
}

struct AIGManager {
    AIGManager() {
        const_true = new AIG(max_id++);
        const_true->type = t_const;
        const_true->neg = false;
        aigs.push_back(const_true);

        const_false = new_not(const_true);
    }

    AIG* copy_aig(AIG* aig, std::map<uint64_t, AIG*>& old_id_to_new_aig) {
        if (aig == nullptr) return nullptr;
        assert(aig->invariants());
        if (old_id_to_new_aig.count(aig->id)) return old_id_to_new_aig.at(aig->id);

        AIG* new_aig = new AIG(max_id++);
        new_aig->type = aig->type;
        new_aig->var = aig->var;
        new_aig->neg = aig->neg;
        new_aig->l = copy_aig(aig->l, old_id_to_new_aig);
        new_aig->r = copy_aig(aig->r, old_id_to_new_aig);
        aigs.push_back(new_aig);
        old_id_to_new_aig[aig->id] = new_aig;
        return new_aig;
    }

    AIGManager& operator=(const AIGManager& other) {
        replace_with(other);
        return *this;
    }

    std::map<uint64_t, AIG*> replace_with(const AIGManager& other) {
        for(auto aig: aigs) delete aig;
        aigs.clear();
        lit_to_aig.clear();
        const_true = nullptr;
        const_false = nullptr;
        max_id = 0;

        std::map<uint64_t, AIG*> old_id_to_new_aig;
        assert(aigs.empty());
        for (auto aig : other.aigs) copy_aig(aig, old_id_to_new_aig);
        const_true = old_id_to_new_aig.at(other.const_true->id);
        const_false = old_id_to_new_aig.at(other.const_false->id);
        max_id = other.max_id;

        assert(lit_to_aig.empty());
        for (auto& it : other.lit_to_aig)
            lit_to_aig[it.first] = old_id_to_new_aig.at(it.second->id);

        return old_id_to_new_aig;
    }

    AIGManager(const AIGManager& other) {
        *this = other;
    }

    std::map<uint64_t, AIG*> append_aigs_to(AIGManager& other) const {
        std::map<uint64_t, AIG*> old_id_to_new_aig;
        for (auto aig : aigs) other.copy_aig(aig, old_id_to_new_aig);
        for(auto& it: lit_to_aig) {
            // NOTE: we may be overriding old ones. It's fine, we can have duplicates
            other.lit_to_aig[it.first] = old_id_to_new_aig.at(it.second->id);
        }
        // No need to copy const_true and const_false
        return old_id_to_new_aig;
    }

    ~AIGManager() {
        for (auto aig : aigs) delete aig;
        max_id = 0;
    }


    AIG* new_lit(CMSat::Lit l) {
        return new_lit(l.var(), l.sign());
    }

    AIG* new_lit(uint32_t var, bool neg = false) {
        if (lit_to_aig.count(CMSat::Lit(var, neg))) {
            return lit_to_aig.at(CMSat::Lit(var, neg));
        }
        AIG* ret = new AIG(max_id++);
        ret->type = t_lit;
        ret->var = var;
        ret->neg = neg;
        aigs.push_back(ret);
        lit_to_aig[CMSat::Lit(var, neg)] = ret;

        return ret;
    }

    AIG* new_const(bool val) {
        return val ? const_true : const_false;
    }

    AIG* new_not(AIG* a) {
        AIG* ret = new AIG(max_id++);
        ret->type = t_and;
        ret->l = a;
        ret->r = a;

        ret->neg = true;
        aigs.push_back(ret);
        return ret;
    }

    AIG* new_and(AIG* l, AIG* r) {
        AIG* ret = new AIG(max_id++);
        ret->type = t_and;
        ret->l = l;
        ret->r = r;
        aigs.push_back(ret);
        return ret;
    }

    AIG* new_or(AIG* l, AIG* r) {
        AIG* ret = new AIG(max_id++);
        ret->type = t_and;
        ret->neg = true;
        ret->l = new_not(l);
        ret->r = new_not(r);
        aigs.push_back(ret);
        return ret;
    }

    AIG* new_ite(AIG* l, AIG* r, AIG* b) {
        return new_or(new_and(b, l), new_and(new_not(b), r));
    }

    AIG* new_ite(AIG* l, AIG* r, CMSat::Lit b) {
        auto b_aig = new_lit(b.var(), b.sign());
        return new_or(new_and(b_aig, l), new_and(new_not(b_aig), r));
    }

    std::vector<AIG*> aigs;
    // A map from lit to AIG. This is just a lookup -- it is NOT guaranteed
    // there aren't any other AIGs that are this lit. Due to copying, there may
    // well be. So we DON'T guarantee uniqueness
    std::map<CMSat::Lit, AIG*> lit_to_aig;
    // There could be other const true, this is just a good example so we don't always copy
    // Due to copying we don'g guarantee uniqueness
    AIG* const_true = nullptr;
    // There could be other const false, this is just a good example so we don't always copy
    // Due to copying we don'g guarantee uniqueness
    AIG* const_false = nullptr;
    uint64_t max_id = 0;
};

namespace ArjunNS {

class FMpq : public CMSat::Field {
public:
    mpq_class val;
    FMpq() : val(0) {}
    FMpq(const int _val) : val(_val) {}
    FMpq(const mpz_class& _val) : val(_val) {}
    FMpq(const mpq_class& _val) : val(_val) {}
    FMpq(const FMpq& other) : val(other.val) {}
    const mpq_class& get_val() const { return val; }

    Field& operator=(const Field& other) override {
        const auto& od = dynamic_cast<const FMpq&>(other);
        val = od.val;
        return *this;
    }

    Field& operator+=(const Field& other) override {
        const auto& od = dynamic_cast<const FMpq&>(other);
        val += od.val;
        return *this;
    }

    std::unique_ptr<Field> add(const Field& other) override {
        const auto& od = dynamic_cast<const FMpq&>(other);
        return std::make_unique<FMpq>(val + od.val);
    }

    Field& operator-=(const Field& other) override {
        const auto& od = dynamic_cast<const FMpq&>(other);
        val -= od.val;
        return *this;
    }

    Field& operator*=(const Field& other) override {
        const auto& od = dynamic_cast<const FMpq&>(other);
        val *= od.val;
        return *this;
    }

    Field& operator/=(const Field& other) override {
        const auto& od = dynamic_cast<const FMpq&>(other);
        if (od.val == 0) throw std::runtime_error("Division by zero");
        val /= od.val;
        return *this;
    }

    bool operator==(const Field& other) const override {
        const auto& od = dynamic_cast<const FMpq&>(other);
        return val == od.val;
    }

    std::ostream& display(std::ostream& os) const override {
        os << val;
        return os;
    }

    std::unique_ptr<Field> dup() const override {
        return std::make_unique<FMpq>(val);
    }

    bool is_zero() const override {
        return val == 0;
    }

    bool is_one() const override {
        return val == 1;
    }

    bool parse(const std::string& str, const uint32_t line_no) override {
        uint32_t at = 0;
        if (!parse_mpq(str, at, line_no)) return false;
        return check_end_of_weight(str, at, line_no);
    }

    void set_zero() override { val = 0; }
    void set_one() override { val = 1; }

    inline uint64_t helper(const mpz_class& v) const {
      return v.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
    }

    uint64_t bytes_used() const override {
      return sizeof(mpq_class) +
          helper(val.get_num()) + helper(val.get_den());
    }

    bool parse_mpq(const std::string& str, uint32_t& at, const uint32_t line_no) {
        skip_whitespace(str, at);
        mpz_class head;
        auto sign = parse_sign(str, at);
        if (!parse_int(head, str, at, line_no)) return false;
        bool rational = false;
        if (str[at] == '.') {
            at++;
            mpz_class tail;
            int len = 0;
            if (!parse_int(tail, str, at, line_no, &len)) return false;
            mpz_class ten(10);
            mpz_ui_pow_ui(ten.get_mpz_t(), 10, len);
            mpq_class tenq(ten);
            mpq_class tailq(tail);
            val = mpq_class(head) + tailq/tenq;
        } else if (str[at] == '/') {
            at++;
            rational = true;
            mpz_class tail;
            if (!parse_int(tail, str, at, line_no)) return false;
            val = mpq_class(head)/mpq_class(tail);
        } else {
            val = head;
        }

        if (str[at] == 'e' || str[at] == 'E') {
            if (rational) {
                std::cerr << "PARSE ERROR! You can't have BOTH rational AND exponent"
                << " At line " << line_no << " Probably looks like 1/2e-4"
                << std::endl;
                return false;
            }
            at++;
            mpz_class exp;
            auto sign2 = parse_sign(str, at);
            if (!parse_int(exp, str, at, line_no)) return false;
            exp*=sign2;
            if (!exp.fits_sint_p()) {
                std::cerr << "PARSE ERROR! Exponent too large for int64_t"
                << " At line " << line_no << " Probably looks like 1e100" << std::endl;
                return false;
            }
            int64_t ex = exp.get_si();
            mpz_class x(1);
            if (ex < 0) {
                ex *=-1;
                mpz_pow_ui(x.get_mpz_t(), mpz_class(10).get_mpz_t(), ex);
                val /= x;
            } else {
                mpz_pow_ui(x.get_mpz_t(), mpz_class(10).get_mpz_t(), ex);
                val *=x;
            }
        }
        val *= sign;
        return true;
    }
};

class FGenMpq : public CMSat::FieldGen {
public:
    ~FGenMpq() override = default;
    std::unique_ptr<CMSat::Field> zero() const override {
        return std::make_unique<FMpq>(0);
    }

    std::unique_ptr<CMSat::Field> one() const override {
        return std::make_unique<FMpq>(1.0);
    }

    std::unique_ptr<FieldGen> dup() const override {
        return std::make_unique<FGenMpq>();
    }

    bool weighted() const override { return true; }
};


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
        std::unique_ptr<CMSat::FieldGen> fg = nullptr;
        SimplifiedCNF(const std::unique_ptr<CMSat::FieldGen>& _fg) : fg(_fg->dup()), multiplier_weight(fg->one()) {}
        SimplifiedCNF(const CMSat::FieldGen* _fg) : fg(_fg->dup()), multiplier_weight(fg->one()) {}
        ~SimplifiedCNF() = default;

        bool need_aig = false;
        std::vector<std::vector<CMSat::Lit>> clauses;
        std::vector<std::vector<CMSat::Lit>> red_clauses;
        bool proj = false;
        bool sampl_vars_set = false;
        bool opt_sampl_vars_set = false;
        std::vector<uint32_t> sampl_vars;
        std::vector<uint32_t> opt_sampl_vars; // Filled during synthesis with vars that have been defined already

        uint32_t nvars = 0;
        std::unique_ptr<CMSat::Field> multiplier_weight = nullptr;
        bool weighted = false;
        bool backbone_done = false;
        struct Weight {
            Weight() = default;
            std::unique_ptr<CMSat::Field> pos;
            std::unique_ptr<CMSat::Field> neg;
            Weight(std::unique_ptr<CMSat::FieldGen>& fg) : pos(fg->one()), neg(fg->one()) {}

            Weight(const Weight& other) :
                pos (other.pos->dup()),
                neg (other.neg->dup()) {}
            Weight& operator=(const Weight& other) {
                pos = other.pos->dup();
                neg = other.neg->dup();
                return *this;
            }
        };
        std::map<uint32_t, Weight> weights;
        std::map<uint32_t, CMSat::VarMap> orig_to_new_var;
        AIGManager aig_mng;
        std::map<uint32_t, AIG*> defs; //definition of variables in terms of AIG. ORIGINAL number space

        SimplifiedCNF& operator=(const SimplifiedCNF& other) {
            fg = other.fg->dup();
            need_aig = other.need_aig;
            clauses = other.clauses;
            red_clauses = other.red_clauses;
            proj = other.proj;
            sampl_vars_set = other.sampl_vars_set;
            opt_sampl_vars_set = other.opt_sampl_vars_set;
            sampl_vars = other.sampl_vars;
            opt_sampl_vars = other.opt_sampl_vars;
            nvars = other.nvars;
            multiplier_weight = other.multiplier_weight->dup();
            weighted = other.weighted;
            backbone_done = other.backbone_done;
            weights = other.weights;
            orig_to_new_var = other.orig_to_new_var;
            replace_aigs_from(other);

            return *this;
        }

        void replace_aigs_from(const SimplifiedCNF& other) {
            if (!need_aig) {
                assert(!other.need_aig);
                assert(other.aig_mng.aigs.size() == 2 && other.defs.empty());
                return;
            }

            // Copy AIGs
            aig_mng = other.aig_mng;
            std::map<uint64_t, AIG*> id_to_aig;
            for(const auto& aig: aig_mng.aigs) id_to_aig[aig->id] = aig;

            // Copy defs
            defs.clear();
            for(const auto& it: other.defs) {
                assert(id_to_aig.count(it.second->id) && "Must have already been copied");
                defs[it.first] = id_to_aig[it.second->id];
            }
        }

        void add_aigs_from(const AIGManager& other, const std::map<uint32_t, AIG*>& other_defs) {
            if (!need_aig) {
                assert(aig_mng.aigs.size() == 2 && defs.empty());
                return;
            }
            auto old_id_to_new_aig = other.append_aigs_to(aig_mng);

            for(const auto& it: other_defs) {
                assert(defs.find(it.first) == defs.end() && "Must not already be defined here");
                assert(old_id_to_new_aig.count(it.second->id) && "Must have already been copied");
                defs[it.first] = old_id_to_new_aig[it.second->id];
            }
        }

        SimplifiedCNF(const SimplifiedCNF& other) {
            *this = other;
        }

        // Gives all the orig lits that map to this variable
        std::map<uint32_t, std::vector<CMSat::Lit>> get_new_to_orig_var_list() const {
            std::map<uint32_t, std::vector<CMSat::Lit>> ret;
            for(const auto& p: orig_to_new_var) {
                const CMSat::Lit l = p.second.lit;
                if (l != CMSat::lit_Undef) {
                    auto it2 = ret.find(l.var());
                    if (it2 != ret.end()) ret[l.var()] = std::vector<CMSat::Lit>();
                    ret[l.var()].push_back(CMSat::Lit(p.first, l.sign()));
                }
            }
            return ret;
        }

        // Gives an example lit, sometimes good enough
        std::map<uint32_t, CMSat::Lit> get_new_to_orig_var() const {
            std::map<uint32_t, CMSat::Lit> ret;
            for(const auto& p: orig_to_new_var) {
                const CMSat::Lit l = p.second.lit;
                if (l != CMSat::lit_Undef) {
                    ret[l.var()] = CMSat::Lit(p.first, l.sign());
                }
            }
            return ret;
        }

        uint32_t nVars() const { return nvars; }
        uint32_t new_vars(uint32_t vars) {
            nvars+=vars;
            for(uint32_t i = 0; i < vars; i++) {
                const uint32_t v = nvars-vars+i;
                orig_to_new_var[v] = CMSat::VarMap(CMSat::Lit(v, false));
            }
            return nvars;
        }
        uint32_t new_var() {
            uint32_t v = nvars;
            nvars++;
            orig_to_new_var[v] = CMSat::VarMap(CMSat::Lit(v, false));
            return nvars;
        }

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
        template<class T> void set_opt_sampl_vars(const T& vars) {
            opt_sampl_vars.clear();
            opt_sampl_vars_set = true;
            opt_sampl_vars.insert(opt_sampl_vars.begin(), vars.begin(), vars.end());
        }

        void set_multiplier_weight(const std::unique_ptr<CMSat::Field>& m) {
            *multiplier_weight = *m;
        }
        const auto& get_multiplier_weight() const { return *multiplier_weight; }
        auto get_lit_weight(CMSat::Lit lit) const {
            assert(weighted);
            if (!fg->weighted()) {
              std::cout << "ERROR: Formula is weighted but the field is not weighted!" << std::endl;
              exit(-1);
            }
            assert(lit.var() < nVars());
            auto it = weights.find(lit.var());
            if (it == weights.end()) return std::unique_ptr<CMSat::Field>(fg->one());
            else {
                if (!lit.sign()) return std::unique_ptr<CMSat::Field>(it->second.pos->dup());
                else return std::unique_ptr<CMSat::Field>(it->second.neg->dup());
            }
        }
        void unset_var_weight(uint32_t v) {
            assert(v < nVars());
            auto it = weights.find(v);
            if (it != weights.end()) weights.erase(it);
        }
        void set_lit_weight(CMSat::Lit lit, const std::unique_ptr<CMSat::Field>& w) {
            assert(weighted);
            if (!fg->weighted()) {
              std::cout << "ERROR: Formula is weighted but the field is not weighted!" << std::endl;
              exit(-1);
            }
            assert(lit.var() < nVars());
            auto it = weights.find(lit.var());
            if (it == weights.end()) {
                Weight weight(fg);
                if (lit.sign()) {
                    *weight.neg = *w;
                    *weight.pos = *fg->one();
                    *weight.pos -= *w;}
                else {
                    *weight.pos = *w;
                    *weight.neg = *fg->one();
                    *weight.neg -= *w;}
                weights[lit.var()] = weight;
                return;
            } else {
                if (!lit.sign()) *it->second.pos = *w;
                else *it->second.neg = *w;
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

        std::vector<CMSat::Lit>& map_cl(std::vector<CMSat::Lit>& cl, const std::vector<uint32_t>& v_map) {
                for(auto& l: cl) l = CMSat::Lit(v_map[l.var()], l.sign());
                return cl;
        }
        std::vector<uint32_t>& map_var(std::vector<uint32_t>& cl, const std::vector<uint32_t>& v_map) {
            for(auto& l: cl) l = v_map[l];
            return cl;
        }
        std::set<uint32_t> map_var(const std::set<uint32_t>& cl, const std::vector<uint32_t>& v_map) {
            std::set<uint32_t> new_set;
            for(auto& l: cl) new_set.insert(v_map[l]);
            return new_set;
        }

        // renumber variables such that sampling set start from 0...N
        void renumber_sampling_vars_for_ganak() {
            assert(sampl_vars.size() <= opt_sampl_vars.size());

            // Create mapping
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
            for(uint32_t x = 0; x < nvars; x++) {
                if (map_here_to_there[x] == m) {
                    map_here_to_there[x] = i;
                    i++;
                }
            }
            assert(i == nvars);

            // Update var map
            std::map<uint32_t, CMSat::VarMap> upd_vmap;
            for(const auto& p: orig_to_new_var) {
                p.second.invariant();
                if (p.second.lit != CMSat::lit_Undef) {
                    CMSat::Lit l = p.second.lit;
                    l = CMSat::Lit(map_here_to_there[l.var()], l.sign());
                    upd_vmap[p.first] = CMSat::VarMap(l);
                } else {
                    upd_vmap[p.first] = p.second;
                }
            }
            orig_to_new_var = upd_vmap;

            // Now we renumber samp_vars, opt_sampl_vars, weights
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

        void write_simpcnf(const std::string& fname, bool red = true) const
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
                    outf << "c p weight " << CMSat::Lit(it.first,false) << " "
                        << *it.second.pos << " 0" << std::endl;

                    outf << "c p weight " << CMSat::Lit(it.first,true) << " "
                        << *it.second.neg << " 0" << std::endl;
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
            outf << "c MUST MULTIPLY BY " << *multiplier_weight << std::endl;
        }

        bool weight_set(uint32_t v) const {
            if (!fg->weighted()) {
              std::cout << "ERROR: Formula is weighted but the field is not weighted!" << std::endl;
              exit(-1);
            }
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
                            << " get_lit_weight(l): " << *get_lit_weight(l) << std::endl;
                    *multiplier_weight *= *get_lit_weight(l);
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
            if (debug_w)
                std::cout << __FUNCTION__ << " [w-debug] orig multiplier_weight: "
                    << *multiplier_weight << std::endl;

            // Take units
            for(const auto& l: solver->get_zero_assigned_lits()) {
                if (l.var() >= nVars()) continue;
                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] orig unit l: " << l
                        << " w: " << *get_lit_weight(l) << std::endl;
                sampling_vars_set.erase(l.var());
                opt_sampling_vars_set.erase(l.var());
                if (get_weighted()) {
                    *multiplier_weight *= *get_lit_weight(l);
                    if (debug_w)
                        std::cout << __FUNCTION__ << " [w-debug] unit: " << l
                            << " multiplier_weight: " << *multiplier_weight << std::endl;
                    unset_var_weight(l.var());
                }
            }

            // Take bin XORs
            // [ replaced, replaced_with ]
            const auto eq_lits = solver->get_all_binary_xors();
            for(auto p: eq_lits) {
                if (p.first.var() >= nVars() || p.second.var() >= nVars()) continue;
                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] repl: " << p.first
                        << " with " << p.second << std::endl;
                if (get_weighted()) {
                    auto wp2 = get_lit_weight(p.second);
                    auto wn2 = get_lit_weight(~p.second);
                    auto wp1 = get_lit_weight(p.first);
                    auto wn1 = get_lit_weight(~p.first);
                    if (debug_w) {
                        std::cout << __FUNCTION__ << " [w-debug] wp1 " << *wp1
                            << " wn1 " << *wn1 << std::endl;
                        std::cout << __FUNCTION__ << " [w-debug] wp2 " << *wp2
                            << " wn2 " << *wn2 << std::endl;
                    }
                    *wp2 *= *wp1;
                    *wn2 *= *wn1;
                    set_lit_weight(p.second, wp2);
                    set_lit_weight(~p.second, wn2);
                    if (debug_w) {
                        std::cout << __FUNCTION__ << " [w-debug] set lit " << p.second
                            << " weight to " << *wp2 << std::endl;
                        std::cout << __FUNCTION__ << " [w-debug] set lit " << ~p.second
                            << " weight to " << *wn2 << std::endl;
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
                auto tmp = fg->zero();
                if (get_weighted()) {
                    CMSat::Lit l(v, false);
                    *tmp += *get_lit_weight(l);
                    *tmp += *get_lit_weight(~l);
                    unset_var_weight(l.var());
                } else {
                    *tmp = *fg->one();
                    *tmp += *fg->one();
                }
                *multiplier_weight *= *tmp;
                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] empty mul: " << *tmp
                        << " final multiplier_weight: " << *multiplier_weight << std::endl;
            }

            set_sampl_vars(sampling_vars_set, true);
            set_opt_sampl_vars(opt_sampling_vars_set);

            for(uint32_t i = 0; i < nVars(); i++) {
                if (opt_sampling_vars_set.count(i) == 0) unset_var_weight(i);
            }

            if (debug_w) {
                std::cout << "w-debug FINAL sampl_vars    : ";
                for(const auto& v: sampl_vars) std::cout << v+1 << " ";
                std::cout << std::endl;
                std::cout << "w-debug FINAL opt_sampl_vars: ";
                for(const auto& v: opt_sampl_vars) {
                    std::cout << v+1 << " ";
                }
                std::cout << std::endl;
            }
        }

        bool not_renumbered() const {
            for(uint32_t i = 0; i < nvars; i++) {
                CMSat::Lit l = CMSat::Lit (i, false);
                auto it = orig_to_new_var.find(i);
                assert(it != orig_to_new_var.end());
                assert(it->second.invariant());
                if (it->second != CMSat::VarMap(l)) return false;

            }
            return true;
        }

        bool evaluate(const std::vector<CMSat::lbool>& vals, uint32_t var) const {
            if (defs.find(var) == defs.end()) {
                std::cout << "ERROR: Variable " << var+1 << " not defined" << std::endl;
                assert(defs.find(var) != defs.end() && "Must be defined");
                exit(-1);
            }
            return ::evaluate(vals, defs.find(var)->second, defs);
        }

        std::set<uint32_t> get_vars_need_definition() const {
            std::set<uint32_t> ret;
            std::set<uint32_t> osv(opt_sampl_vars.begin(), opt_sampl_vars.end());
            for(uint32_t i = 0; i < nvars; i++) {
                if (defs.find(i) == defs.end() && !osv.count(i))
                    ret.insert(i);
            }
            return ret;
        }

        bool aig_contains(const AIG* aig, const uint32_t v) const {
            if (aig == nullptr) return false;
            assert(aig->invariants());
            if (aig->type == t_lit) {
                if (aig->var == v) return true;

                /// Need to be recursive
                if (defs.find(aig->var) != defs.end()) {
                    AIG* aig2 = defs.at(aig->var);
                    return aig_contains(aig2, v);
                }
                return false;
            }
            if (aig->type == t_const) return false;
            if (aig->type == t_and) {
                return aig_contains(aig->l, v) || aig_contains(aig->r, v);
            }
            assert(false && "Unknown AIG type");
            exit(-1);
        }

        std::set<uint32_t> get_cannot_depend_on(const uint32_t v) const {
            assert(false && "defs is original number space but v is not... below is broken");
            if (defs.find(v) != defs.end()) {
                std::cout << "ERROR: Variable " << v+1 << " already defined, why query what it cannot depend on???" << std::endl;
                assert(false);
                exit(-1);
            }
            std::set<uint32_t> osv(opt_sampl_vars.begin(), opt_sampl_vars.end());
            if (osv.count(v)) {
                std::cout << "ERROR: Variable " << v+1 << " is in opt sampling set, why query what it cannot depend on???" << std::endl;
                assert(false);
                exit(-1);
            }

            std::set<uint32_t> ret;
            for(const auto& it: defs) {
                if (osv.count(it.first)) {
                    // The extended input we can always depend on
                    continue;
                }
                if (aig_contains(it.second, v)) ret.insert(it.first);
            }
            return ret;
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
        void standalone_minimize_indep(SimplifiedCNF& cnf, bool all_indep);
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
        SimplifiedCNF standalone_get_simplified_cnf(const SimplifiedCNF& cnf, const SimpConf& simp_conf);
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
        void set_oracle_find_bins(int oracle_find_bins);
        void set_num_samples(int num_samples);
        void set_cms_glob_mult(double cms_glob_mult);
        void set_extend_ccnr(int extend_ccnr);
        void set_autarkies(int autarkies);

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
        int get_num_samples() const;
        int get_oracle_find_bins() const;
        double get_cms_glob_mult() const;
        int get_extend_ccnr() const;
        int get_autarkies() const;

    private:
        ArjPrivateData* arjdata = nullptr;
    };

}
