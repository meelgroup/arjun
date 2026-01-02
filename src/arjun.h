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
#include <functional>
#include <memory>
#include <vector>
#include <string>
#include <map>
#include <set>
#include <fstream>
#include <gmpxx.h>
#include <cryptominisat5/solvertypesmini.h>
#include <cryptominisat5/cryptominisat.h>
#include <mpfr.h>

namespace ArjunNS {

class FHolder;

class AIG;
class AIGManager;
class SimplifiedCNF;
using aig_ptr = std::shared_ptr<AIG>;

enum class AIGT {t_and, t_lit, t_const};
class AIG {
public:
    AIG() = default;
    ~AIG() = default;
    AIG(const AIG&) = delete;
    AIG& operator=(const AIG&) = delete;

    bool invariants() const {
        if (type == AIGT::t_lit) {
            return l == nullptr && r == nullptr && var != none_var;
        }
        if (type == AIGT::t_const) {
            return l == nullptr && r == nullptr && var == none_var;
        }
        if (type == AIGT::t_and) {
            return l != nullptr && r != nullptr && var == none_var;
        }
        assert(false && "Unknown AIG type");
        std::exit(EXIT_FAILURE);
    }

    // vals = input variable assignments
    // aig = AIG to evaluate
    // defs = known definitions of variables
    static bool evaluate(const std::vector<CMSat::lbool>& vals, const aig_ptr& aig, const std::vector<aig_ptr>& defs) {
        assert(aig->invariants());
        if (aig->type == AIGT::t_lit) {
            if (defs[aig->var] != nullptr) {
                // TODO: this is highly inefficient, because this should be cached
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

        if (aig->type == AIGT::t_const) return aig->neg == false;

        if (aig->type == AIGT::t_and) {
            const bool l = evaluate(vals, aig->l, defs);
            const bool r = evaluate(vals, aig->r, defs);
            return aig->neg ^ (l && r);
        }
        assert(false && "Unknown AIG type");
        exit(EXIT_FAILURE);
    }

    static aig_ptr new_lit(CMSat::Lit l) {
        return new_lit(l.var(), l.sign());
    }

    static aig_ptr new_lit(uint32_t var, bool neg = false) {
        auto ret = std::make_shared<AIG>();
        ret->type = AIGT::t_lit;
        ret->var = var;
        ret->neg = neg;
        return ret;
    }

    static aig_ptr new_ite(const aig_ptr& l, const aig_ptr& r, CMSat::Lit b) {
        auto b_aig = new_lit(b.var(), b.sign());
        return new_or(new_and(b_aig, l), new_and(new_not(b_aig), r));
    }

    static aig_ptr new_not(const aig_ptr& a) {
        auto ret = std::make_shared<AIG>();
        ret->type = AIGT::t_and;
        ret->l = a;
        ret->r = a;

        ret->neg = true;
        return ret;
    }

    static aig_ptr new_and(const aig_ptr& l, const aig_ptr& r) {
        auto ret = std::make_shared<AIG>();
        ret->type = AIGT::t_and;
        ret->l = l;
        ret->r = r;
        return ret;
    }

    static aig_ptr new_or(const aig_ptr& l, const aig_ptr& r) {
        auto ret = std::make_shared<AIG>();
        ret->type = AIGT::t_and;
        ret->neg = true;
        ret->l = new_not(l);
        ret->r = new_not(r);
        return ret;
    }

    static aig_ptr new_ite(const aig_ptr& l, const aig_ptr& r, const aig_ptr& b) {
        return AIG::new_or(AIG::new_and(b, l), AIG::new_and(AIG::new_not(b), r));
    }

    // marking for traversals
    static void unmark_all(const aig_ptr& aig) {
        if (!aig) return;
        if (aig->mark) {
            aig->mark = false;
            if (aig->type == AIGT::t_and) {
                unmark_all(aig->l);
                unmark_all(aig->r);
            }
        }
    }
    bool marked() const { return mark; }
    void set_mark() const { mark = true; }

    static void get_dependent_vars(const aig_ptr& aig_orig, std::set<uint32_t>& dep, uint32_t v) {
        unmark_all(aig_orig);
        std::function<void(const aig_ptr&)> helper =
            [&](const aig_ptr& aig) {
                if (aig->marked()) return;
                if (aig->type == AIGT::t_lit) {
                    assert(aig->var != v && "Variable cannot depend on itself");
                    dep.insert(aig->var);
                }
                if (aig->type == AIGT::t_and) {
                    helper(aig->l);
                    helper(aig->r);
                }
                aig->set_mark();
            };
        helper(aig_orig);
    }

    friend std::ostream& operator<<(std::ostream& out, const aig_ptr& aig);
    friend class AIGManager;
    friend class SimplifiedCNF;
private:
    AIGT type = AIGT::t_const;
    static constexpr uint32_t none_var = std::numeric_limits<uint32_t>::max();
    uint32_t var = none_var;
    bool neg = false;
    mutable bool mark = false; // For traversals
    aig_ptr l = nullptr;
    aig_ptr r = nullptr;
};


inline std::ostream& operator<<(std::ostream& out, const aig_ptr& aig) {
    if (!aig) {
        out << "NULL_AIG";
        return out;
    }
    assert(aig->invariants());

    if (aig->type == AIGT::t_lit) {
        out << (aig->neg ? "~" : "") << "x" << aig->var+1;
        return out;
    }
    if (aig->type == AIGT::t_const) {
        out << (aig->neg ? "FALSE" : "TRUE");
        return out;
    }
    assert(aig->type == AIGT::t_and);
    out << (aig->neg ? "~" : "") << "AND(";
    out << (aig->l) << ", " << (aig->r) << ")";
    out << ")";
    return out;
}

class AIGManager {
public:
    ~AIGManager() = default;
    AIGManager() {
        const_true = std::make_shared<AIG>();
        const_true->type = AIGT::t_const;
        const_true->neg = false;
        const_false = std::make_shared<AIG>();
        const_false->type = AIGT::t_const;
        const_false->neg = true;
    }

    void clear() {
        const_true = nullptr;
        const_false = nullptr;
    }

    AIGManager& operator=(const AIGManager& other) {
        if (this != &other) {
            clear();
            // With shared_ptr, just copy the pointers - no deep copy needed!
            const_true = other.const_true;
            const_false = other.const_false;
        }
        return *this;
    }

    AIGManager(const AIGManager& other) {
        const_true = other.const_true;
        const_false = other.const_false;
    }

    aig_ptr new_const(bool val) {
        return val ? const_true : const_false;
    }


private:
    // There could be other const true, this is just a good example so we don't always copy
    // Due to copying we don'g guarantee uniqueness
    aig_ptr const_true = nullptr;
    // There could be other const false, this is just a good example so we don't always copy
    // Due to copying we don'g guarantee uniqueness
    aig_ptr const_false = nullptr;
};

class FMpz final : public CMSat::Field {
public:
    mpz_class val;
    FMpz(const int _val) : val(_val) {}
    FMpz(const mpz_class& _val) : val(_val) {}
    FMpz(const FMpz& other) : val(other.val) {}

    Field& operator=(const Field& other) final {
        const auto& od = static_cast<const FMpz&>(other);
        val = od.val;
        return *this;
    }

    Field& operator+=(const Field& other) final {
        const auto& od = static_cast<const FMpz&>(other);
        val += od.val;
        return *this;
    }

    std::unique_ptr<Field> add(const Field& other) final {
        const auto& od = static_cast<const FMpz&>(other);
        return std::make_unique<FMpz>(val + od.val);
    }

    Field& operator-=(const Field& other) final {
        const auto& od = static_cast<const FMpz&>(other);
        val -= od.val;
        return *this;
    }

    Field& operator*=(const Field& other) final {
        const auto& od = static_cast<const FMpz&>(other);
        val *= od.val;
        return *this;
    }

    Field& operator/=(const Field& other) final {
        const auto& od = static_cast<const FMpz&>(other);
        if (od.val == 0) throw std::runtime_error("Division by zero");
        val /= od.val;
        return *this;
    }

    bool operator==(const Field& other) const final {
        const auto& od = static_cast<const FMpz&>(other);
        return od.val == val;
    }

    std::ostream& display(std::ostream& os) const final {
        os << val;
        return os;
    }

    std::unique_ptr<Field> dup() const final { return std::make_unique<FMpz>(val); }
    bool is_zero() const final { return val == 0; }
    bool is_one() const final { return val == 1; }
    void set_zero() final { val = 0; }
    void set_one() final { val = 1; }

    bool parse(const std::string& str, const uint32_t line_no) final {
        uint32_t at = 0;
        skip_whitespace(str, at);
        auto sign = parse_sign(str, at);
        if (!parse_int(val, str, at, line_no)) return false;
        val*=sign;
        return check_end_of_weight(str, at, line_no);
    }

    uint64_t helper(const mpz_class& v) const {
      return v.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
    }

    uint64_t bytes_used() const final {
      return sizeof(FMpz) + helper(val);
    }
};

class FGenMpz final : public CMSat::FieldGen {
public:
    ~FGenMpz() final = default;
    std::unique_ptr<CMSat::Field> zero() const final {
        return std::make_unique<FMpz>(0);
    }

    std::unique_ptr<CMSat::Field> one() const final {
        return std::make_unique<FMpz>(1);
    }

    std::unique_ptr<FieldGen> dup() const final {
        return std::make_unique<FGenMpz>();
    }

    bool larger_than(const CMSat::Field& a, const CMSat::Field& b) const final {
        const auto& ad = static_cast<const FMpz&>(a);
        const auto& bd = static_cast<const FMpz&>(b);
        return ad.val > bd.val;
    }

    bool weighted() const final { return false; }
};

class FMpq final : public CMSat::Field {
public:
    mpq_class val;
    FMpq() : val(0) {}
    FMpq(const int _val) : val(_val) {}
    FMpq(const mpz_class& _val) : val(_val) {}
    FMpq(const mpq_class& _val) : val(_val) {}
    FMpq(const FMpq& other) : val(other.val) {}
    const mpq_class& get_val() const { return val; }

    Field& operator=(const Field& other) final {
        const auto& od = static_cast<const FMpq&>(other);
        val = od.val;
        return *this;
    }

    Field& operator+=(const Field& other) final {
        const auto& od = static_cast<const FMpq&>(other);
        val += od.val;
        return *this;
    }

    std::unique_ptr<Field> add(const Field& other) final {
        const auto& od = static_cast<const FMpq&>(other);
        return std::make_unique<FMpq>(val + od.val);
    }

    Field& operator-=(const Field& other) final {
        const auto& od = static_cast<const FMpq&>(other);
        val -= od.val;
        return *this;
    }

    Field& operator*=(const Field& other) final {
        const auto& od = static_cast<const FMpq&>(other);
        val *= od.val;
        return *this;
    }

    Field& operator/=(const Field& other) final {
        const auto& od = static_cast<const FMpq&>(other);
        if (od.val == 0) throw std::runtime_error("Division by zero");
        val /= od.val;
        return *this;
    }

    bool operator==(const Field& other) const final {
        const auto& od = static_cast<const FMpq&>(other);
        return val == od.val;
    }

    std::ostream& display(std::ostream& os) const final {
        os << val;
        return os;
    }

    std::unique_ptr<Field> dup() const final {
        return std::make_unique<FMpq>(val);
    }

    bool is_zero() const final {
        return val == 0;
    }

    bool is_one() const final {
        return val == 1;
    }

    bool parse(const std::string& str, const uint32_t line_no) final {
        uint32_t at = 0;
        if (!parse_mpq(str, at, line_no)) return false;
        return check_end_of_weight(str, at, line_no);
    }

    void set_zero() final { val = 0; }
    void set_one() final { val = 1; }

    inline uint64_t helper(const mpz_class& v) const {
      return v.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
    }

    uint64_t bytes_used() const final {
      return sizeof(FMpq) +
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

class FGenMpq final : public CMSat::FieldGen {
public:
    ~FGenMpq() final = default;
    std::unique_ptr<CMSat::Field> zero() const final {
        return std::make_unique<FMpq>(0);
    }

    std::unique_ptr<CMSat::Field> one() const final {
        return std::make_unique<FMpq>(1);
    }

    std::unique_ptr<FieldGen> dup() const final {
        return std::make_unique<FGenMpq>();
    }

    bool larger_than(const CMSat::Field& a, const CMSat::Field& b) const final {
        const auto& ad = static_cast<const FMpq&>(a);
        const auto& bd = static_cast<const FMpq&>(b);
        return ad.val > bd.val;
    }

    bool weighted() const final { return true; }
};


inline unsigned int mpfr_memory_usage(const mpfr_t& x) {
    // Get the precision of the mpfr_t variable (in bits)
    mpfr_prec_t precision = mpfr_get_prec(x);

    // Determine the size of a limb (in bits)
    size_t limb_size = mp_bits_per_limb;

    // Calculate the number of limbs required for the significand
    size_t num_limbs = (precision + limb_size - 1) / limb_size;

    // Base size of mpfr_t structure
    unsigned int base_size = sizeof(__mpfr_struct);

    // Size of the mantissa (significand) data
    unsigned int mantissa_size = num_limbs * sizeof(mp_limb_t);

    // Total memory usage
    return base_size + mantissa_size;
}

class FMpfr final : public CMSat::Field {
public:
    mpfr_t val;
    ~FMpfr() final { mpfr_clear(val); }
    FMpfr() {
        mpfr_init2(val, 256);
        mpfr_set_si(val, 0, MPFR_RNDN);
    }
    FMpfr(const int _val) {
        mpfr_init2(val, 256);
        mpfr_set_si(val, _val, MPFR_RNDN);
    }
    FMpfr(const double _val) {
        mpfr_init2(val, 256);
        mpfr_set_d(val, _val, MPFR_RNDN);
    }
    FMpfr(const mpfr_t& _val) {
        mpfr_init2(val, 256);
        mpfr_set(val, _val, MPFR_RNDN);
    }
    FMpfr(const FMpfr& other) {
        mpfr_init2(val, 256);
        mpfr_set(val, other.val, MPFR_RNDN);
    }
    const mpfr_t& get_val() const { return val; }

    Field& operator=(const Field& other) final {
        const auto& od = static_cast<const FMpfr&>(other);
        mpfr_set(val, od.val, MPFR_RNDN);
        return *this;
    }

    Field& operator+=(const Field& other) final {
        const auto& od = static_cast<const FMpfr&>(other);
        mpfr_add(val, val, od.val, MPFR_RNDN);
        return *this;
    }

    std::unique_ptr<Field> add(const Field& other) final {
        const auto& od = static_cast<const FMpfr&>(other);
        mpfr_t res;
        mpfr_init2(res, 256);
        mpfr_add(res, val, od.val, MPFR_RNDN);
        std::unique_ptr<FMpfr> ret = std::make_unique<FMpfr>(res);
        mpfr_clear(res);
        return ret;
    }

    Field& operator-=(const Field& other) final {
        const auto& od = static_cast<const FMpfr&>(other);
        mpfr_sub(val, val, od.val, MPFR_RNDN);
        return *this;
    }

    Field& operator*=(const Field& other) final {
        const auto& od = static_cast<const FMpfr&>(other);
        mpfr_mul(val, val, od.val, MPFR_RNDN);
        return *this;
    }

    Field& operator/=(const Field& other) final {
        const auto& od = static_cast<const FMpfr&>(other);
        if (mpfr_cmp_si(od.val, 0) == 0)
            throw std::runtime_error("Division by zero");
        mpfr_div(val, val, od.val, MPFR_RNDN);
        return *this;
    }

    bool operator==(const Field& other) const final {
        const auto& od = static_cast<const FMpfr&>(other);
        return mpfr_cmp(val, od.val) == 0;
    }

    std::ostream& display(std::ostream& os) const final {
        char* tmp = nullptr;
        mpfr_asprintf(&tmp, "%.8Re", val);
        os << tmp;
        mpfr_free_str(tmp);
        return os;
    }

    std::unique_ptr<Field> dup() const final {
        return std::make_unique<FMpfr>(val);
    }

    bool is_zero() const final {
        return mpfr_cmp_si(val, 0) == 0;
    }

    bool is_one() const final {
        return mpfr_cmp_si(val, 1) == 0;
    }

    bool parse(const std::string& str, const uint32_t line_no) final {
        uint32_t at = 0;
        FMpq val_pre;
        if (!val_pre.parse_mpq(str, at, line_no)) return false;
        skip_whitespace(str, at);
        mpfr_set_q(val, val_pre.get_val().get_mpq_t(), MPFR_RNDN);
        return true;
    }

    void set_zero() final { mpfr_set_si(val, 0, MPFR_RNDN); }
    void set_one() final { mpfr_set_si(val, 1, MPFR_RNDN); }


    uint64_t bytes_used() const final {
      return sizeof(FMpfr) + mpfr_memory_usage(val);
    }
};

class FGenMpfr final : public CMSat::FieldGen {
public:
    ~FGenMpfr() final = default;
    std::unique_ptr<CMSat::Field> zero() const final {
        return std::make_unique<FMpfr>(0);
    }

    std::unique_ptr<CMSat::Field> one() const final {
        return std::make_unique<FMpfr>(1);
    }

    std::unique_ptr<FieldGen> dup() const final {
        return std::make_unique<FGenMpfr>();
    }

    bool larger_than(const CMSat::Field& a, const CMSat::Field& b) const final {
        const auto& ad = static_cast<const FMpfr&>(a);
        const auto& bd = static_cast<const FMpfr&>(b);
        return mpfr_cmp(ad.val, bd.val) > 0;
    }

    bool weighted() const final { return true; }
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
    int do_subs_with_resolvent_clauses = 1;
    bool do_backbone_puura = true;
    int weaken_limit = 8000;
};

class SimplifiedCNF {
public:
    std::unique_ptr<CMSat::FieldGen> fg = nullptr;
    SimplifiedCNF(const std::unique_ptr<CMSat::FieldGen>& _fg) : fg(_fg->dup()), multiplier_weight(fg->one()) {}
    SimplifiedCNF(const CMSat::FieldGen* _fg) : fg(_fg->dup()), multiplier_weight(fg->one()) {}
    ~SimplifiedCNF() = default;
    SimplifiedCNF& operator=(const SimplifiedCNF& other) {
        assert(other.defs_invariant());
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
        if (!need_aig) {
            assert(defs.empty());
            assert(other.defs.empty());
            assert(other.orig_sampl_vars.empty());
            assert(other.orig_clauses.empty());
        } else {
            after_backward_round_synth = other.after_backward_round_synth;
            aig_mng = other.aig_mng;
            defs = other.defs;
            orig_clauses = other.orig_clauses;
            orig_sampl_vars = other.orig_sampl_vars;
            orig_sampl_vars_set = other.orig_sampl_vars_set;
        }
        defs_invariant();

        return *this;
    }
    SimplifiedCNF(const SimplifiedCNF& other) {
        *this = other;
    }

    const auto& nVars() const { return nvars; }
    const auto& get_clauses() const { return clauses; }
    const auto& get_red_clauses() const { return red_clauses; }
    const auto& get_weights() const { return weights; }
    const auto& get_sampl_vars() const { return sampl_vars; }
    const auto& get_orig_sampl_vars() const { assert(orig_sampl_vars_set); return orig_sampl_vars; }
    const auto& get_orig_clauses() const { return orig_clauses; }
    const auto& get_opt_sampl_vars() const { return opt_sampl_vars; }
    const auto& get_backbone_done() const { return backbone_done; }
    bool is_projected() const { return proj; }

    template<class T>
    void set_orig_sampl_vars(const T& vars) {
        assert(need_aig);
        assert(orig_sampl_vars.empty());
        assert(!orig_sampl_vars_set);
        orig_sampl_vars_set = true;
        for(const auto& v: vars) orig_sampl_vars.insert(v);
    }
    void set_orig_clauses(const std::vector<std::vector<CMSat::Lit>>& cls) {
        assert(need_aig);
        assert(orig_clauses.empty());
        orig_clauses = cls;
    }
    void add_orig_clause(const std::vector<CMSat::Lit>& cl) {
        assert(need_aig);
        orig_clauses.push_back(cl);
    }

    // ORIG variable
    bool defined(const uint32_t v) const {
        assert(v < defs.size());
        assert(need_aig);
        if (defs[v] != nullptr) return true;
        return false;
    }
    void set_need_aig() {
        // should be the first thing to set
        assert(!need_aig);
        assert(nvars == 0);
        assert(clauses.empty());
        assert(red_clauses.empty());
        assert(defs.empty());
        assert(opt_sampl_vars.empty());
        assert(sampl_vars.empty());
        assert(orig_sampl_vars_set == false);
        assert(orig_sampl_vars.empty());
        assert(sampl_vars_set == false);
        assert(opt_sampl_vars_set == false);
        need_aig = true;
    }
    bool get_need_aig() const { return need_aig; }
    uint32_t num_defs() const { return defs.size(); }

    // Returns NEW vars, i.e. < nVars()
    // It is checked that it is correct and total
    auto get_var_types([[maybe_unused]] uint32_t verb) const {
        assert(need_aig);
        std::set<uint32_t> input;
        for (const auto& v: get_orig_sampl_vars()) {
            const auto it = orig_to_new_var.find(v);
            if (it == orig_to_new_var.end()) continue;
            const uint32_t cnf_var = it->second.var();
            /* std::cout << "c o input var: " << v+1 << " maps to cnf var " */
            /*      << cnf_var+1 << std::endl; */
            assert(cnf_var < nVars());
            input.insert(cnf_var);
        }
        assert(input.size() == sampl_vars.size());
        std::set<uint32_t> to_define;
        for (uint32_t v = 0; v < num_defs(); v++) {
            if (!get_orig_sampl_vars().count(v) && !defined(v)) {
                const auto it = orig_to_new_var.find(v);
                if (it == orig_to_new_var.end()) continue;
                const uint32_t cnf_var = it->second.var();
                /* std::cout << "c o to_define var: " << v+1 << " maps to cnf var " */
                /*  << cnf_var+1 << std::endl; */
                assert(cnf_var < nVars());
                to_define.insert(cnf_var);
            }
        }
        std::set<uint32_t> unsat_defined_vars;
        std::set<uint32_t> backw_synth_defined_vars;
        for (uint32_t v = 0; v < num_defs(); v++) {
            if (get_orig_sampl_vars().count(v)) continue;
            if (orig_to_new_var.count(v) == 0) continue;
            // This var is NOT input and IS in the CNF
            if (defined(v) == false) continue;
            auto s = get_dependent_vars_recursive(defs[v], v);
            bool only_input_deps = true;
            for(const auto& d: s) {
                if (!get_orig_sampl_vars().count(d)) {
                    only_input_deps = false;
                    break;
                }
            }

            const uint32_t cnf_var = orig_to_new_var.at(v).var();
            assert(cnf_var < nVars());
            if (only_input_deps) unsat_defined_vars.insert(cnf_var);
            else backw_synth_defined_vars.insert(cnf_var);
        }
        if (verb >= 1) {
            std::cout << "c o [get-var-types] Variable types in CNF:" << std::endl;
            std::cout << "c o [get-var-types]   Input vars: ";
            for(const auto& v: input) {
                std::cout << v+1 << " ";
            }
            std::cout << std::endl;

            std::cout << "c o [get-var-types] Input vars: " << input.size() << std::endl;
            std::cout << "c o [get-var-types] To-define vars: " << to_define.size() << std::endl;
            std::cout << "c o [get-var-types]   To-define vars: ";
            for(const auto& v: to_define) {
                std::cout << v+1 << " ";
            }
            std::cout << std::endl;

            std::cout << "c o [get-var-types] Unsat-defined vars: "
                << unsat_defined_vars.size() << std::endl;
            std::cout << "c o [get-var-types] Backward-synth-defined vars: "
                << backw_synth_defined_vars.size() << std::endl;
            std::cout << "c o [get-var-types] Total vars in CNF: " << nVars() << std::endl;
        }
        assert(input.size() + to_define.size() + unsat_defined_vars.size() + backw_synth_defined_vars.size() == nVars());

        // unsat-defined vars can be treateed as input vars
        for(const auto& v: unsat_defined_vars) input.insert(v);
        return std::make_tuple(input, to_define, backw_synth_defined_vars);
    }

    bool defs_invariant() const {
        check_cnf_sampl_sanity();

        if (!need_aig) return true;
        assert(orig_sampl_vars_set && "If need_aig, orig_sampl_vars_set must be set");
        assert(sampl_vars_set);
        assert(sampl_vars.size() == opt_sampl_vars.size());
        assert(defs.size() >= nvars && "Defs size must be at least nvars, as nvars can only be smaller");


        for(const auto& v: orig_sampl_vars) {
            if(defs[v] == nullptr) continue;
            else if (defs[v]->type == AIGT::t_const) {
                continue;
            }
            else if (defs[v]->type == AIGT::t_lit) {
                assert(orig_sampl_vars.count(defs[v]->var) && "If orig_sampl_var is defined to a literal, that literal must also be an orig_sampl_var");
                continue;
            } else {
                std::cerr << "ERROR: Orig sampl var " << v+1
                    << " cannot be defined to an AIG other than"
                    " a const or a lit pointing to another orig_sampl_var, but it is: "
                    << defs[v] << std::endl;
                assert(false);
            }

        }
        check_pre_post_backward_round_synth();
        all_vars_accounted_for();
        check_self_dependency();
        get_var_types(0); // just to check assertions inside
        return true;
    }

    // Get the orig vars this AIG depends on, recursively expanding defined vars
    std::set<uint32_t> get_dependent_vars_recursive(const aig_ptr& aig, uint32_t orig_v) const {
        assert(need_aig);
        std::set<uint32_t> dep;
        std::map<uint32_t, std::set<uint32_t>> cache;
        AIG::get_dependent_vars(aig, dep, orig_v);
        bool changed = true;
        while(changed) {
            changed = false;
            std::set<uint32_t> new_dep;
            for(const auto& v: dep) {
                if (!defined(v)) new_dep.insert(v);
                else {
                    std::set<uint32_t> sub_dep;
                    if (cache.count(v)) sub_dep = cache.at(v);
                    else {
                        AIG::get_dependent_vars(defs[v], sub_dep, v);
                        assert(!sub_dep.count(v) && "Variable cannot depend on itself");
                        cache[v] = sub_dep;
                    }
                    new_dep.insert(sub_dep.begin(), sub_dep.end());
                }
            }
            if (new_dep != dep) changed = true;
            dep = new_dep;
        }
        assert(!dep.count(orig_v) && "Variable cannot depend on itself");
        return dep;
    }

    void check_self_dependency() const {
        if (!need_aig) return;
        for(uint32_t orig_v = 0; orig_v < defs.size(); orig_v ++) {
            if (orig_sampl_vars.count(orig_v)) {
                if (!defined(orig_v)) continue;
                else if (defs[orig_v]->type == AIGT::t_lit) {
                    assert(defs[orig_v]->var != orig_v && "Variable depends on itself? Also this is an orig sampl var defined to a literal that has the same var?");
                    assert(orig_sampl_vars.count(defs[orig_v]->var) && "If orig_sampl_var is defined to a literal, that literal must also be an orig_sampl_var");
                    continue;
                } else if (defs[orig_v]->type == AIGT::t_const) {
                    continue;
                } else {
                    std::cerr << "ERROR:Orig sampl var " << orig_v+1 << " cannot be defined to an AIG other than literal or const, but it is: " << defs[orig_v] << std::endl;
                    assert(false);
                }
            }
            if (!defined(orig_v)) continue;

            // This checks for self-dependency
            get_dependent_vars_recursive(defs[orig_v], orig_v);
        }
    }

    void check_cnf_vars() const {
        auto check = [](const std::vector<CMSat::Lit>& cl, uint32_t _nvars) {
            for(const auto& l: cl) {
                if (l.var() >= _nvars) {
                    std::cout << "ERROR: Found a clause with a variable that has more variables than the number of variables we are supposed to have" << std::endl;
                    std::cout << "cl: ";
                    for(const auto& l2: cl) std::cout << l2 << " ";
                    std::cout << std::endl;
                    std::cout << "nvars: " << _nvars+1 << std::endl;
                    exit(EXIT_FAILURE);
                }
                assert(l.var() < _nvars);
            }
        };

        // all clauses contain variables that are less than nvars
        for(const auto& cl: clauses) check(cl, nvars);
        for(const auto& cl: red_clauses) check(cl, nvars);


        // Now check orig_to_new_var covers all vars in the CNF
        if (!need_aig) return;
        std::set<uint32_t> vars_in_cnf;
        for(const auto& cl: clauses) {
            for(const auto& l: cl) {
                vars_in_cnf.insert(l.var());
            }
        }
        for(const auto& cl: red_clauses) {
            for(const auto& l: cl) {
                vars_in_cnf.insert(l.var());
            }
        }
        for(const auto& v: vars_in_cnf) {
            assert(v < nvars); // already checked above
            bool in_orig = false;
            for(const auto& [o, n]: orig_to_new_var) {
                if (n.var() == v) {
                    in_orig = true;
                    break;
                }
            }
            assert(in_orig && "All CNF vars must be in orig_to_new_var");
        }
    }

    // all vars are either: in orig_sampl_vars, defined, or in the cnf
    void all_vars_accounted_for() const {
        assert(need_aig);
        for(uint32_t v = 0; v < defs.size(); v ++) {
            if (orig_sampl_vars.count(v)) continue; // we'll get this as input
            if (defined(v)) continue; // already defined
            if (orig_to_new_var.count(v)) continue; // appears in CNF
            std::cout << "ERROR: Orig var " << v+1 << " is not defined, not in orig_sampl_vars, and not in cnf" << std::endl;
            assert(false && "All vars must be accounted for");
        }
    }

    // this checks that NO unsat-define has been made yet
    void check_pre_post_backward_round_synth() const {
        if (!need_aig) return;
        std::map<uint32_t, std::set<uint32_t>> dependencies;
        for(const auto& [o, n] : orig_to_new_var) {
            assert(o < defs.size());
            assert(n != CMSat::lit_Undef && n.var() < nvars);
            if (defined(o)) {
                auto s = get_dependent_vars_recursive(defs[o], o);
                dependencies[o] = s;
                bool only_orig_sampl = true;
                for(const auto& v: s) {
                    if (!orig_sampl_vars.count(v)) {
                        only_orig_sampl = false;
                        break;
                    }
                }
                if (!after_backward_round_synth && !only_orig_sampl) {
                    std::cout << "ERROR: Found a variable in CNF, orig: " << o+1 << " new: " << n.var()+1
                        << " that is defined in terms of non-orig-sampl-vars before backward round synth.";
                    std::cout << std::endl << " in old: ";
                    for(const auto& v: s) std::cout << v+1 << "( " << (orig_sampl_vars.count(v) ? "o" : "n") << " ) ";
                    std::cout << std::endl << " in new: ";
                    for(const auto& v: s) {
                        auto it = orig_to_new_var.find(v);
                        if (it == orig_to_new_var.end()) std::cout << "undef ";
                        else std::cout << it->second.var()+1 << "( " << (orig_sampl_vars.count(v) ? "o" : "n") << " ) ";
                    }
                    std::cout << std::endl;
                    assert(false && "Before backward round synth, variables in CNF must be defined ONLY in terms of orig_sampl_vars");
                }
            }
        }
        for(const auto& [o, dep] : dependencies) {
            assert(!orig_sampl_vars.count(o));
            for(const auto& v: dep) {
                // o depends on v
                if (orig_sampl_vars.count(v)) continue;
                auto it = dependencies.find(v);
                if (it == dependencies.end()) continue;
                if (it->second.count(o)) {
                    // so v cannot depend on o
                    std::cout << "ERROR: Found a dependency cycle between orig vars "
                        << o+1 << " and " << v+1 << std::endl;
                    assert(false && "Dependency cycle found");
                }
            }

        }
    }

    void set_all_opt_indep() {
        opt_sampl_vars.clear();
        for(uint32_t i = 0; i < nvars; i++) opt_sampl_vars.push_back(i);
    }
    void add_opt_sampl_var(const uint32_t v) {
        assert(v < nvars);
        opt_sampl_vars.push_back(v);
    }

    void clean_idiotic_mccomp_weights() {
        std::set<uint32_t> opt_sampl_vars_s(opt_sampl_vars.begin(), opt_sampl_vars.end());
        std::set<uint32_t> to_remove;
        for(const auto& w: weights) {
            if (opt_sampl_vars_s.count(w.first) == 0) to_remove.insert(w.first);
        }
        if (to_remove.empty()) return;

        std::cout << "c o WARNING!!!! "
            << to_remove.size() << " weights removed that weren't in the (opt) sampling set" << std::endl;
        for(const auto& w: to_remove) weights.erase(w);
    }

    void check_cnf_sampl_sanity() const {
        assert(fg != nullptr);

        check_cnf_vars();
        std::set<uint32_t> sampl_vars_s(sampl_vars.begin(), sampl_vars.end());
        std::set<uint32_t> opt_sampl_vars_s(opt_sampl_vars.begin(), opt_sampl_vars.end());

        // sampling vars less than nvars
        for(const auto& v: opt_sampl_vars_s) {
            if (v >= nvars) {
                std::cout << "ERROR: Found a sampling var that is greater than the number of variables we are supposed to have" << std::endl;
                std::cout << "sampling var: " << v+1 << std::endl;
                std::cout << "nvars: " << nvars+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(v < nvars);
        }

        // all sampling vars are also opt sampling vars
        for(const auto& v: sampl_vars_s) {
            if (!opt_sampl_vars_s.count(v)) {
                std::cout << "ERROR: Found a sampling var that is not an opt sampling var: "
                    << v+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(opt_sampl_vars_s.count(v));
        }

        // weights must be in opt sampling vars
        for(const auto& w: weights) {
            if (w.first >= nvars) {
                std::cout << "ERROR: Found a weight that is greater than the number of variables we are supposed to have" << std::endl;
                std::cout << "weight var: " << w.first+1 << std::endl;
                std::cout << "nvars: " << nvars+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(w.first < nvars);
            if (opt_sampl_vars_s.count(w.first) == 0) {
                // Idiotic but we allow 1/1 weights, even though they are useless
                if (w.second.pos->is_one() && w.second.neg->is_one()) continue;

                std::cout << "ERROR: Found a weight that is not an (opt) sampling var: "
                    << w.first+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(opt_sampl_vars_s.count(w.first));
        }
    }

    // Gives all the orig lits that map to this variable
    std::map<uint32_t, std::vector<CMSat::Lit>> get_new_to_orig_var_list() const {
        std::map<uint32_t, std::vector<CMSat::Lit>> ret;
        for(const auto& p: orig_to_new_var) {
            const CMSat::Lit l = p.second;
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
        for(const auto& [origv, l]:  orig_to_new_var) {
            assert(l != CMSat::lit_Undef);
            ret[l.var()] = CMSat::Lit(origv, l.sign());
        }
        return ret;
    }

    uint32_t new_vars(uint32_t vars) {
        nvars+=vars;
        for(uint32_t i = 0; i < vars; i++) {
            const uint32_t v = nvars-vars+i;
            orig_to_new_var[v] = CMSat::Lit(v, false);
            if (need_aig) defs.push_back(nullptr);
        }
        return nvars;
    }
    uint32_t new_var() {
        uint32_t v = nvars;
        nvars++;
        orig_to_new_var[v] = CMSat::Lit(v, false);
        if (need_aig) defs.push_back(nullptr);
        return nvars;
    }

    void start_with_clean_sampl_vars() {
        assert(sampl_vars.empty());
        assert(opt_sampl_vars.empty());
        for(uint32_t i = 0; i < nvars; i++) sampl_vars.push_back(i);
        for(uint32_t i = 0; i < nvars; i++) opt_sampl_vars.push_back(i);
    }
    void check_var(const uint32_t v) const {
        if (v >= nVars()) {
            std::cout << "ERROR: Tried to access a variable that is too large" << std::endl;
            std::cout << "var: " << v+1 << std::endl;
            std::cout << "nvars: " << nVars() << std::endl;
            assert(v < nVars());
            exit(EXIT_FAILURE);
        }
    }
    void check_clause(const std::vector<CMSat::Lit>& cl) const {
        for(const auto& l: cl) check_var(l.var());
    }
    void add_xor_clause(const std::vector<uint32_t>&, bool) { exit(EXIT_FAILURE); }
    void add_xor_clause(const std::vector<CMSat::Lit>&, bool) { exit(EXIT_FAILURE); }
    void add_clause(const std::vector<CMSat::Lit>& cl) {
        check_clause(cl);
        clauses.push_back(cl);
    }
    void add_red_clause(const std::vector<CMSat::Lit>& cl) {
        check_clause(cl);
        red_clauses.push_back(cl);
    }
    bool get_sampl_vars_set() const { return sampl_vars_set; }
    bool get_opt_sampl_vars_set() const { return opt_sampl_vars_set; }

    template<class T>
    void set_sampl_vars(const T& vars, bool ignore = false) {
        for(const auto& v: vars) check_var(v);
        if (!ignore) {
            assert(sampl_vars.empty());
            assert(sampl_vars_set == false);
        }
        sampl_vars.clear();
        sampl_vars_set = true;
        for(const auto& v: vars) sampl_vars.push_back(v);
        if (!opt_sampl_vars_set) set_opt_sampl_vars(vars);
    }
    template<class T> void set_opt_sampl_vars(const T& vars) {
        for(const auto& v: vars) check_var(v);
        opt_sampl_vars.clear();
        opt_sampl_vars_set = true;
        opt_sampl_vars.insert(opt_sampl_vars.begin(), vars.begin(), vars.end());
    }

    template<class T2>
    void remove_sampling_vars(const T2& zero_assigned) {
        std::set sampl_vars2(get_sampl_vars().begin(), get_sampl_vars().end());
        std::set opt_sampl_vars2(get_opt_sampl_vars().begin(), get_opt_sampl_vars().end());
        for(const auto& l: zero_assigned) {
            assert(l.var() < nvars);
            sampl_vars2.erase(l.var());
            opt_sampl_vars2.erase(l.var());
        }
        set_sampl_vars(sampl_vars2, true);
        set_opt_sampl_vars(opt_sampl_vars2);
    }

    void set_multiplier_weight(const std::unique_ptr<CMSat::Field>& m) {
        *multiplier_weight = *m;
    }
    const auto& get_multiplier_weight() const { return multiplier_weight; }
    auto get_lit_weight(CMSat::Lit lit) const {
        assert(weighted);
        if (!fg->weighted()) {
          std::cout << "ERROR: Formula is weighted but the field is not weighted!" << std::endl;
          exit(EXIT_FAILURE);
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
        set_lit_weight(lit, *w);
    }
    void set_lit_weight(CMSat::Lit lit, const CMSat::Field& w) {
        check_var(lit.var());
        assert(weighted);
        if (!fg->weighted()) {
          std::cout << "ERROR: Formula is weighted but the field is not weighted!" << std::endl;
          exit(EXIT_FAILURE);
        }
        assert(lit.var() < nVars());
        auto it = weights.find(lit.var());
        if (it == weights.end()) {
            Weight weight(fg);
            if (lit.sign()) {
                *weight.neg = w;
                *weight.pos = *fg->one();
                *weight.pos -= w;}
            else {
                *weight.pos = w;
                *weight.neg = *fg->one();
                *weight.neg -= w;}
            weights[lit.var()] = weight;
            return;
        } else {
            if (!lit.sign()) *it->second.pos = w;
            else *it->second.neg = w;
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

    void strip_opt_sampling_vars() {
        std::set<uint32_t> tmp(sampl_vars.begin(), sampl_vars.end());
        for(const auto& w: weights) tmp.insert(w.first);
        sampl_vars.clear();
        sampl_vars.insert(sampl_vars.begin(), tmp.begin(), tmp.end());
        opt_sampl_vars = sampl_vars;
    }

    // renumber variables such that sampling set start from 0...N
    void renumber_sampling_vars_for_ganak() {
        assert(sampl_vars.size() <= opt_sampl_vars.size());
        // NOTE: we do not need to update defs, because defs is ORIG to ORIG

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
        std::map<uint32_t, CMSat::Lit> upd_vmap;
        for(const auto& [o,n]: orig_to_new_var) {
            if (n != CMSat::lit_Undef) {
                CMSat::Lit l = n;
                l = CMSat::Lit(map_here_to_there[l.var()], l.sign());
                upd_vmap[o] = l;
            } else {
                upd_vmap[o] = n;
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

    void write_simpcnf(const std::string& fname, bool red = true) const {
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
        outf << "c MUST MULTIPLY BY " << *multiplier_weight << " 0" << std::endl;
    }

    bool weight_set(uint32_t v) const {
        check_var(v);
        if (!fg->weighted()) {
          std::cout << "ERROR: Formula is weighted but the field is not weighted!" << std::endl;
          exit(EXIT_FAILURE);
        }
        return weights.count(v) > 0;
    }

    void remove_equiv_weights() {
        if (!weighted) return;

        constexpr bool debug_w = false;
        std::set<uint32_t> tmp(opt_sampl_vars.begin(), opt_sampl_vars.end());
        for(uint32_t i = 0; i < nvars; i++) {
            CMSat::Lit l(i, false);
            if (tmp.count(i) == 0) continue;

            if (weights.count(l.var()) && *get_lit_weight(l) == *get_lit_weight(~l)) {
                if (debug_w)
                    std::cout << __FUNCTION__ << " Removing equiv weight for " << l
                        << " get_lit_weight(l): " << *get_lit_weight(l) << std::endl;
                *multiplier_weight *= *get_lit_weight(l);
                unset_var_weight(i);
            }
        }
    }

    void fix_weights(std::unique_ptr<CMSat::SATSolver>& solver,
            const std::vector<uint32_t> new_sampl_vars,
            const std::vector<uint32_t>& empty_sampling_vars) {
        for(const auto& v: new_sampl_vars) check_var(v);
        for(const auto& v: empty_sampling_vars) check_var(v);
        std::set<uint32_t> sampling_vars_set(new_sampl_vars.begin(), new_sampl_vars.end());
        std::set<uint32_t> opt_sampling_vars_set(opt_sampl_vars.begin(), opt_sampl_vars.end());
        constexpr bool debug_w = false;
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
        sampl_vars = solver->translate_sampl_set(new_sampl_vars);
        opt_sampl_vars = solver->translate_sampl_set(opt_sampl_vars);
        auto empty_sampling_vars2 = solver->translate_sampl_set(empty_sampling_vars);
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

    bool evaluate(const std::vector<CMSat::lbool>& vals, uint32_t var) const {
        check_var(var);
        if (defs[var] == nullptr) {
            std::cout << "ERROR: Variable " << var+1 << " not defined" << std::endl;
            assert(defs[var] != nullptr && "Must be defined");
            exit(EXIT_FAILURE);
        }
        return AIG::evaluate(vals, defs[var], defs);
    }

    std::set<uint32_t> get_vars_need_definition() const {
        std::set<uint32_t> ret;
        std::set<uint32_t> osv(opt_sampl_vars.begin(), opt_sampl_vars.end());
        for(uint32_t i = 0; i < defs.size(); i++) {
            if (defs[i] == nullptr && !osv.count(i))
                ret.insert(i);
        }
        return ret;
    }

    bool aig_contains(const aig_ptr& aig, const uint32_t v) const {
        check_var(v);
        if (aig == nullptr) return false;
        assert(aig->invariants());
        if (aig->type == AIGT::t_lit) {
            if (aig->var == v) return true;

            /// Need to be recursive
            if (defs[aig->var] != nullptr) {
                const auto& aig2 = defs[aig->var];
                return aig_contains(aig2, v);
            }
            return false;
        }
        if (aig->type == AIGT::t_const) return false;
        if (aig->type == AIGT::t_and) {
            return aig_contains(aig->l, v) || aig_contains(aig->r, v);
        }
        assert(false && "Unknown AIG type");
        exit(EXIT_FAILURE);
    }

    // returns in CNF (new vars) the dependencies of each variable
    // every LHS element in the map is a backward_defined variable
    std::map<uint32_t, std::set<uint32_t>> compute_backw_dependencies() {
        std::map<uint32_t, std::set<uint32_t>> ret;
        for(uint32_t orig_v = 0; orig_v < defs.size(); orig_v ++) {
            // Skip orig sampl vars
            if (orig_sampl_vars.count(orig_v)) continue; // if orig_sampl_var, skip
            if (!defined(orig_v)) continue; // if undefined, skip
            if (orig_to_new_var.count(orig_v) == 0) continue; // if NOT mapped to CNF, skip
            const CMSat::Lit n = orig_to_new_var.at(orig_v);
            assert(n != CMSat::lit_Undef);

            // var n IS backward_defined
            auto ret_orig = get_dependent_vars_recursive(defs[orig_v], orig_v);
            std::set<uint32_t> ret_new;
            for(const auto& ov: ret_orig) {
                if(!orig_to_new_var.count(ov)) continue;
                if (orig_sampl_vars.count(ov)) continue; //orig sampl vars not included
                const CMSat::Lit nl = orig_to_new_var.at(ov);
                assert(nl != CMSat::lit_Undef);
                ret_new.insert(nl.var());
            }
            if (ret_new.empty()) continue; //unsat defined
            ret[n.var()] = ret_new;
        }
        return ret;
    }

    // Serialize SimplifiedCNF to binary file
    void write_aig_defs(std::ofstream& out) const {
        // Write simple fields
        out.write((char*)&nvars, sizeof(nvars));
        out.write((char*)&backbone_done, sizeof(backbone_done));
        out.write((char*)&proj, sizeof(proj));
        out.write((char*)&need_aig, sizeof(need_aig));

        // Write sampl_vars
        uint32_t sz = sampl_vars.size();
        out.write((char*)&sz, sizeof(sz));
        out.write((char*)sampl_vars.data(), sz * sizeof(uint32_t));

        // Write opt_sampl_vars
        sz = opt_sampl_vars.size();
        out.write((char*)&sz, sizeof(sz));
        out.write((char*)opt_sampl_vars.data(), sz * sizeof(uint32_t));

        // Write clauses
        sz = clauses.size();
        out.write((char*)&sz, sizeof(sz));
        for (const auto& cl : clauses) {
            uint32_t cl_sz = cl.size();
            out.write((char*)&cl_sz, sizeof(cl_sz));
            for (const auto& lit : cl) {
                uint32_t v = lit.var();
                bool sign = lit.sign();
                out.write((char*)&v, sizeof(v));
                out.write((char*)&sign, sizeof(sign));
            }
        }

        // Write red_clauses
        sz = red_clauses.size();
        out.write((char*)&sz, sizeof(sz));
        for (const auto& cl : red_clauses) {
            uint32_t cl_sz = cl.size();
            out.write((char*)&cl_sz, sizeof(cl_sz));
            for (const auto& lit : cl) {
                uint32_t v = lit.var();
                bool sign = lit.sign();
                out.write((char*)&v, sizeof(v));
                out.write((char*)&sign, sizeof(sign));
            }
        }

        // Write orig_to_new_var
        sz = orig_to_new_var.size();
        out.write((char*)&sz, sizeof(sz));
        for (const auto& [orig, n] : orig_to_new_var) {
            out.write((char*)&orig, sizeof(orig));
            uint32_t lit_var = n.var();
            bool lit_sign = n.sign();
            out.write((char*)&lit_var, sizeof(lit_var));
            out.write((char*)&lit_sign, sizeof(lit_sign));
        }

        // 1. Collect all unique AIG nodes by traversing the DAG
        std::map<AIG*, uint32_t> node_to_id;
        std::vector<AIG*> id_to_node;
        uint32_t next_id = 0;

        std::function<void(const aig_ptr&)> collect = [&](const aig_ptr& aig) {
            if (!aig || node_to_id.count(aig.get())) return;
            node_to_id[aig.get()] = next_id++;
            id_to_node.push_back(aig.get());
            if (aig->type == AIGT::t_and) {
                collect(aig->l);
                collect(aig->r);
            }
        };

        for (const auto& aig : defs) collect(aig);

        // 2. Write number of nodes
        uint32_t num_nodes = id_to_node.size();
        out.write((char*)&num_nodes, sizeof(num_nodes));

        // 3. Write each node (postorder: children before parents)
        for (AIG* node : id_to_node) {
            out.write((char*)&node->type, sizeof(node->type));
            out.write((char*)&node->var, sizeof(node->var));
            out.write((char*)&node->neg, sizeof(node->neg));
            if (node->type == AIGT::t_and) {
                uint32_t lid = node_to_id[node->l.get()];
                uint32_t rid = node_to_id[node->r.get()];
                out.write((char*)&lid, sizeof(lid));
                out.write((char*)&rid, sizeof(rid));
            }
        }

        // 4. Write defs map
        uint32_t num_defs = defs.size();
        out.write((char*)&num_defs, sizeof(num_defs));
        for (const auto& aig : defs) {
            uint32_t aid = node_to_id[aig.get()];
            out.write((char*)&aid, sizeof(aid));
        }
    }

    // Deserialize SimplifiedCNF from binary file
    void read_aig_defs(std::ifstream& in) {
        // Read simple fields
        in.read((char*)&nvars, sizeof(nvars));
        in.read((char*)&backbone_done, sizeof(backbone_done));
        in.read((char*)&proj, sizeof(proj));
        in.read((char*)&need_aig, sizeof(need_aig));

        // Read sampl_vars
        uint32_t sz;
        in.read((char*)&sz, sizeof(sz));
        sampl_vars.resize(sz);
        in.read((char*)sampl_vars.data(), sz * sizeof(uint32_t));

        // Read opt_sampl_vars
        in.read((char*)&sz, sizeof(sz));
        opt_sampl_vars.resize(sz);
        in.read((char*)opt_sampl_vars.data(), sz * sizeof(uint32_t));

        // Read clauses
        in.read((char*)&sz, sizeof(sz));
        clauses.resize(sz);
        for (uint32_t i = 0; i < sz; i++) {
            uint32_t cl_sz;
            in.read((char*)&cl_sz, sizeof(cl_sz));
            clauses[i].resize(cl_sz);
            for (uint32_t j = 0; j < cl_sz; j++) {
                uint32_t v;
                bool sign;
                in.read((char*)&v, sizeof(v));
                in.read((char*)&sign, sizeof(sign));
                clauses[i][j] = CMSat::Lit(v, sign);
            }
        }

        // Read red_clauses
        in.read((char*)&sz, sizeof(sz));
        red_clauses.resize(sz);
        for (uint32_t i = 0; i < sz; i++) {
            uint32_t cl_sz;
            in.read((char*)&cl_sz, sizeof(cl_sz));
            red_clauses[i].resize(cl_sz);
            for (uint32_t j = 0; j < cl_sz; j++) {
                uint32_t v;
                bool sign;
                in.read((char*)&v, sizeof(v));
                in.read((char*)&sign, sizeof(sign));
                red_clauses[i][j] = CMSat::Lit(v, sign);
            }
        }

        // Read orig_to_new_var
        in.read((char*)&sz, sizeof(sz));
        orig_to_new_var.clear();
        for (uint32_t i = 0; i < sz; i++) {
            uint32_t orig, lit_var;
            bool lit_sign;
            in.read((char*)&orig, sizeof(orig));
            in.read((char*)&lit_var, sizeof(lit_var));
            in.read((char*)&lit_sign, sizeof(lit_sign));
            orig_to_new_var[orig] = CMSat::Lit(lit_var, lit_sign);
        }

        // Read AIGs
        uint32_t num_nodes;
        in.read((char*)&num_nodes, sizeof(num_nodes));

        // Read all nodes
        std::vector<aig_ptr> id_to_node(num_nodes);
        for (uint32_t i = 0; i < num_nodes; i++) {
            auto node = std::make_shared<AIG>();
            in.read((char*)&node->type, sizeof(node->type));
            in.read((char*)&node->var, sizeof(node->var));
            in.read((char*)&node->neg, sizeof(node->neg));
            if (node->type == AIGT::t_and) {
                uint32_t lid, rid;
                in.read((char*)&lid, sizeof(lid));
                in.read((char*)&rid, sizeof(rid));
                assert(id_to_node[lid] != nullptr);
                assert(id_to_node[rid] != nullptr);
                node->l = id_to_node[lid];
                node->r = id_to_node[rid];
            }
            id_to_node[i] = node;
        }

        // Read defs map
        uint32_t num_defs;
        in.read((char*)&num_defs, sizeof(num_defs));
        defs.clear();
        for (uint32_t i = 0; i < num_defs; i++) {
            uint32_t aig;
            in.read((char*)&aig, sizeof(aig));
            defs[i] = id_to_node[aig];
        }
    }

    // Write AIG defs to file (opens file for you)
    void write_aig_defs_to_file(const std::string& fname) const {
        std::ofstream out(fname, std::ios::binary);
        if (!out) {
            std::cerr << "ERROR: Cannot open file for writing: " << fname << std::endl;
            exit(EXIT_FAILURE);
        }
        write_aig_defs(out);
        out.close();
        std::cout << "c o Wrote AIG defs: " << fname << std::endl;
    }

    // Read AIG defs from file (opens file for you)
    void read_aig_defs_from_file(const std::string& fname) {
        std::ifstream in(fname, std::ios::binary);
        if (!in) {
            std::cerr << "ERROR: Cannot open file for reading: " << fname << std::endl;
            exit(EXIT_FAILURE);
        }
        read_aig_defs(in);
        in.close();
    }
    std::vector<CMSat::lbool> extend_sample(const std::vector<CMSat::lbool>& sample) const {
        assert(sample.size() == nvars);
        auto ext_sample(sample);
        assert(sample.size() == nvars);
        assert(need_aig && "AIG definitions must be present to extend samples");
        for(uint32_t v = 0; v < nvars; v++) {
            if (defs[v] == nullptr) continue;
            assert(defs[v]->invariants());
            assert(v < nvars);
            CMSat::lbool val = AIG::evaluate(sample, defs[v], defs) ? CMSat::l_True : CMSat::l_False;
            assert(sample[v] == CMSat::l_Undef && "Sample variable already assigned");
            ext_sample[v] = val;
        }
        return ext_sample;
    }

    void map_aigs_to_orig(std::map<uint32_t, std::shared_ptr<AIG>>& aigs, uint32_t max_num_vars) {
        const auto new_to_orig_var = get_new_to_orig_var();
        std::function<void(const aig_ptr&)> remap_aig = [&](const aig_ptr& aig) {
            if (aig == nullptr) return;
            if (aig->marked()) return;
            assert(aig->invariants());
            aig->set_mark();

            if (aig->type == AIGT::t_lit) {
                uint32_t v = aig->var;
                assert(v < max_num_vars);
                aig->var = new_to_orig_var.at(v).var();
                aig->neg ^= new_to_orig_var.at(v).sign();
                return;
            }
            if (aig->type == AIGT::t_and) {
                remap_aig(aig->l);
                remap_aig(aig->r);
                return;
            }
            if (aig->type == AIGT::t_const) return;
            assert(false && "Unknown AIG type");
            exit(EXIT_FAILURE);
        };

        for(auto& [v, aig]: aigs) AIG::unmark_all(aig);
        for(auto& [v, aig]: aigs) remap_aig(aig);
        for(auto& [v, aig]: aigs) {
            auto l = new_to_orig_var.at(v);
            assert(defs[l.var()] == nullptr && "Variable must not already have a definition");
            assert(orig_sampl_vars.count(l.var()) == 0 && "Original sampling var cannot have definition via unsat_define or backward_round_synth");
            if (l.sign()) defs[l.var()] = AIG::new_not(aig);
            else defs[l.var()] = aig;
        }
    }

    SimplifiedCNF get_cnf(
            std::unique_ptr<CMSat::SATSolver>& solver,
            const std::vector<uint32_t>& new_sampl_vars,
            const std::vector<uint32_t>& empty_sampl_vars,
            uint32_t verb
    ) const {
        assert(defs_invariant());

        SimplifiedCNF scnf(fg);
        std::vector<CMSat::Lit> clause;
        bool is_xor, rhs;
        scnf.weighted = weighted;
        scnf.proj = get_projected();
        scnf.new_vars(solver->simplified_nvars());
        scnf.aig_mng = aig_mng;
        scnf.need_aig = need_aig;
        if (need_aig) {
            scnf.defs = defs;
            scnf.aig_mng = aig_mng;
            scnf.set_orig_sampl_vars(orig_sampl_vars);
            scnf.set_orig_clauses(orig_clauses);
        }

        if (verb >= 5) {
            for(const auto& v: new_sampl_vars)
                std::cout << "c o [w-debug] get_cnf sampl var: " << v+1 << std::endl;
            for(const auto& v: opt_sampl_vars)
                std::cout << "c o [w-debug] get_cnf opt sampl var: " << v+1 << std::endl;
            for(const auto& v: empty_sampl_vars)
                std::cout << "c o [w-debug] get_cnf empty sampl var: " << v+1 << std::endl;
        }

        {// We need to fix weights here via cnf2
            auto cnf2(*this);
            cnf2.fix_weights(solver, new_sampl_vars, empty_sampl_vars);
            solver->start_getting_constraints(false, true);
            if (cnf2.weighted) {
                std::map<CMSat::Lit, std::unique_ptr<CMSat::Field>> outer_w;
                for(const auto& [v, w]: cnf2.weights) {
                    const CMSat::Lit l(v, false);
                    outer_w[l] = w.pos->dup();
                    outer_w[~l] = w.neg->dup();
                    if (verb >= 5) {
                        std::cout << "c o [w-debug] outer_w " << l << " w: " << *w.pos << std::endl;
                        std::cout << "c o [w-debug] outer_w " << ~l << " w: " << *w.neg << std::endl;
                    }
                }

                const auto trans = solver->get_weight_translation();
                std::map<CMSat::Lit, std::unique_ptr<CMSat::Field>> inter_w;
                for(const auto& w: outer_w) {
                    CMSat::Lit orig = w.first;
                    CMSat::Lit t = trans[orig.toInt()];
                    inter_w[t] = w.second->dup();
                }

                for(const auto& myw: inter_w) {
                    if (myw.first.var() >= scnf.nvars) continue;
                    if (verb >= 5)
                        std::cout << " c o [w-debug] int w: " << myw.first << " " << *myw.second << std::endl;
                    scnf.set_lit_weight(myw.first, myw.second);
                }
            }
            *scnf.multiplier_weight = *cnf2.multiplier_weight;

            // Map orig set to new set
            scnf.set_sampl_vars(solver->translate_sampl_set(cnf2.sampl_vars));
            scnf.set_opt_sampl_vars(solver->translate_sampl_set(cnf2.opt_sampl_vars));
            std::sort(scnf.sampl_vars.begin(), scnf.sampl_vars.end());
            std::sort(scnf.opt_sampl_vars.begin(), scnf.opt_sampl_vars.end());
        }

        // Get clauses
        while(solver->get_next_constraint(clause, is_xor, rhs)) {
            assert(!is_xor); assert(rhs);
            scnf.clauses.push_back(clause);
        }

        // Get fixed and BVE AIG mapping
        if (need_aig) {
            get_fixed_values(scnf, solver);
            get_bve_mapping(scnf, solver, verb);
        }
        solver->end_getting_constraints();

        // RED clauses
        solver->start_getting_constraints(true, true);
        while(solver->get_next_constraint(clause, is_xor, rhs)) {
            assert(!is_xor); assert(rhs);
            scnf.red_clauses.push_back(clause);
        }
        solver->end_getting_constraints();


        if (verb >= 5) {
            std::cout << "w-debug AFTER PURA FINAL sampl_vars    : ";
            for(const auto& v: scnf.sampl_vars) {
                std::cout << v+1 << " ";
            }
            std::cout << std::endl;
            std::cout << "w-debug AFTER PURA FINAL opt_sampl_vars: ";
            for(const auto& v: scnf.opt_sampl_vars) std::cout << v+1 << " ";
            std::cout << std::endl;
        }

        // Now we do the mapping. Otherwise, above will be complicated
        // This ALSO gets all the fixed values
        scnf.orig_to_new_var = solver->update_var_mapping(orig_to_new_var);
        fix_mapping_after_renumber(scnf, verb);

        assert(scnf.defs_invariant());
        return scnf;
    }

    // when 2 vars point to the same new var, we must set define one by the other.
    // We must prefer orig_sampl_vars to remain undefined, and define the other by it.
    void fix_mapping_after_renumber(SimplifiedCNF& scnf, const uint32_t verb) const {
        std::cout << "c o [get-cnf] Checking for variables mapping to same new var to set AIG definitions..." << std::endl;
        std::map<uint32_t, std::vector<uint32_t>> new_var_to_origs;
        for(const auto& it: scnf.orig_to_new_var) {
            auto& orig = it.first;
            auto& n = it.second;
            new_var_to_origs[n.var()].push_back(orig);
        }

        for(const auto& it: new_var_to_origs) {
            const auto& origs = it.second;
            if (origs.size() <= 1) continue;

            std::cout << "c o [get-cnf] Found " << origs.size()
                << " original vars mapping to new var " << CMSat::Lit(it.first, false) << ": ";
            for(const auto& o: origs)
                std::cout << CMSat::Lit(o, false) << " ";
            std::cout << std::endl;

            // Find which orig to keep undefined (prefer orig_sampl_vars)
            uint32_t orig_to_keep = UINT32_MAX;
            for(const auto& o: origs) {
                if (scnf.orig_sampl_vars.count(o)) {
                    orig_to_keep = o;
                    break;
                }
            }
            if (orig_to_keep == UINT32_MAX)
                orig_to_keep = origs[0];

            std::cout << "c o [get-cnf] Keeping orig var " << CMSat::Lit(orig_to_keep, false)
                << " undefined, defining others by it." << std::endl;

            for(const auto& o: origs) {
                if (o ==  orig_to_keep) continue;
                assert(scnf.defs[o] == nullptr);
                CMSat::Lit n = scnf.orig_to_new_var.at(o);
                CMSat::Lit n2 = scnf.orig_to_new_var.at(orig_to_keep);
                scnf.orig_to_new_var.erase(o);
                scnf.defs[o] = AIG::new_lit(CMSat::Lit(orig_to_keep, n.sign() ^ n2.sign()));
                if (verb >= 1)
                    std::cout << "c o [get-cnf] set aig for var: " << CMSat::Lit(o, false)
                        << " to that of " << CMSat::Lit(orig_to_keep, false)
                        << " since both map to the same new var " << n << std::endl;
            }
        }
    }

    void get_fixed_values(
        SimplifiedCNF& scnf,
        std::unique_ptr<CMSat::SATSolver>& solver) const
    {
        auto new_to_orig_var = get_new_to_orig_var();
        auto fixed = solver->get_zero_assigned_lits();
        for(const auto& l: fixed) {
            CMSat::Lit orig_lit = new_to_orig_var.at(l.var());
            orig_lit ^= l.sign();
            scnf.defs[orig_lit.var()] = scnf.aig_mng.new_const(!orig_lit.sign());
        }
    }

    // Get back BVE AIGs into scnf.defs
    void get_bve_mapping(SimplifiedCNF& scnf, std::unique_ptr<CMSat::SATSolver>& solver,
            const uint32_t verb) const {
        std::vector<uint32_t> vs = solver->get_elimed_vars();
        const auto new_to_orig_var = get_new_to_orig_var();
        assert(defs_invariant());

        // We are all in NEW here. So we need to map back to orig, both the
        // definition and the target
        auto map_cl_to_orig = [&new_to_orig_var](const std::vector<std::vector<CMSat::Lit>>& def) {
            std::vector<std::vector<CMSat::Lit>> ret;
            for(const auto& cl: def) {
                std::vector<CMSat::Lit> new_cl;
                for(const auto& l: cl) {
                    assert(new_to_orig_var.count(l.var()) && "Must be in the new var set");
                    const CMSat::Lit l2 = new_to_orig_var.at(l.var());
                    new_cl.push_back(l2 ^ l.sign());
                }
                ret.push_back(new_cl);
            }
            return ret;
        };

        for(const auto& target: vs) {
            auto def = solver->get_cls_defining_var(target);
            auto orig_def = map_cl_to_orig(def);
            auto orig_target = new_to_orig_var.at(target);

            uint32_t pos = 0;
            uint32_t neg = 0;
            for(const auto& cl: orig_def) {
                bool found_this_cl = false;
                for(const auto& l: cl) {
                    if (l.var() != orig_target.var()) continue;
                    found_this_cl = true;
                    if (l.sign()) neg++;
                    else pos++;
                }
                assert(found_this_cl);
            }
            bool sign = neg > pos;

            auto overall = scnf.aig_mng.new_const(false);
            for(const auto& cl: orig_def) {
                auto current = scnf.aig_mng.new_const(true);

                // Make sure only one side is used, the smaller side
                bool ok = false;
                for(const auto& l: cl) {
                    if (l.var() == orig_target.var()) {
                        if (l.sign() == sign) ok = true;
                        break;
                    }
                }
                if (!ok) continue;

                for(const auto& l: cl) {
                    if (l.var() == orig_target.var()) continue;
                    auto aig = AIG::new_lit(~l);
                    current = AIG::new_and(current, aig);
                }
                overall = AIG::new_or(overall, current);
            }
            if (sign) overall = AIG::new_not(overall);
            assert(scnf.get_orig_sampl_vars().count(orig_target.var()) == 0 &&
                "Elimed variable cannot be in the orig sampling set");
            if (orig_target.sign()) overall = AIG::new_not(overall);
            scnf.defs[orig_target.var()] = overall;
            if (verb >= 5)
                std::cout << "c o [bve-aig] set aig for var: " << orig_target << " from bve elim" << std::endl;
        }

        // Finally, set defs for replaced vars that are elimed
        auto pairs = solver->get_all_binary_xors(); // [replaced, replaced_with]
        std::map<uint32_t, std::vector<CMSat::Lit>> var_to_lits_it_replaced;
        for(const auto& [orig, replacement] : pairs) {
            var_to_lits_it_replaced[replacement.var()].push_back(orig ^ replacement.sign());
        }
        for(const auto& target: vs) {
            for(const auto& l: var_to_lits_it_replaced[target]) {
                auto orig_target = new_to_orig_var.at(target);
                auto orig_lit = new_to_orig_var.at(l.var()) ^ l.sign();
                const auto aig = scnf.defs[orig_target.var()];
                assert(aig != nullptr);
                assert(scnf.defs[orig_lit.var()] == nullptr);
                assert(scnf.get_orig_sampl_vars().count(orig_lit.var()) == 0 &&
                    "Replaced variable cannot be in the orig sampling set here -- we would have elimed what it got replaced with");
                if (orig_lit.sign()) {
                    scnf.defs[orig_lit.var()] = AIG::new_not(aig);
                } else {
                    scnf.defs[orig_lit.var()] = aig;
                }
                if (verb >= 5)
                    std::cout << "c o [bve-aig] replaced var: " << orig_lit
                        << " with aig of " << orig_target << std::endl;
            }
        }
    }

    void set_backbone_done(const bool bb_done) {
        backbone_done = bb_done;
    }

    // Used after SBVA to replace clauses
    void replace_clauses_with(std::vector<int>& ret, uint32_t new_nvars, uint32_t new_nclauses) {
        nvars = new_nvars;
        clauses.clear();
        std::vector<CMSat::Lit> cl;
        uint32_t at = 0;
        while(ret.size() > at) {
            int l = ret[at++];
            if (l == 0) {
                add_clause(cl);
                cl.clear();
                continue;
            }
            cl.push_back(CMSat::Lit(std::abs(l)-1, l < 0));
        }
        assert(cl.empty() && "SBVA should have ended with a 0");
        assert(clauses.size() == new_nclauses && "Number of clauses mismatch after SBVA");
    }

    // Used after BCE to replace clauses
    struct BCEClause {
        uint32_t at = std::numeric_limits<uint32_t>::max();
        std::vector<CMSat::Lit> lits;
        bool red = false;
    };
    void replace_clauses_with(std::vector<BCEClause>& cls) {
        clauses.clear();
        for(const auto& cl: cls) {
            if (!cl.red) add_clause(cl.lits);
            else add_red_clause(cl.lits);
        }
    }
    void set_after_backward_round_synth() {
        assert(!after_backward_round_synth && "Should only be set once");
        after_backward_round_synth = true;
    }
    const auto& get_orig_to_new_var() const {
        return orig_to_new_var;
    }

private:
    bool after_backward_round_synth = false;
    bool need_aig = false;
    std::vector<std::vector<CMSat::Lit>> clauses;
    std::vector<std::vector<CMSat::Lit>> red_clauses;
    bool proj = false;
    bool sampl_vars_set = false;
    bool opt_sampl_vars_set = false;
    std::vector<uint32_t> sampl_vars;
    std::vector<uint32_t> opt_sampl_vars; // During synthesis this is EXACTY the same as sampl_vars

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
    std::map<uint32_t, CMSat::Lit> orig_to_new_var; // ONLY maps in the CNF -- does NOT map to vars NOT in the CNF
    AIGManager aig_mng; // only for const true/false
    std::vector<aig_ptr> defs; //definition of variables in terms of AIG. ORIGINAL number space. Size is the
                               //original number of variables.

    // debug
    bool orig_sampl_vars_set = false;
    std::set<uint32_t> orig_sampl_vars;
    std::vector<std::vector<CMSat::Lit>> orig_clauses;
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
    static std::string get_version_sha1();
    static std::string get_thanks_info(const char* prefix = "c o ");
    static std::string get_sbva_version_sha1();
    static std::string get_compilation_env();
    static std::string get_solver_version_sha1();
    static std::string get_solver_thanks_info(const char* prefix);

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

} // end namespace
