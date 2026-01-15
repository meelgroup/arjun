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
#include <cstdlib>
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
inline std::ostream& operator<<(std::ostream& os, const AIGT& value) {
    switch (value) {
        case AIGT::t_and:  return os << "t_and";
        case AIGT::t_lit:  return os << "t_lit";
        case AIGT::t_const: return os << "t_const";
        default: assert(false && "Unknown AIGT"); exit(EXIT_FAILURE);
    }
}

class AIG {
public:
    AIG() = default;
    ~AIG() = default;
    AIG(const AIG&) = delete;
    AIG& operator=(const AIG&) = delete;

    bool invariants() const {
        if (type == AIGT::t_lit) {
            if (l != nullptr || r != nullptr) std::cout << "ERROR: AIG literal has children!" << std::endl;
            if (var == none_var) std::cout << "ERROR: AIG var node doesn't have a var!" << std::endl;
            return l == nullptr && r == nullptr && var != none_var;
        }
        if (type == AIGT::t_const) {
            if (l != nullptr || r != nullptr) std::cout << "ERROR: AIG const has children!" << std::endl;
            if (var != none_var) std::cout << "ERROR: AIG const node has var!" << std::endl;
            return l == nullptr && r == nullptr && var == none_var;
        }
        if (type == AIGT::t_and) {
            if (var != none_var) std::cout << "ERROR: AIG AND node has var!" << std::endl;
            if (l == nullptr || r == nullptr) std::cout << "ERROR: AIG AND node missing children!" << std::endl;
            return l != nullptr && r != nullptr && var == none_var;
        }
        assert(false && "Unknown AIG type");
        std::exit(EXIT_FAILURE);
    }

    // vals = input variable assignments
    // aig = AIG to evaluate
    // defs = known definitions of variables
    static CMSat::lbool evaluate(const std::vector<CMSat::lbool>& vals, const aig_ptr& a, const std::vector<aig_ptr>& defs, std::map<aig_ptr, CMSat::lbool>& cache) {
        std::function<CMSat::lbool(const aig_ptr&)> sub_eval = [&](const aig_ptr& aig) -> CMSat::lbool {
            if (cache.count(aig)) return cache.at(aig);
            assert(aig->invariants());
            if (aig->type == AIGT::t_lit) {
                if (defs[aig->var] != nullptr) {
                    auto ret = sub_eval(defs.at(aig->var));
                    if (ret == CMSat::l_Undef) {
                        cache[aig] = CMSat::l_Undef;
                        return CMSat::l_Undef;
                    }
                    ret = ret ^ aig->neg;
                    cache[aig] = ret;
                    return ret;
                } else {
                    assert(aig->var < vals.size());
                    auto ret = vals[aig->var];
                    if (ret == CMSat::l_Undef) {
                        cache[aig] = CMSat::l_Undef;
                        return CMSat::l_Undef;
                    }
                    ret = ret ^ aig->neg;
                    cache[aig] = ret;
                    return ret;
                }
            }

            if (aig->type == AIGT::t_const) return CMSat::boolToLBool(!aig->neg);

            if (aig->type == AIGT::t_and) {
                const auto l = sub_eval(aig->l);
                const auto r = sub_eval(aig->r);
                CMSat::lbool ret;
                if (l ==CMSat::l_Undef && r == CMSat::l_Undef) ret = CMSat::l_Undef;
                else if (l == CMSat::l_False) ret = CMSat::l_False ^ aig->neg;
                else if (r == CMSat::l_False) ret = CMSat::l_False ^ aig->neg;
                else ret = (l && r) ^ aig->neg;
                cache[aig] = ret;
                return ret;
            }
            assert(false && "Unknown AIG type");
            exit(EXIT_FAILURE);
        };
        return sub_eval(a);
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
        assert(l != nullptr);
        assert(r != nullptr);
        auto branch = new_lit(b.var(), b.sign());
        return new_or(new_and(branch, l), new_and(new_not(branch), r));
    }

    static aig_ptr new_not(const aig_ptr& a) {
        assert(a != nullptr);
        auto ret = std::make_shared<AIG>();
        ret->type = AIGT::t_and;
        ret->l = a;
        ret->r = a;

        ret->neg = true;
        return ret;
    }

    static aig_ptr new_and(const aig_ptr& l, const aig_ptr& r) {
        assert(l != nullptr && r != nullptr);
        auto ret = std::make_shared<AIG>();
        ret->type = AIGT::t_and;
        ret->l = l;
        ret->r = r;
        return ret;
    }

    static aig_ptr new_or(const aig_ptr& l, const aig_ptr& r) {
        assert(l != nullptr && r != nullptr);
        auto ret = std::make_shared<AIG>();
        ret->type = AIGT::t_and;
        ret->neg = true;
        ret->l = new_not(l);
        ret->r = new_not(r);
        return ret;
    }

    static aig_ptr simplify(aig_ptr aig, std::set<aig_ptr>& visited);

    static aig_ptr new_ite(const aig_ptr& l, const aig_ptr& r, const aig_ptr& b) {
        assert(l != nullptr);
        assert(r != nullptr);
        assert(b != nullptr);
        return AIG::new_or(AIG::new_and(b, l), AIG::new_and(AIG::new_not(b), r));
    }

    static void get_dependent_vars(const aig_ptr& aig_orig, std::set<uint32_t>& dep, uint32_t v) {
        std::set<aig_ptr> visited;
        std::function<void(const aig_ptr&)> helper =
            [&](const aig_ptr& aig) {
                if (visited.count(aig)) return;
                if (aig->type == AIGT::t_lit) {
                    assert(aig->var != v && "Variable cannot depend on itself");
                    dep.insert(aig->var);
                }
                if (aig->type == AIGT::t_and) {
                    helper(aig->l);
                    helper(aig->r);
                }
                visited.insert(aig);
            };
        helper(aig_orig);
    }

    template<typename T>
    static std::vector<aig_ptr> deep_clone_set(const T& aigs) {
        std::vector<aig_ptr> ret;
        std::map<aig_ptr, aig_ptr> cache;
        for (auto& aig : aigs) ret.push_back(deep_clone(aig, cache));
        return ret;
    }

    template<typename T>
    static T deep_clone_map(const T& aigs) {
        T ret;
        std::map<aig_ptr, aig_ptr> cache;
        for (auto& [x, aig] : aigs) ret[x] = deep_clone(aig, cache);
        return ret;
    }

    static aig_ptr deep_clone(const aig_ptr& aig, std::map<aig_ptr, aig_ptr>& cache) {
        if (!aig) return nullptr;

        std::function<aig_ptr(const aig_ptr&)> clone_helper =
            [&](const aig_ptr& node) -> aig_ptr {
                if (!node) return nullptr;

                // Check cache to avoid cloning the same node multiple times
                auto it = cache.find(node);
                if (it != cache.end()) return it->second;

                // Create new AIG node
                auto cloned = std::make_shared<AIG>();
                cloned->type = node->type;
                cloned->var = node->var;
                cloned->neg = node->neg;

                // Add to cache before recursing to handle cycles
                cache[node] = cloned;

                // Recursively clone children for AND nodes
                if (node->type == AIGT::t_and) {
                    cloned->l = clone_helper(node->l);
                    cloned->r = clone_helper(node->r);
                }

                return cloned;
            };

        return clone_helper(aig);
    }

    // Generic recursive traversal function that applies a function to each AIG node
    // The function receives the current node as an aig_ptr
    // Use cache to avoid visiting the same node multiple times
    template<typename Func>
    static void traverse(const aig_ptr& aig, Func&& func) {
        if (!aig) return;
        std::set<aig_ptr> visited;
        traverse_helper(aig, std::forward<Func>(func), visited);
    }

    template<typename Func>
    static void traverse_helper(const aig_ptr& node, Func&& func, std::set<aig_ptr>& visited) {
        if (!node) return;

        // Check if already visited to avoid infinite loops
        if (visited.count(node)) return;
        visited.insert(node);

        // Apply the function to the current node
        func(node);

        // Recursively traverse children for AND nodes
        if (node->type == AIGT::t_and) {
            traverse_helper(node->l, std::forward<Func>(func), visited);
            traverse_helper(node->r, std::forward<Func>(func), visited);
        }
    }

    // Transform function that performs post-order traversal and builds up a result
    // The visitor receives: (type, var, neg, left_result*, right_result*)
    // - type: the node type (t_const, t_lit, or t_and)
    // - var: variable number (only meaningful for t_lit)
    // - neg: negation flag
    // - left_result, right_result: pointers to children results (nullptr for non-AND nodes)
    template<typename ResultType, typename Visitor>
    static ResultType transform(
        const aig_ptr& aig,
        Visitor&& visitor,
        std::map<aig_ptr, ResultType>& cache
    ) {
        assert(aig);

        // Check cache first
        auto it = cache.find(aig);
        if (it != cache.end()) return it->second;

        ResultType result;
        if (aig->type == AIGT::t_and) {
            // Post-order: process children first
            ResultType left_result = transform<ResultType>(aig->l, std::forward<Visitor>(visitor), cache);
            ResultType right_result = transform<ResultType>(aig->r, std::forward<Visitor>(visitor), cache);
            result = visitor(aig->type, aig->var, aig->neg, &left_result, &right_result);
        } else {
            // Leaf nodes (t_const or t_lit)
            result = visitor(aig->type, aig->var, aig->neg, nullptr, nullptr);
        }

        cache[aig] = result;
        return result;
    }

    friend std::ostream& operator<<(std::ostream& out, const aig_ptr& aig);
    friend class AIGManager;
    friend class SimplifiedCNF;
private:
    AIGT type = AIGT::t_const;
    static constexpr uint32_t none_var = std::numeric_limits<uint32_t>::max();
    uint32_t var = none_var;
    bool neg = false;
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
            defs = AIG::deep_clone_set(other.defs);
            orig_clauses = other.orig_clauses;
            orig_sampl_vars = other.orig_sampl_vars;
            orig_sampl_vars_set = other.orig_sampl_vars_set;
        }
        assert(defs_invariant());

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
    std::tuple<std::set<uint32_t>, std::set<uint32_t>, std::set<uint32_t>> get_var_types([[maybe_unused]] uint32_t verb) const;

    bool check_all_opt_sampl_vars_depend_only_on_orig_sampl_vars() const;
    bool check_orig_sampl_vars_undefined() const;
    bool defs_invariant() const;

    // Get the orig vars this AIG depends on, recursively expanding defined vars
    std::set<uint32_t> get_dependent_vars_recursive(const uint32_t orig_v, std::map<uint32_t, std::set<uint32_t>>& cache) const;

    bool check_aig_cycles() const;
    void check_self_dependency() const;
    void check_cnf_vars() const;

    // all vars are either: in orig_sampl_vars, defined, or in the cnf
    void check_all_vars_accounted_for() const;

    // this checks that NO unsat-define has been made yet
    void check_pre_post_backward_round_synth() const;

    void set_all_opt_indep();
    void add_opt_sampl_var(const uint32_t v);
    void clean_idiotic_mccomp_weights();
    void check_cnf_sampl_sanity() const;

    // Gives all the orig lits that map to this variable
    std::map<uint32_t, std::vector<CMSat::Lit>> get_new_to_orig_var_list() const;

    // Gives an example lit, sometimes good enough
    std::map<uint32_t, CMSat::Lit> get_new_to_orig_var() const;

    uint32_t new_vars(uint32_t vars);
    uint32_t new_var();

    void start_with_clean_sampl_vars();
    void check_var(const uint32_t v) const;
    void check_clause(const std::vector<CMSat::Lit>& cl) const;
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
            assert(opt_sampl_vars_set == false);
            assert(opt_sampl_vars.empty());
        }
        sampl_vars.clear();
        sampl_vars_set = true;
        std::set<uint32_t> tmp(vars.begin(), vars.end());
        sampl_vars.insert(sampl_vars.begin(), tmp.begin(), tmp.end());
        if (!opt_sampl_vars_set) set_opt_sampl_vars(vars);
    }
    template<class T> void set_opt_sampl_vars(const T& vars) {
        for(const auto& v: vars) check_var(v);
        opt_sampl_vars.clear();
        opt_sampl_vars_set = true;
        std::set<uint32_t> tmp(vars.begin(), vars.end());
        opt_sampl_vars.insert(opt_sampl_vars.begin(), tmp.begin(), tmp.end());
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
    void renumber_sampling_vars_for_ganak();

    void write_simpcnf(const std::string& fname, bool red = true) const;

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
            const std::vector<uint32_t>& empty_sampling_vars);

    CMSat::lbool evaluate(const std::vector<CMSat::lbool>& vals, uint32_t var, std::map<aig_ptr, CMSat::lbool>& cache ) const;

    // returns in CNF (new vars) the dependencies of each variable
    // every LHS element in the map is a backward_defined variable
    std::map<uint32_t, std::set<uint32_t>> compute_backw_dependencies();

    // Serialize SimplifiedCNF to binary file
    void write_aig_defs(std::ofstream& out) const;

    // Deserialize SimplifiedCNF from binary file
    void read_aig_defs(std::ifstream& in);

    // Write AIG defs to file (opens file for you)
    void write_aig_defs_to_file(const std::string& fname) const;

    // Read AIG defs from file (opens file for you)
    void read_aig_defs_from_file(const std::string& fname);

    std::vector<CMSat::lbool> extend_sample(const std::vector<CMSat::lbool>& sample, const bool relaxed = false) const;

    void map_aigs_to_orig(const std::map<uint32_t, aig_ptr>& aigs, const uint32_t max_num_vars);

    SimplifiedCNF get_cnf(
            std::unique_ptr<CMSat::SATSolver>& solver,
            const std::vector<uint32_t>& new_sampl_vars,
            const std::vector<uint32_t>& empty_sampl_vars,
            uint32_t verb
    ) const;

    // when 2 vars point to the same new var, we must set define one by the other.
    // We must prefer orig_sampl_vars to remain undefined, and define the other by it.
    void fix_mapping_after_renumber(SimplifiedCNF& scnf, const uint32_t verb) const;

    void get_fixed_values(SimplifiedCNF& scnf, std::unique_ptr<CMSat::SATSolver>& solver) const;
    void set_fixed_values(const std::vector<CMSat::Lit>& lits);


    // Get back BVE AIGs into scnf.defs
    void get_bve_mapping(SimplifiedCNF& scnf, std::unique_ptr<CMSat::SATSolver>& solver, const uint32_t verb) const;

    void set_backbone_done(const bool bb_done) {
        backbone_done = bb_done;
    }

    std::vector<std::vector<uint32_t>> find_disconnected() const;

    // Used after SBVA to replace clauses
    void replace_clauses_with(std::vector<int>& ret, uint32_t new_nvars, uint32_t new_nclauses);

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

    // Get AIG definition for a variable (in ORIG numbering)
    const aig_ptr& get_def(uint32_t v) const {
        assert(v < defs.size());
        return defs[v];
    }
    void clear_orig_sampl_defs();
    void simplify_aigs();

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

    void check_synth_funs_randomly() const;
    bool orig_sampl_vars_set = false;
    std::set<uint32_t> orig_sampl_vars;
    // debug
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
    struct ManthanConf {
        ManthanConf() = default;
        ManthanConf(const ManthanConf& other) = default;
        int do_filter_samples = 1;
        int do_biased_sampling = 0;
        uint32_t num_samples = 10000;
        uint32_t num_samples_ccnr = 3000;
        uint32_t minimumLeafSize = 20;
        double minGainSplit = 0.1;
        uint32_t maximumDepth = 0;
        uint32_t sampler_fixed_conflicts = 100;
        int do_minimize_conflict = 1;
        uint32_t simplify_every = 1000;
        std::string write_manthan_cnf;
        int do_maxsat_better_ctx = 0;
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
    SimplifiedCNF standalone_manthan(const SimplifiedCNF& cnf, const ManthanConf& manthan_conf);

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
    void set_cms_glob_mult(double cms_glob_mult);
    void set_seed(uint32_t seed);

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
    int get_oracle_find_bins() const;
    double get_cms_glob_mult() const;
    uint32_t get_seed() const;

private:
    ArjPrivateData* arjdata = nullptr;
};

} // end namespace
