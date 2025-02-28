/******************************************
Copyright (C) 2025 Mate Soos

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

#include <iostream>
#include <gmpxx.h>
#include <solvertypesmini.h>
#include <complex>

class FMpq : public CMSat::Field {
private:
    mpq_class val;

public:
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

    template<class T>
    inline uint64_t helper(const T& v) const {
      return v->_mp_alloc * sizeof(mp_limb_t);
    }

    inline uint64_t bytes_used() const override {
      return sizeof(mpq_class) +
          helper(val.get_num().get_mpz_t()) + helper(val.get_den().get_mpz_t());
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
            if (!parse_int(exp, str, at, line_no)) return false;
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


class FComplex : public CMSat::Field {
private:
    std::complex<mpq_class> val;

public:
    FComplex() { val = std::complex<mpq_class>(0, 0); }
    FComplex(const std::complex<mpq_class>& _val) : val(_val) {}
    FComplex(const mpq_class& _real, const mpq_class& _imag) : val(_real, _imag) {}
    FComplex(const FComplex& other) : val(other.val) {}

    Field& operator=(const Field& other) override {
        const auto& od = dynamic_cast<const FComplex&>(other);
        val = od.val;
        return *this;
    }

    Field& operator+=(const Field& other) override {
        const auto& od = dynamic_cast<const FComplex&>(other);
        val += od.val;
        return *this;
    }

    Field& operator-=(const Field& other) override {
        const auto& od = dynamic_cast<const FComplex&>(other);
        val -= od.val;
        return *this;
    }

    Field& operator*=(const Field& other) override {
        const auto& od = dynamic_cast<const FComplex&>(other);
        val *= od.val;
        return *this;
    }

    Field& operator/=(const Field& other) override {
        const auto& od = dynamic_cast<const FComplex&>(other);
        if (od.val.real() == 0) throw std::runtime_error("Division by zero");
        val /= od.val;
        return *this;
    }

    std::ostream& display(std::ostream& os) const override {
        os << val.real() << " + " << val.imag() << "i";
        return os;
    }

    std::unique_ptr<Field> dup() const override {
        return std::make_unique<FComplex>(val);
    }

    bool is_zero() const override {
        return val.real() == 0 && val.imag() == 0;
    }

    bool is_one() const override {
        return val.real() == 1 && val.imag() == 0;
    }

    void set_zero() override {
        val.real() = 0;
        val.imag() = 0;
    }

    void set_one() override {
        val.real() = 1;
        val.imag() = 0;
    }

    template<class T>
    inline uint64_t helper(const T& v) const {
      return v->_mp_alloc * sizeof(mp_limb_t);
    }

    inline uint64_t bytes_used() const override {
      return 2*sizeof(mpq_class) +
          helper(val.imag().get_num().get_mpz_t()) + helper(val.imag().get_den().get_mpz_t()) +
          helper(val.real().get_num().get_mpz_t()) + helper(val.real().get_den().get_mpz_t());
    }

    bool parse(const std::string& str, const uint32_t line_no) override {
        uint32_t at = 0;
        FMpq real;
        if (!real.parse_mpq(str, at, line_no)) return false;
        skip_whitespace(str, at);
        FMpq imag;
        if (str[at] == '+') {
            at++;
            if (!imag.parse_mpq(str, at, line_no)) return false;
            skip_whitespace(str, at);
            if (str[at] != 'i') {
                std::cerr << "PARSE ERROR! Expected 'i' at end of complex number"
                << " At line " << line_no << " Probably looks like 1+2i"
                << std::endl;
                return false;
            }
            at++;
        }
        val = std::complex<mpq_class>(real.get_val(), imag.get_val());
        return true;
    }
};

class FGenComplex : public CMSat::FieldGen {
public:
    ~FGenComplex() override = default;
    std::unique_ptr<CMSat::Field> zero() const override {
        return std::make_unique<FComplex>();
    }

    std::unique_ptr<CMSat::Field> one() const override {
        return std::make_unique<FComplex>(1, 0);
    }

    std::unique_ptr<FieldGen> dup() const override {
        return std::make_unique<FGenComplex>();
    }

    bool weighted() const override { return true; }
};
