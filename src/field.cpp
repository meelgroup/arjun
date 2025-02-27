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
#include <stdexcept>
#include "arjun.h"

class FDouble : public Field {
private:
    double val;

public:
    FDouble(double _val) : val(_val) {}

    Field& operator=(const Field& other) override {
        const auto& od = dynamic_cast<const FDouble&>(other);
        val = od.val;
        return *this;
    }

    Field& operator+=(const Field& other) override {
        const auto& od = dynamic_cast<const FDouble&>(other);
        val += od.val;
        return *this;
    }

    Field& operator-=(const Field& other) override {
        const auto& od = dynamic_cast<const FDouble&>(other);
        val -= od.val;
        return *this;
    }

    Field& operator*=(const Field& other) override {
        const auto& od = dynamic_cast<const FDouble&>(other);
        val *= od.val;
        return *this;
    }

    Field& operator/=(const Field& other) override {
        const auto& od = dynamic_cast<const FDouble&>(other);
        if (od.val == 0) throw std::runtime_error("Division by zero");
        val /= od.val;
        return *this;
    }

    std::ostream& display(std::ostream& os) const override {
        os << val;
        return os;
    }

    Field* duplicate() const override {
        return new FDouble(val);
    }

    bool is_zero() const override {
        return val == 0;
    }

    bool is_one() const override {
        return val == 1;
    }
};

class FGenDouble : public FieldGen {
public:
    ~FGenDouble() override = default;
    Field* zero() const override {
        return new FDouble(0);
    }

    Field* one() const override {
        return new FDouble(1.0);
    }

    FieldGen* duplicate() const override {
        return new FGenDouble();
    }
};
