/*
 Arjun

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include "verilog.h"
#include <algorithm>
#include <charconv>
#include <functional>
#include <iostream>
#include <iterator>
#include <unordered_map>

using namespace ArjunNS;
using std::vector;
using std::set;
using std::string;
using std::function;

void ArjunInt::write_verilog(std::ostream& out, const vector<aig_lit>& defs, const set<uint32_t>& inputs) {
    // Collect all unique AIG nodes in topological (post) order: children before parents
    std::unordered_map<uint64_t, uint32_t> nid_to_id;
    vector<const AIG*> topo_order;
    vector<uint32_t> lid, rid;

    function<void(const aig_lit&)> collect = [&](const aig_lit& aig) {
        if (!aig || nid_to_id.count(aig->nid)) return;
        uint32_t l = 0, r = 0;
        if (aig->type == AIGT::t_and) {
            collect(aig->l);
            collect(aig->r);
            l = nid_to_id.find(aig->l->nid)->second;
            r = nid_to_id.find(aig->r->nid)->second;
        }
        nid_to_id[aig->nid] = topo_order.size();
        topo_order.push_back(aig.get());
        lid.push_back(l);
        rid.push_back(r);
    };
    for (const auto& aig : defs) collect(aig);
    const uint32_t num_nodes = topo_order.size();

    vector<uint32_t> outputs;
    for (uint32_t v = 0; v < defs.size(); v++) {
        if (defs[v] == nullptr) continue;
        if (inputs.count(v)) continue;
        outputs.push_back(v);
    }

    // Fanout = uses by other AND nodes + output roots. Fanout-1 AND nodes are
    // inlined into their sole user rather than emitted as a named wire.
    vector<uint32_t> fanout(num_nodes, 0);
    for (uint32_t id = 0; id < num_nodes; id++) {
        if (topo_order[id]->type != AIGT::t_and) continue;
        fanout[lid[id]]++;
        // NOT/idem nodes have the same child twice: count it once
        if (rid[id] != lid[id]) fanout[rid[id]]++;
    }
    for (const auto& v : outputs) fanout[nid_to_id.find(defs[v]->nid)->second]++;

    // compound: the inlined node renders as a bare `a & b`, to be
    // parenthesized when composed further
    vector<char> inlined(num_nodes, 0), compound(num_nodes, 0);
    for (uint32_t id = 0; id < num_nodes; id++) {
        const AIG* node = topo_order[id];
        if (node->type != AIGT::t_and) continue;
        inlined[id] = fanout[id] == 1;
        if (node->l == node->r) compound[id] = !node->l.neg && inlined[lid[id]] && compound[lid[id]];
        else compound[id] = 1;
    }

    string buf;
    char num[16];
    auto put_num = [&](uint32_t n) {
        buf.append(num, std::to_chars(num, num + sizeof(num), n).ptr);
    };
    function<void(uint32_t)> put_rhs;
    // Leaves are unsigned, so their sign lives on the edge
    auto put_edge = [&](const aig_lit& e, uint32_t id, bool paren) {
        if (e->type == AIGT::t_const) { buf += e.neg ? "1'b0" : "1'b1"; return; }
        if (e.neg) buf += '~';
        if (e->type == AIGT::t_lit) { buf += 'x'; put_num(e->var + 1); return; }
        if (!inlined[id]) { buf += "_n"; put_num(id); return; }
        const bool wrap = compound[id] && (e.neg || paren);
        if (wrap) buf += '(';
        put_rhs(id);
        if (wrap) buf += ')';
    };
    put_rhs = [&](uint32_t id) {
        const AIG* node = topo_order[id];
        // Idempotent case AND(x, x): render as the child directly.
        if (node->l == node->r) { put_edge(node->l, lid[id], false); return; }
        put_edge(node->l, lid[id], true);
        buf += " & ";
        put_edge(node->r, rid[id], true);
    };
    auto flush = [&] { out.write(buf.data(), buf.size()); buf.clear(); };

    // Module header
    buf += "module aig_defs(\n";
    bool first = true;
    for (const auto& v : inputs) {
        if (!first) buf += ",\n";
        buf += "    input wire x"; put_num(v + 1);
        first = false;
    }
    for (const auto& v : outputs) {
        if (!first) buf += ",\n";
        buf += "    output wire x"; put_num(v + 1);
        first = false;
    }
    buf += "\n);\n";

    for (uint32_t id = 0; id < num_nodes; id++) {
        if (topo_order[id]->type != AIGT::t_and || inlined[id]) continue;
        buf += "    wire _n"; put_num(id); buf += ";\n";
        buf += "    assign _n"; put_num(id); buf += " = ";
        put_rhs(id);
        buf += ";\n";
        if (buf.size() > (1U << 20)) flush();
    }

    // Output assignments
    for (const auto& v : outputs) {
        buf += "    assign x"; put_num(v + 1); buf += " = ";
        put_edge(defs[v], nid_to_id.find(defs[v]->nid)->second, false);
        buf += ";\n";
    }

    buf += "endmodule\n";
    flush();
}

namespace {

enum class Tok { ident, konst, sym, end };
struct Token {
    Tok type;
    char sym = 0;
    bool val = false;
    uint32_t sig = 0;
    uint32_t line = 0;
};

enum class Kind { undeclared, input, output, wire };
struct Signal {
    string name;
    Kind kind = Kind::undeclared;
    uint32_t var = 0;
    // tokens [begin, end) of the assigned expression
    size_t begin = 0;
    size_t end = 0;
    bool assigned = false;
    bool in_progress = false;
    aig_lit val;
};

struct ParseError { string msg; };

struct Reader {
    vector<Token> toks;
    vector<Signal> sigs;
    std::unordered_map<string, uint32_t> name_to_sig;
    size_t at = 0;

    [[noreturn]] static void fail(const uint32_t line, const string& msg) {
        throw ParseError{"line " + std::to_string(line) + ": " + msg};
    }

    uint32_t sig_of(const string& name) {
        auto [it, inserted] = name_to_sig.try_emplace(name, sigs.size());
        if (inserted) { sigs.emplace_back(); sigs.back().name = name; }
        return it->second;
    }

    void tokenize(std::istream& in) {
        const string s((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
        uint32_t line = 1;
        size_t i = 0;
        auto is_id = [](char c) { return isalnum((unsigned char)c) || c == '_' || c == '$'; };
        while (i < s.size()) {
            const char c = s[i];
            if (c == '\n') { line++; i++; continue; }
            if (isspace((unsigned char)c)) { i++; continue; }
            if (c == '/' && i+1 < s.size() && s[i+1] == '/') {
                while (i < s.size() && s[i] != '\n') i++;
                continue;
            }
            if (c == '/' && i+1 < s.size() && s[i+1] == '*') {
                const size_t e = s.find("*/", i+2);
                if (e == string::npos) fail(line, "unterminated comment");
                line += std::count(s.begin()+i, s.begin()+e, '\n');
                i = e+2;
                continue;
            }
            Token t;
            t.line = line;
            if (isdigit((unsigned char)c)) {
                size_t e = i;
                while (e < s.size() && (is_id(s[e]) || s[e] == '\'')) e++;
                const string n = s.substr(i, e-i);
                if (n == "0" || n == "1'b0" || n == "1'h0" || n == "1'd0") t.val = false;
                else if (n == "1" || n == "1'b1" || n == "1'h1" || n == "1'd1") t.val = true;
                else fail(line, "only single-bit constants are handled, got '" + n + "'");
                t.type = Tok::konst;
                i = e;
            } else if (is_id(c)) {
                size_t e = i;
                while (e < s.size() && is_id(s[e])) e++;
                t.type = Tok::ident;
                t.sig = sig_of(s.substr(i, e-i));
                i = e;
            } else if (string("(),;=~!&|^?:").find(c) != string::npos) {
                t.type = Tok::sym;
                t.sym = c;
                i++;
            } else fail(line, string("unexpected character '") + c + "'");
            toks.push_back(t);
        }
        Token t;
        t.type = Tok::end;
        t.line = line;
        toks.push_back(t);
    }

    const Token& peek() const { return toks[at]; }
    bool is_sym(const char c) const { return peek().type == Tok::sym && peek().sym == c; }
    bool is_word(const char* w) const { return peek().type == Tok::ident && sigs[peek().sig].name == w; }
    bool eat_sym(const char c) { if (!is_sym(c)) return false; at++; return true; }
    bool eat_word(const char* w) { if (!is_word(w)) return false; at++; return true; }
    void need_sym(const char c) {
        if (!eat_sym(c)) fail(peek().line, string("expected '") + c + "'");
    }
    uint32_t need_ident() {
        if (peek().type != Tok::ident) fail(peek().line, "expected a name");
        return toks[at++].sig;
    }

    void declare(const uint32_t sig, const Kind kind, const uint32_t line) {
        auto& s = sigs[sig];
        // "output x; wire x;" is fine
        if (kind == Kind::wire && s.kind != Kind::undeclared) return;
        if (s.kind == Kind::input || s.kind == Kind::output) fail(line, "'" + s.name + "' declared twice");
        s.kind = kind;
        if (kind == Kind::wire) return;
        const auto& n = s.name;
        bool ok = n.size() >= 2 && n.size() <= 10 && n[0] == 'x' && n[1] != '0';
        for (size_t i = 1; ok && i < n.size(); i++) ok = isdigit((unsigned char)n[i]);
        if (!ok) fail(line, "port '" + n + "' is not named x<variable number>");
        s.var = std::stoul(n.substr(1)) - 1;
    }

    // "input wire a, b" up to the terminating ';' or ')'
    void declaration(Kind kind, const bool in_ports) {
        while (true) {
            if (in_ports) {
                if (eat_word("input")) kind = Kind::input;
                else if (eat_word("output")) kind = Kind::output;
            }
            eat_word("wire");
            const uint32_t line = peek().line;
            const uint32_t sig = need_ident();
            if (kind != Kind::undeclared) declare(sig, kind, line);
            if (!eat_sym(',')) return;
        }
    }

    void module() {
        if (!eat_word("module")) fail(peek().line, "expected 'module'");
        need_ident();
        if (eat_sym('(')) {
            if (!is_sym(')')) declaration(Kind::undeclared, true);
            need_sym(')');
        }
        need_sym(';');
        while (!eat_word("endmodule")) {
            if (peek().type == Tok::end) fail(peek().line, "missing 'endmodule'");
            if (eat_word("input")) declaration(Kind::input, false);
            else if (eat_word("output")) declaration(Kind::output, false);
            else if (eat_word("wire")) declaration(Kind::wire, false);
            else if (eat_word("assign")) {
                do {
                    const uint32_t line = peek().line;
                    auto& s = sigs[need_ident()];
                    if (s.assigned) fail(line, "'" + s.name + "' assigned twice");
                    need_sym('=');
                    s.assigned = true;
                    s.begin = at;
                    while (!is_sym(';') && !is_sym(',')) {
                        if (peek().type == Tok::end) fail(line, "unterminated assign");
                        at++;
                    }
                    s.end = at;
                } while (eat_sym(','));
            } else fail(peek().line, "expected a declaration or an assign");
            need_sym(';');
        }
        if (peek().type != Tok::end) fail(peek().line, "only one module is handled");
    }

    aig_lit var_lit(const uint32_t var) {
        if (var_lits.size() <= var) var_lits.resize(var+1);
        if (var_lits[var] == nullptr) var_lits[var] = AIG::new_lit(var);
        return var_lits[var];
    }
    vector<aig_lit> var_lits;

    static int prec(const char op) {
        switch (op) {
            case '&': return 4;
            case '^': return 3;
            case '|': return 2;
            default: return 0;
        }
    }

    // Shunting-yard, so that deeply nested parentheses need no recursion
    aig_lit expr(const Signal& s) {
        vector<aig_lit> vals;
        vector<char> ops;
        bool want_operand = true;
        uint32_t line = toks[s.begin].line;
        auto bad = [&] { fail(line, "malformed expression for '" + s.name + "'"); };
        auto negs = [&] {
            while (!ops.empty() && ops.back() == '~') { ops.pop_back(); vals.back() = ~vals.back(); }
        };
        auto reduce = [&] {
            const char op = ops.back();
            ops.pop_back();
            const size_t n = op == ':' ? 3 : 2;
            if (vals.size() < n) bad();
            const aig_lit r = vals.back(); vals.pop_back();
            const aig_lit l = vals.back(); vals.pop_back();
            if (op == '&') vals.push_back(AIG::new_and(l, r));
            else if (op == '|') vals.push_back(AIG::new_or(l, r));
            else if (op == '^') vals.push_back(AIG::new_or(AIG::new_and(l, ~r), AIG::new_and(~l, r)));
            else {
                const aig_lit c = vals.back(); vals.pop_back();
                vals.push_back(AIG::new_ite(l, r, c));
            }
        };
        auto reduce_while = [&](const int min_prec, const bool else_too) {
            while (!ops.empty() && ((prec(ops.back()) && prec(ops.back()) >= min_prec)
                        || (else_too && ops.back() == ':'))) reduce();
        };

        for (size_t i = s.begin; i < s.end; i++) {
            const Token& t = toks[i];
            line = t.line;
            if (want_operand) {
                if (t.type == Tok::sym && (t.sym == '~' || t.sym == '!')) ops.push_back('~');
                else if (t.type == Tok::sym && t.sym == '(') ops.push_back('(');
                else if (t.type == Tok::konst || t.type == Tok::ident) {
                    if (t.type == Tok::konst) vals.push_back(AIG::new_const(t.val));
                    else {
                        const auto& o = sigs[t.sig];
                        vals.push_back(o.kind == Kind::wire ? o.val : var_lit(o.var));
                    }
                    negs();
                    want_operand = false;
                } else bad();
                continue;
            }
            if (t.type != Tok::sym) bad();
            if (t.sym == ')') {
                reduce_while(1, true);
                if (ops.empty() || ops.back() != '(') bad();
                ops.pop_back();
                negs();
                continue;
            }
            if (prec(t.sym)) {
                reduce_while(prec(t.sym), false);
                ops.push_back(t.sym);
            } else if (t.sym == '?') {
                reduce_while(1, false);
                ops.push_back('?');
            } else if (t.sym == ':') {
                reduce_while(1, true);
                if (ops.empty() || ops.back() != '?') bad();
                ops.back() = ':';
            } else bad();
            want_operand = true;
        }
        if (want_operand) bad();
        reduce_while(1, true);
        if (!ops.empty() || vals.size() != 1) bad();
        return vals[0];
    }

    // Wires are built before their users, whatever the order in the file
    void build(const uint32_t top) {
        struct Frame { uint32_t sig; size_t pos; };
        vector<Frame> stack;
        auto enter = [&](const uint32_t sig) {
            sigs[sig].in_progress = true;
            stack.push_back({sig, sigs[sig].begin});
        };
        enter(top);
        while (!stack.empty()) {
            auto& f = stack.back();
            auto& s = sigs[f.sig];
            bool descended = false;
            for (; f.pos < s.end; f.pos++) {
                const Token& t = toks[f.pos];
                if (t.type != Tok::ident) continue;
                const auto& o = sigs[t.sig];
                if (o.kind == Kind::undeclared) fail(t.line, "'" + o.name + "' is not declared");
                if (o.kind != Kind::wire || o.val != nullptr) continue;
                if (!o.assigned) fail(t.line, "wire '" + o.name + "' is never assigned");
                if (o.in_progress) fail(t.line, "wire '" + o.name + "' depends on itself");
                enter(t.sig);
                descended = true;
                break;
            }
            if (descended) continue;
            s.val = expr(s);
            s.in_progress = false;
            stack.pop_back();
        }
    }

    void read(std::istream& in, vector<aig_lit>& defs, set<uint32_t>& inputs) {
        tokenize(in);
        module();
        uint32_t num_vars = 0;
        for (const auto& s : sigs) {
            if (s.kind != Kind::input && s.kind != Kind::output) continue;
            num_vars = std::max(num_vars, s.var+1);
            if (s.kind == Kind::input) inputs.insert(s.var);
        }
        defs.assign(num_vars, aig_lit());
        for (uint32_t i = 0; i < sigs.size(); i++) {
            const auto& s = sigs[i];
            if (!s.assigned) {
                if (s.kind == Kind::output) fail(toks.back().line, "output '" + s.name + "' is never assigned");
                continue;
            }
            if (s.kind == Kind::undeclared) fail(toks[s.begin].line, "'" + s.name + "' is not declared");
            if (s.kind == Kind::input) fail(toks[s.begin].line, "input '" + s.name + "' is assigned");
            if (s.val == nullptr) build(i);
            if (s.kind == Kind::output) defs[s.var] = s.val;
        }
    }
};

}

bool ArjunInt::read_verilog(std::istream& in, vector<aig_lit>& defs, set<uint32_t>& inputs, string& err) {
    defs.clear();
    inputs.clear();
    try {
        Reader().read(in, defs, inputs);
    } catch (const ParseError& e) {
        err = e.msg;
        return false;
    }
    return true;
}
