/*
 Arjun

 Copyright (c) 2019-2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include <cstdint>
#include <iostream>
#include <vector>
#include <fstream>
#include <string>
#include <boost/program_options.hpp>
#include <cryptominisat5/dimacsparser.h>
#include <cryptominisat5/solvertypesmini.h>
#ifdef USE_ZLIB
#include <zlib.h>
#endif

#include "arjun.h"

namespace po = boost::program_options;
using std::vector;
using namespace ArjunNS;
using namespace CMSat;
using std::cerr;
using std::cout;
using std::endl;

inline void add_supported_options(int argc, char** argv,
        po::positional_options_description& p,
        po::options_description& help_options,
        po::variables_map& vm, Arjun* arjun)
{
    p.add("input", -1);

    try {
        po::store(po::command_line_parser(argc, argv).
                options(help_options).positional(p).run(), vm);
        if (vm.count("help"))
        {
            cout
            << "Minimal projection set finder and simplifier." << endl << endl
            << "arjun [options] inputfile [outputfile]" << endl;

            cout << help_options << endl;
            std::exit(0);
        }

        if (vm.count("version")) {
            cout << "c [arjun] SHA revision: " << arjun->get_version_info() << endl;
            cout << "c [arjun] Compilation environment: " << arjun->get_compilation_env() << endl;
            std::exit(0);
        }

        po::notify(vm);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::unknown_option> >& c
    ) {
        cerr
        << "ERROR: Some option you gave was wrong. Please give '--help' to get help" << endl
        << "       Unkown option: " << c.what() << endl;
        std::exit(-1);
    } catch (boost::bad_any_cast &e) {
        std::cerr
        << "ERROR! You probably gave a wrong argument type" << endl
        << "       Bad cast: " << e.what()
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::invalid_option_value> >& what
    ) {
        cerr
        << "ERROR: Invalid value '" << what.what() << "'" << endl
        << "       given to option '" << what.get_option_name() << "'"
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::multiple_occurrences> >& what
    ) {
        cerr
        << "ERROR: " << what.what() << " of option '"
        << what.get_option_name() << "'"
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::required_option> >& what
    ) {
        cerr
        << "ERROR: You forgot to give a required option '"
        << what.get_option_name() << "'"
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::too_many_positional_options_error> >& what
    ) {
        cerr
        << "ERROR: You gave too many positional arguments. Only the input CNF can be given as a positional option." << endl;
        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::ambiguous_option> >& what
    ) {
        cerr
        << "ERROR: The option you gave was not fully written and matches" << endl
        << "       more than one option. Please give the full option name." << endl
        << "       The option you gave: '" << what.get_option_name() << "'" <<endl
        << "       The alternatives are: ";
        for(size_t i = 0; i < what.alternatives().size(); i++) {
            cout << what.alternatives()[i];
            if (i+1 < what.alternatives().size()) {
                cout << ", ";
            }
        }
        cout << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::invalid_command_line_syntax> >& what
    ) {
        cerr
        << "ERROR: The option you gave is missing the argument or the" << endl
        << "       argument is given with space between the equal sign." << endl
        << "       detailed error message: " << what.what() << endl
        ;
        std::exit(-1);
    }
}

inline double stats_line_percent(double num, double total)
{
    if (total == 0) {
        return 0;
    } else {
        return num/total*100.0;
    }
}

inline void write_origcnf(Arjun* arjun, vector<uint32_t>& indep_vars,
        const std::string& elimtofile, const uint32_t orig_cnf_must_mult_exp2)
{
    uint32_t num_cls = 0;
    const auto& cnf = arjun->get_orig_cnf();
    for(const auto& l: cnf) if (l == lit_Undef) num_cls++;
    std::ofstream outf;
    outf.open(elimtofile.c_str(), std::ios::out);
    outf << "p cnf " << arjun->get_orig_num_vars() << " " << num_cls << endl;

    //Add projection
    outf << "c ind ";
    std::sort(indep_vars.begin(), indep_vars.end());
    for(const auto& v: indep_vars) {
        assert(v < arjun->get_orig_num_vars());
        outf << v+1  << " ";
    }
    outf << "0\n";

    for(const auto& l: cnf) {
        if (l == lit_Undef) outf << "0\n";
        else outf << l << " ";
    }
    outf << "c MUST MULTIPLY BY 2**" << orig_cnf_must_mult_exp2 << endl;
}

inline void write_simpcnf(const ArjunNS::SimplifiedCNF& simpcnf,
        const std::string& elimtofile, const uint32_t orig_cnf_must_mult_exp2)
{
    uint32_t num_cls = simpcnf.cnf.size();
    std::ofstream outf;
    outf.open(elimtofile.c_str(), std::ios::out);
    outf << "p cnf " << simpcnf.nvars << " " << num_cls << endl;

    //Add projection
    outf << "c ind ";
    for(const auto& v: simpcnf.sampling_vars) {
        assert(v < simpcnf.nvars);
        outf << v+1  << " ";
    }
    outf << "0\n";

    for(const auto& cl: simpcnf.cnf) outf << cl << " 0\n";
    outf << "c MUST MULTIPLY BY 2**" << simpcnf.empty_occs+orig_cnf_must_mult_exp2 << endl;
}

inline void readInAFile(const std::string& filename,
        Arjun* arjun,
        uint32_t& orig_sampling_set_size,
        uint32_t& orig_cnf_must_mult_exp2,
        const bool recompute_sampling_set)
{
    assert(orig_cnf_must_mult_exp2 == 0);
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN>, ArjunNS::Arjun> parser(arjun, NULL, 0);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ>, ArjunNS::Arjun> parser(arjun, NULL, 0);
    #endif

    if (in == NULL) {
        std::cerr
        << "ERROR! Could not open file '"
        << filename
        << "' for reading: " << strerror(errno) << endl;

        std::exit(-1);
    }

    if (!parser.parse_DIMACS(in, true)) {
        exit(-1);
    }

    if (!parser.sampling_vars_found || recompute_sampling_set) {
        orig_sampling_set_size = arjun->start_with_clean_sampling_set();
    } else {
        orig_sampling_set_size = arjun->set_starting_sampling_set(parser.sampling_vars);
    }
    orig_cnf_must_mult_exp2 = parser.must_mult_exp2;

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}
