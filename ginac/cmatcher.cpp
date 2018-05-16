// cmatcher.cpp: commutative matching
// Distributed under GPL2+
// Author: 2018: Ralf Stephan <ralf@ark.in-berlin.de>
//
// This differs from GiNaC's original basic::match() because commutative
// structures need a special algorithm. We follow the outline in
// Manuel Krebber's Master Thesis, "Non-linear Associative-Commutative
// Many-to-One Pattern Matching with Sequence Variables", section 3.2
// https://arxiv.org/abs/1705.00907
//
// Features:
//       - commutative matching (sums and products, backtracking also in
//         powers and functions)
//       - more than two args with noncommutative functions
//
// TODO:
//       - one "global wildcard" (i.e. x^+ in a f_C, see basic::match)
//       - "zero wildcards" (matching superfluous wilds with 0(+) or 1(*)
//       - constant wildcards (those lacking specified symbols)
//       - commutative functions
//       - more than one global wildcard (i.e., fully sequential)

#include "cmatcher.h"
#include "expairseq.h"
#include "symbol.h"
#include "wildcard.h"
#include "power.h"
#include "function.h"
#include "operators.h"
#include "utils.h"

#include <unistd.h>
#include <iostream>
#include <algorithm>

#define DEBUG if(debug)

namespace GiNaC {

static bool debug=true;
int CMatcher::level = 0;

inline bool is_ncfunc(const ex& e)
{
        return is_exactly_a<power>(e)
            or is_exactly_a<function>(e)
            or is_exactly_a<exprseq>(e)
            or is_exactly_a<lst>(e);
}

inline bool is_func(const ex& e)
{
        return is_ncfunc(e)
            or is_a<expairseq>(e);
}

inline CMatcher& CMatcher::make_cmatcher(const ex& e, size_t i, exmap& mm)
{
        exmap m = mm;
        cms[i].emplace(CMatcher(e, pat[i], m));
        return cms[i].value();
}

inline bool CMatcher::get_alt(size_t i)
{
        if (not m_cmatch[i])
                return false;
        CMatcher& cm = cms[i].value();
        if (cm.ret_val) {
                bool ret = cm.ret_val.value();
                if (ret) {
                        ret_map = cm.ret_map.value();
                        cm.ret_map.reset();
                }
                cm.ret_val.reset();
                return ret;
        }
        if (cm.finished)
                return false;
        bool ret;
        cm.map_repo[0] = cm.map = map_repo[i];
        const opt_exmap& opm = cm.get();
        ret_map = opm;
        ret_val = ret = opm? true : false;
        cm.clear_ret();
        if (not cm.finished)
                finished = false;
        return ret;
}

opt_bool CMatcher::init()
{
        DEBUG std::cerr<<level<<" cmatch: "<<source<<", "<<pattern<<", "<<map<<std::endl;
        const size_t snops = source.nops(), pnops = pattern.nops();
	if (is_exactly_a<wildcard>(pattern)) {
                DEBUG std::cerr << "pattern is single wildcard"<<std::endl;
                const auto& it = map.find(pattern);
                finished = true;
                if (it != map.end()) {
		        if (not source.is_equal(ex_to<basic>(it->second)))
                                return false;
                        ret_map = map;
                        return true;
                }
		map[pattern] = source;
                ret_map = map;
		return true;
	} 
	if (ex_to<basic>(source).tinfo() != ex_to<basic>(pattern).tinfo()) {
                DEBUG std::cerr<<"pattern type mismatch"<<std::endl;
                return false;
        }
        if (is_exactly_a<function>(source)
           and ex_to<function>(source).get_serial()
            != ex_to<function>(pattern).get_serial()) {
                DEBUG std::cerr<<"function type mismatch"<<std::endl;
                return false;
        }
        if (snops < pnops) {
                DEBUG std::cerr<<"# of source terms > pattern terms"<<std::endl;
                return false;
        }
        symbolset oset = source.symbols();
        symbolset pset = substitute(pattern.wilds(), map);
        if (not subset_of(pset, oset)) {
                DEBUG std::cerr<<"substitution has unmatched symbols"<<std::endl;
                return false;
        }

        // Chop into terms
        std::vector<size_t> wild_ind;
        for (size_t i=0; i<snops; i++) {
                ops.push_back(source.op(i));
        }
        for (size_t i=0; i<pnops; i++)
                pat.push_back(pattern.op(i).subs(map,
                                        subs_options::no_pattern));
        for (size_t i=0; i<pat.size(); ++i)
                if (is_exactly_a<wildcard>(pat[i]))
                        wild_ind.push_back(i);

        if (not is_ncfunc(source)) { // source is commutative
                if (snops > pnops) {
                        if (wild_ind.empty())
                                return false;
                        // we have a global wildcard, i.e., one that matches
                        // more than one term (x^+ in the paper) in a sum or
                        // product
                        global_wild = true;
                        DEBUG std::cerr<<"global wildcard seen: "<<snops<<","<<pnops<<std::endl;
                }
                // Check that all "constants" in the pattern are matched
                // Presets are already substituted now
                for (auto it1 = pat.begin(); it1 != pat.end(); ) {
                        if (haswild(*it1)) {
                                ++it1;
                                continue;
                        }
                        const auto& it2 = std::find_if(ops.begin(), ops.end(),
                                              [it1](const ex& e) {
                                                      return e.is_equal(*it1);
                                              } );
                        if (it2 != ops.end()) {
                                DEBUG std::cerr<<level<<" constant "<<*it1<<" found in "<<source<<std::endl;
                                (void)ops.erase(it2);
                                it1 = pat.erase(it1);
                        }
                        else {
                                DEBUG std::cerr<<level<<" constant "<<*it1<<" not found in "<<source<<std::endl;
                                return false;
                        }
                }
        }
        else
        {
                // Check that all "constants" in the pattern are matched
                // Presets are already substituted now
                for (auto it1 = pat.begin(), it2 = ops.begin();
                                it1 != pat.end(); ) {
                        if (haswild(*it1)) {
                                ++it1;
                                ++it2;
                                continue;
                        }
                        if (it2->is_equal(*it1)) {
                                DEBUG std::cerr<<level<<" constant "<<*it1<<" found in "<<source<<std::endl;
                                it2 = ops.erase(it2);
                                it1 = pat.erase(it1);
                        }
                        else {
                                DEBUG std::cerr<<level<<" constant "<<*it1<<" not found in "<<source<<std::endl;
                                return false;
                        }
                }
                if (pat.empty()) {
                        finished = true;
                        ret_map = map;
                        return true;
                }
        }
        if (wild_ind.empty() and ops.empty() and pat.empty()) {
                finished = true;
                ret_map = map;
                return true;
        }
        if (wild_ind.empty() and (ops.empty() or pat.empty()))
                throw std::runtime_error("matching gotcha");

        N = ops.size();
        P = pat.size();
        size_t len = global_wild? N-1 : P;
        m_cmatch = std::vector<int>(len);
        std::transform(ops.begin(), ops.end(), m_cmatch.begin(),
                        [](const ex& e) { return int(is_func(e)); } );
        for (size_t i=0; i<len; ++i)
                cms.emplace_back();
        map_repo = std::vector<exmap>(P);

        finished = false;
        if (is_ncfunc(source)) {
                if (std::all_of(m_cmatch.begin(), m_cmatch.end(),
                                [](bool b) { return not b; } )) {
                        finished = true;
                        for (size_t i=0; i<N; ++i)
                                if (not ops[i].match(pat[i], map))
                                        return false;
                        ret_map = map;
                        DEBUG std::cerr<<"all noncomm matched"<<std::endl;
                        return true;
                }
                return nullopt;
        }
        finished = false;
        if (len == 1
            and not m_cmatch[0]) {
                ret_val = ops[0].match(pat[0], map);
                if (ret_val.value())
                        ret_map = map;
                finished = true;
                return ret_val.value();
        }

        perm.reserve(len);
        for (size_t i=0; i<len; ++i) {
                perm.push_back(i);
        }
        return nullopt;
}

void CMatcher::run()
{
        if (finished or
            (not is_ncfunc(source) and perm.empty())) {
                ret_val = false;
                return;
        }
        clear_ret();
        if (is_ncfunc(source)) {
                noncomm_run();
                return;
        }

        if (global_wild)
                with_global_wild();
        else
                no_global_wild();
}

void CMatcher::noncomm_run()
{
        DEBUG std::cerr<<level<<" noncomm_run() entered, N="<<N<<", "<<map<<std::endl;
        int ii = P;
        while (--ii >= 0) {
                if (m_cmatch[ii]
                    and cms[ii]
                    and not cms[ii].value().finished)
                        break;
        }
        size_t index;
        if (ii >= 0) {
                index = static_cast<size_t>(ii);
                while (unsigned(++ii) < P)
                        cms[ii].reset();
        }
        else // no cmatcher or all uninitialized
                index = 0;
        // The second loop increases index to get a new ops term
        do {
                const ex& e = ops[index];
                if (index == 0)
                        map_repo[0] = map;
                else
                        map_repo[index] = map_repo[index-1];
                // At this point we try matching p to e 
                const ex& p = pat[index];
                DEBUG std::cerr<<level<<" index: "<<index<<", op: "<<e<<", pat: "<<p<<std::endl;
                if (not m_cmatch[index]) {
                        // normal matching attempt
                        exmap m = map_repo[index];
                        bool ret = e.match(p, m);
                        if (ret) {
                                map_repo[index] = m;
                                DEBUG std::cerr<<level<<" match found: "<<e<<", "<<p<<", "<<m<<": "<<ret<<std::endl; 
                                continue;
                        }
                        DEBUG std::cerr<<"match failed"<<std::endl;
                }
                else {
                        if (not cms[index])
                                (void)make_cmatcher(e, index, map_repo[index]);
                        else {
                                cms[index].value().ret_val.reset();
                                cms[index].value().finished = false;
                        }
                        if (get_alt(index)) {
                                map_repo[index] = ret_map.value();
                                DEBUG std::cerr<<level<<" cmatch found: "<<e<<", "<<p<<", "<<map_repo[index]<<std::endl; 
                                continue;
                        }
                        cms[index].reset();
                        DEBUG std::cerr<<"cmatch failed"<<std::endl;
                }
                bool alt_solution_found = false;
                int i = static_cast<int>(index);
                while (--i >= 0) {
                        if (cms[i]) {
                           DEBUG std::cerr<<level<<" find alt: "<<i<<std::endl;
                                cms[i].value().ret_val.reset();
                                map = map_repo[i];
                                if (get_alt(i)) {
                                        map_repo[i] = ret_map.value();
                                        index = i;
                                        alt_solution_found = true;
                                        DEBUG std::cerr<<level<<" try alt: "<<i<<", "<<map_repo[i]<<std::endl;
                                        break;
                                }
                                else
                                        cms[i].reset();
                        }
                }
                if (not alt_solution_found)
                        break;
        }
        while (++index < P);

        if (index >= P) {
                DEBUG std::cerr<<level<<" send alt: "<<map_repo[P-1]<<std::endl;
                ret_val = true;
                ret_map = map_repo[P-1];
                return;
        }
        finished = true;
        ret_map.reset();
        ret_val = false;
}

void CMatcher::no_global_wild()
{
        DEBUG std::cerr<<level<<" run() entered"<<std::endl;
        // The outer loop goes though permutations of perm
        while (true) {
                int ii = P;
                while (--ii >= 0) {
                        if (m_cmatch[ii]
                            and cms[ii]
                            and not cms[ii].value().finished)
                                break;
                }
                size_t index;
                if (ii >= 0) {
                        index = static_cast<size_t>(ii);
                        while (unsigned(++ii) < P)
                                cms[ii].reset();
                }
                else // no cmatcher or all uninitialized
                        index = 0;
                finished = true;
                DEBUG { std::cerr<<level<<" ["; for (size_t i:perm) std::cerr<<i<<","; std::cerr<<"]"<<std::endl; }
                // The second loop increases index to get a new ops term
                do {
                        const ex& e = ops[perm[index]];
                        if (index == 0)
                                map_repo[0] = map;
                        else
                                map_repo[index] = map_repo[index-1];
                        // At this point we try matching p to e 
                        const ex& p = pat[index];
                        DEBUG std::cerr<<level<<" index: "<<index<<", op: "<<e<<", pat: "<<p<<std::endl;
                        if (not m_cmatch[index]) {
                                // normal matching attempt
                                exmap m = map_repo[index];
                                bool ret = e.match(p, m);
                                if (ret) {
                                        map_repo[index] = m;
                                        DEBUG std::cerr<<level<<" match found: "<<e<<", "<<p<<", "<<m<<": "<<ret<<std::endl; 
                                        continue;
                                }
                                    DEBUG std::cerr<<"match failed"<<std::endl;
                        }
                        else {
                                if (not cms[index])
                                        (void)make_cmatcher(e, index,
                                                        map_repo[index]);
                                else {
                                        cms[index].value().ret_val.reset();
                                        cms[index].value().finished = false;
                                }
                                if (get_alt(index)) {
                                        map_repo[index] = ret_map.value();
                                        DEBUG std::cerr<<level<<" cmatch found: "<<e<<", "<<p<<", "<<map_repo[index]<<std::endl; 
                                        continue;
                                }
                                else
                                        cms[index].reset();
                                DEBUG std::cerr<<"cmatch failed"<<std::endl;
                        }
                        // did we start coroutines in this permutation?
                        bool alt_solution_found = false;
                        int i = static_cast<int>(index);
                        while (--i >= 0) {
                                if (cms[i]) {
                                        DEBUG std::cerr<<level<<" find alt: "<<i<<std::endl;
                                        cms[i].value().ret_val.reset();
                                        map = map_repo[i];
                                        if (get_alt(i)) {
                                                map_repo[i] = ret_map.value();
                                                index = i;
                                                alt_solution_found = true;
                                                DEBUG std::cerr<<level<<" try alt: "<<i<<", "<<map_repo[i]<<std::endl;
                                                break;
                                        }
                                        cms[i].reset();
                                }
                        }
                        if (not alt_solution_found)
                                break;
                }
                while (++index < P);

                if (index >= P) {
                        // give back one solution of this cmatch call
                        // possibly still permutations left
                        DEBUG std::cerr<<level<<" send alt: "<<map_repo[P-1]<<std::endl;
                        finished = not std::next_permutation(perm.begin(),
                                                perm.end());
                        ret_val = true;
                        ret_map = map_repo[P-1];
                        return;
                }
                else {
                        // no cmatch calls have alternative solutions
                        // to their cmatch, so get the next permutation
                        // that changes current index position
                        size_t old = perm[index];
                        while (perm[index] == old) {
                                bool more = std::next_permutation(perm.begin(),
                                                perm.end());
                                if (not more) {
                                        ret_val = false;
                                        ret_map.reset();
                                        finished = true;
                                        DEBUG std::cerr<<level<<" perms exhausted"<<std::endl;
                                        return;
                                }
                        }
                }
        }
        DEBUG std::cerr<<"noncomm_run() exited"<<std::endl;
        ret_val = false;
}

void CMatcher::with_global_wild()
{
        DEBUG std::cerr<<level<<" gwrun() entered"<<std::endl;
}

}
