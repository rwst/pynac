/** @file inifcns_hyperg.cpp
 *
 *  Implementation of hypergeometric functions.
 *
 *  (C) 2016 Ralf Stephan <ralf@ark.in-berlin.de>
 */

/*
 *  GiNaC Copyright (C) 1999-2008 Johannes Gutenberg University Mainz, Germany
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */

#include "inifcns.h"
#include "ex.h"
#include "constant.h"
#include "infinity.h"
#include "numeric.h"
#include "add.h"
#include "mul.h"
#include "power.h"
#include "operators.h"
#include "relational.h"
#include "symbol.h"
#include "pseries.h"
#include "utils.h"
#include "py_funcs.h"

#include <vector>
#include <stdexcept>
#include <sstream>
#include <string>
#include <memory>

namespace GiNaC {

inline void py_error(const char* errmsg) {
        throw std::runtime_error((PyErr_Occurred() != nullptr) ? errmsg:
                        "pyerror() called but no error occurred!");
}

// Creates the hypergeometric Python BuiltinFunction object
ex _2F1(ex a, ex b, ex c, ex x)
{
        exvector avec, bvec;
        avec.push_back(a);
        avec.push_back(b);
        bvec.push_back(c);
        PyObject *lista = py_funcs.exvector_to_PyTuple(avec);
        PyObject *listb = py_funcs.exvector_to_PyTuple(bvec);
        PyObject *z = py_funcs.ex_to_pyExpression(x);

        PyObject* m = PyImport_ImportModule("sage.functions.hypergeometric");
        if (m == nullptr)
                py_error("Error importing hypergeometric");
        PyObject* hypfunc = PyObject_GetAttrString(m, "hypergeometric");
        if (hypfunc == nullptr)
                py_error("Error getting hypergeometric attribute");

        PyObject* name = PyString_FromString(const_cast<char*>("__call__"));
        PyObject* pyresult = PyObject_CallMethodObjArgs(hypfunc, name, lista, listb, z, NULL);
        Py_DECREF(m);
        Py_DECREF(name);
        Py_DECREF(hypfunc);
        if (pyresult == nullptr) {
                throw(std::runtime_error("numeric::hypergeometric_pFq(): python function hypergeometric::__call__ raised exception"));
        }
        if ( pyresult == Py_None ) {
                throw(std::runtime_error("numeric::hypergeometric_pFq(): python function hypergeometric::__call__ returned None"));
        }
        // convert output Expression to an ex
        ex eval_result = py_funcs.pyExpression_to_ex(pyresult);
        Py_DECREF(pyresult);
        if (PyErr_Occurred() != nullptr) {
                throw(std::runtime_error("numeric::hypergeometric_pFq(): python function (Expression_to_ex) raised exception"));
        }
        return eval_result;
}


//////////
// Appell F1 function
//////////

static ex appellf1_evalf(const ex& a, const ex& b1, const ex& b2, const ex& c, const ex& x, const ex& y, PyObject* parent)
{
	/*if (is_exactly_a<numeric>(a) and is_exactly_a<numeric>(b1)
            and is_exactly_a<numeric>(b2) and is_exactly_a<numeric>(c)
            and is_exactly_a<numeric>(x) and is_exactly_a<numeric>(y)) {
                return appellf1(ex_to<numeric>(a), ex_to<numeric>(b1),
                                ex_to<numeric>(b2), ex_to<numeric>(c),
                                ex_to<numeric>(x), ex_to<numeric>(y));
	}*/
	return appell_F1(a, b1, b2, c, x, y).hold();
}

static ex appellf1_eval(const ex& a, const ex& b1, const ex& b2, const ex& c, const ex& x, const ex& y)
{
	if (is_exactly_a<numeric>(a) and is_exactly_a<numeric>(b1)
            and is_exactly_a<numeric>(b2) and is_exactly_a<numeric>(c)
            and is_exactly_a<numeric>(x) and is_exactly_a<numeric>(y)) {
                return appellf1_evalf(a, b1, b2, c, x, y, nullptr);
	}

        if (x.is_zero())
                return _2F1(a, b2, c, y);
        if (y.is_zero())
                return _2F1(a, b1, c, x);
        if (x.is_equal(y))
                return _2F1(a, b1+b2, c, x);
        if (c.is_equal(b1+b2))
                return power(1-y, -a) * _2F1(a, b1, b1+b2, (x-y)/(_ex1-y));

	return appell_F1(a, b1, b2, c, x, y).hold();
}

static ex appellf1_deriv(const ex& a, const ex& b1, const ex& b2, const ex& c, const ex& x, const ex& y, unsigned deriv_param)
{
	GINAC_ASSERT(deriv_param==4 || deriv_param==5);
	
	// d/dx F1(a,b1,b2,c,x,y) --> a*b1/c*F1(a+1,b1+1,b2,c+1,x,y)
	// d/dy F1(a,b1,b2,c,x,y) --> a*b2/c*F1(a+1,b1,b2+1,c+1,x,y)
        if (deriv_param == 4)
        	return mul(mul(mul(a, b1), pow(c, -1)), appell_F1(a+1, b1+1, b2, c+1, x, y));
        return mul(mul(mul(a, b2), pow(c, -1)), appell_F1(a+1, b1, b2+1, c+1, x, y));
}

REGISTER_FUNCTION(appell_F1, eval_func(appellf1_eval).
                        evalf_func(appellf1_evalf).
                        derivative_func(appellf1_deriv).
		        latex_name("\\operatorname{F_1}"));

// ---------------------------------------------------------------------
// The following should get its own file at some time
class rubi_exception : public std::runtime_error {
        public:
                rubi_exception() : std::runtime_error("") {}
};

static ex replace_integrals(bool& res, const ex& the_ex, const ex& xe);
static ex hyperg_rubi(const ex& e, const ex& xe);

bool hyperg_integration_rules(ex& res, const ex& e, const ex& xe)
{
        static unsigned intgr_serial = function::find_function("integrate", 2);
        if (not is_exactly_a<symbol>(xe))
                throw std::runtime_error("apply_hyperg_integration_rules(): not a symbol");
        if (not has_symbol(e, ex_to<symbol>(xe)))
                return false;
        auto functions = e.functions();
        if (functions.size() == 1
            and *(functions.begin()) == intgr_serial) {
                bool ret = false;
                try {
                        res = replace_integrals(ret, e, xe);
                        return ret;
                }
                catch (std::runtime_error) {
                        return false;
                }
        }
        return false;
}

static ex replace_integrals(bool& ret, const ex& the_ex, const ex& x)
{
        static unsigned intgr_serial = function::find_function("integrate", 2);
        if (is_exactly_a<constant>(the_ex)
            or is_exactly_a<numeric>(the_ex)
            or is_exactly_a<symbol>(the_ex))
                return the_ex;
        if (is_exactly_a<power>(the_ex)) {
                power pow = ex_to<power>(the_ex);
                return power(replace_integrals(ret, pow.op(0), x),
                             replace_integrals(ret, pow.op(1), x));
        }
        if (is_a<mul>(the_ex)) {
                const expairseq& epseq = ex_to<expairseq>(the_ex);
                exvector vec;
                for (unsigned int i=0; i<epseq.nops(); i++)
                        vec.push_back(replace_integrals(ret, epseq.op(i), x));
                return mul(vec);
        }
        if (is_a<add>(the_ex)) {
                const expairseq& epseq = ex_to<expairseq>(the_ex);
                exvector vec;
                for (unsigned int i=0; i<epseq.nops(); i++)
                        vec.push_back(replace_integrals(ret, epseq.op(i), x));
                return add(vec);
        }

        if (is_exactly_a<function>(the_ex)) {
                function f = ex_to<function>(the_ex);
                if (f.get_serial() != intgr_serial)
                        throw std::runtime_error("replace_integrals: can't happen");
                if (f.nops() != 2)
                        return the_ex;
                try {
                        ret = true;
                        return hyperg_rubi(f.op(0), x);
                }
                catch (rubi_exception) {
                        return the_ex;
                }
        }
        return the_ex;
}

// 1.1.2.H 1/2/4
// bc-ad == 0 is already handled
static ex rubi112H(ex a, ex b, ex m, ex c, ex d, ex n, ex x)
{
std::cerr<<m.info(info_flags::integer)<<","<<n.info(info_flags::integer)<<","<<a<<","<<b<<","<<m<<","<<c<<","<<d<<","<<n<<std::endl;
        if (a.is_zero()) {
                a.swap(c);
                b.swap(d);
                m.swap(n);
        }
std::cerr<<m.info(info_flags::integer)<<","<<n.info(info_flags::integer)<<","<<a<<","<<b<<","<<m<<","<<c<<","<<d<<","<<n<<std::endl;
//        if ((not m.info(info_flags::integer)
//             or not is_exactly_a<numeric>(m))
//            and (not n.info(info_flags::integer)
//             or not is_exactly_a<numeric>(n)))
        if (not n.info(info_flags::integer)) {
                if (m.is_equal(_ex_1)) {
                        if (a.is_zero())
                                return -power(c+d*x,n+1)/b/c/(n+1) * _2F1(_ex1, n+1, n+2, d*x/c+1);
                        return -power(c+d*x,n+1)/(b*c-a*d)/(n+1) * _2F1(_ex1, n+1, n+2, (b*(c+d*x)/(b*c-a*d)).normal());
                }
                if (a.is_zero()
                    and (m.info(info_flags::integer)
                    or (-d/b/c).info(info_flags::positive)))
                        return power(c+d*x,n+1)/d/(n+1)/power(-d/b/c,m) * _2F1(-m, n+1, n+2, _ex1+d*x/c);
        }
        if (not m.info(info_flags::integer)) {
                if (n.is_equal(_ex_1)) {
                        if (c.is_zero())
                                return -power(a+b*x,m+1)/a/d/(m+1) * _2F1(_ex1, m+1, m+2, b*x/a+1);
                        return -power(a+b*x,m+1)/(a*d-b*c)/(m+1) * _2F1(_ex1, m+1, m+2, (d*(a+b*x)/(a*d-b*c)).normal());
                }
                if (c.is_zero()
                    and (n.info(info_flags::integer)
                    or (-b/d/a).info(info_flags::positive)))
                        return power(a+b*x,m+1)/b/(m+1)/power(-b/d/a,n) * _2F1(-n, m+1, m+2, _ex1+b*x/a);
        }
        return power(-b*c+a*d,m) * power(c+d*x,n+1) / power(d,m+1) / (n+1) * _2F1(-m, n+1, n+2, -b*(c+d*x)/(-b*c+a*d));
        throw rubi_exception();
}

static ex rubi113H(ex a, ex b, ex m, ex c, ex d, ex n, ex e, ex f, ex p, ex x)
{
        // 1.1.3.H.1/2
        if ((m+n+p+2).is_zero()) {
                if (m.info(info_flags::integer)
                    and m.info(info_flags::negative)) {
                        m.swap(n);
                        a.swap(c);
                        b.swap(d);
                }
                else if (p.info(info_flags::integer)
                    and p.info(info_flags::negative)) {
                        p.swap(n);
                        e.swap(c);
                        f.swap(d);
                }
                if (n.info(info_flags::integer)
                    and n.info(info_flags::negative)) {
                        return power(b*c-a*d,n) * power(a+b*x,m+1) / (m+1) / power(b*e-a*f,n+1) / power(e+f*x,m+1) * _2F1(m+1, -n, m+2, -(d*e-c*f)*(a+b*x)/(b*c-a*d)/(e+f*x));
                }
                return power(a+b*x,m+1) * power(c+d*x,n) * power(e+f*x,p+1) / (m+1) / (b*e-a*f) * power((b*e-a*f)*(c+d*x)/(b*c-a*d)/(e+f*x),-n) * _2F1(m+1, -n, m+2, -(d*e-c*f)*(a+b*x)/(b*c-a*d)/(e+f*x));
        }
        // 1.1.3.A.1
        if (c.is_zero()) {
                c.swap(a);
                d.swap(b);
                n.swap(m);
        }
        if (e.is_zero()) {
                e.swap(a);
                f.swap(b);
                p.swap(m);
        }
        if (a.is_zero()) {
                if (c.info(info_flags::positive)
                    and not (m+1).is_zero()
                    and (p.info(info_flags::integer)
                         or e.info(info_flags::positive)))
                        return power(c,n)*power(e,p)*power(b*x,m+1)/b/(m+1) * appellf1_eval(m+1, -n, -p, m+2, -d/c*x, -f/e*x);
                if (e.info(info_flags::positive)
                    and not (m+1).is_zero()
                    and (n.info(info_flags::integer)
                         or c.info(info_flags::positive)))
                        return power(e,p)*power(c,n)*power(b*x,m+1)/b/(m+1) * appellf1_eval(m+1, -p, -n, m+2, -f/e*x, -d/c*x);
        }
        // 1.1.3.A.2
        if (m.info(info_flags::integer)) {
                m.swap(p);
                a.swap(e);
                b.swap(f);
        }
        else if (n.info(info_flags::integer)) {
                n.swap(p);
                c.swap(e);
                d.swap(f);
        }
        if (p.info(info_flags::integer))
                return power(b*e-a*f,p) * power(a+b*x,m+1) / power(b,p+1) / (m+1) / power(b / (b*c-a*d), n) * appellf1_eval(m+1, -n, -p, m+2, -d*(a+b*x)/(b*c-a*d), -f*(a+b*x)/(b*e-a*f));
        // 1.1.3.A.3
        return power(a+b*x,m+1) / b / (m+1) / power(b/(b*c-a*d),n) / power(b/(b*e-a*f),p) * appellf1_eval(m+1, -n, -p, m+2, -d*(a+b*x)/(b*c-a*d), -f*(a+b*x)/(b*e-a*f));
}

static ex rubi121H(ex a, ex b, ex c, ex p, ex x)
{
        ex q = sqrt(b*b - _ex4*a*c);
        if (q.is_zero())
                throw rubi_exception();

        return -power(a+b*x+c*x*x,p+1) / q / (p+1) / power((q-b-_ex2*c*x)/_ex2/q,p+1) * _2F1(-p, p+1, p+2, (b+q+_ex2*c*x)/_ex2/q);
}

static ex rubi131H(ex a, ex b, ex n, ex p, ex x)
{
        if (a.is_zero())
                throw rubi_exception();

        return x*power(a+b*power(x,n),p+1)/a * _2F1(_ex1, p+_ex1/n+1, _ex1/n+1, -b*power(x,n)/a);
}

static ex rubi132H(ex c, ex m, ex a, ex b, ex n, ex p, ex x)
{
        if (p.info(info_flags::integer)
            or a.info(info_flags::negative))
                throw rubi_exception();
        return power(c*x,m+1) * power(a+b*power(x,n),p+1) / a / c / (m+1) * _2F1(_ex1, (m+1)/n+p+1, (m+1)/n+1, -b/a*power(x,n));
}

static ex rubi133H(ex a, ex b, ex c, ex d, ex n, ex p, ex q, ex x)
{
        if ((n*(p+q+1)+1).is_zero()) {
                if (p.info(info_flags::integer)
                    and p.info(info_flags::negative))
                        return power(a,p)*x/power(c,p+1)/power(c+d*power(x,n),_ex1/n) * _2F1(_ex1/n, -p, _ex1+_ex1/n, -(b*c-a*d)*power(x,n)/a/(c+d*power(x,n)));
                if (q.info(info_flags::integer)
                    and q.info(info_flags::negative))
                        return power(c,q)*x/power(a,q+1)/power(a+b*power(x,n),_ex1/n) * _2F1(_ex1/n, -q, _ex1+_ex1/n, (b*c-a*d)*power(x,n)/c/(a+b*power(x,n)));
                return power(a+b*power(x,n),p)*x/c/power(c/a*(a+b*power(x,n))/(c+d*power(x,n)),p)/power(c+d*power(x,n),_ex1/n+p) * _2F1(_ex1/n, -p, _ex1+_ex1/n, -(b*c-a*d)*power(x,n)/a/(c+d*power(x,n)));
        }
        throw rubi_exception();
}

static ex rubi134H(ex m, ex a, ex b, ex n, ex p, ex c, ex d, ex q, ex x)
{
        if (m.is_equal(_ex_1) or (m-n).is_equal(_ex_1)
            or a.info(info_flags::negative)
            or c.info(info_flags::negative))
                throw rubi_exception();
        return power(a,p)*power(c,q)*power(x,m+1)/(m+1) * appellf1_eval((m+1)/n, -p, -q, (m+1)/n+1, -b/a*power(x,n), -d/c*power(x,n));
}

static ex rubi138H(ex a, ex j, ex b, ex n, ex p, ex x)
{
        if ((j*p+1).is_zero())
                return x * power(a*power(x,j)+b*power(x,n), p) / p / (n-j) / power(power((a*power(x,j)+b*power(x,n))/b/power(x,n), p)) * _2F1(-p, -p, -p+1, -a/b/power(x,n-j));
        if ((n*p+1).is_zero())
                return x * power(a*power(x,j)+b*power(x,n), p) / p / (j-n) / power(power((a*power(x,j)+b*power(x,n))/a/power(x,j), p)) * _2F1(-p, -p, -p+1, -b/a/power(x,j-n));
        return x * power(a*power(x,j)+b*power(x,n), p) / (j*p+1) / power(power((a*power(x,j)+b*power(x,n))/a/power(x,j), p)) * _2F1(-p, (j*p+1)/(n-j), (j*p+1)/(n-j)+1, -b/a*power(x,n-j));
}

static ex rubi139H(ex m, ex a, ex j, ex b, ex n, ex p, ex x)
{
        if ((m+j*p+1).is_zero())
                return power(a*power(x,j)+b*power(x,n),p+1) / b / p / (n-j) / power(x,n+j*p) * _2F1(_ex1, _ex1, _ex1-p, -a/b/power(x,n-j));
        if ((m+n*p+1).is_zero())
                return power(a*power(x,j)+b*power(x,n),p+1) / a / p / (j-n) / power(x,j+n*p) * _2F1(_ex1, _ex1, _ex1-p, -b/a/power(x,j-n));
        if ((m+n+(p-1)*j+1).is_zero())
                return power(a*power(x,j)+b*power(x,n),p+1) / b / (p+1) / (n-j) / power(x,_ex2*n+j*(p+1)) * _2F1(_ex1, _ex2, _ex2-p, -a/b/power(x,n-j));
        if ((m+j+(p-1)*n+1).is_zero())
                return power(a*power(x,j)+b*power(x,n),p+1) / a / (p+1) / (j-n) / power(x,_ex2*j+n*(p+1)) * _2F1(_ex1, _ex2, _ex2-p, -b/a/power(x,j-n));
        return power(x,m-j+1) * power(a*power(x,j)+b*power(x,n),p+1) / a / (m+j*p+1)  * _2F1(_ex1, (m+n*p+1)/(n-j)+1, (m+j*p+1)/(n-j)+1, -b/a*power(x,n-j));
}

static ex hyperg_rubi(const ex& e, const ex& xe)
{
        const symbol& x = ex_to<symbol>(xe);
        if (not has_symbol(e, x))
                return e*x;
        if (e.is_equal(x))
                return power(x, _ex2) / _ex2;
        ex the_ex = e;
        (void)the_ex.expand();
        if (is_exactly_a<add>(the_ex)) {
                const add& m = ex_to<add>(the_ex);
                exvector vec;
                for (unsigned int i=0; i<m.nops(); i++)
                        vec.push_back(hyperg_rubi(m.op(i), ex(x)));
                return add(vec);
        }
        if (is_exactly_a<mul>(the_ex)) {
                const mul& mu = ex_to<mul>(the_ex);
                exvector cvec, xvec;
                for (unsigned int i=0; i<mu.nops(); i++) {
                        if (has_symbol(mu.op(i), x))
                                xvec.push_back(mu.op(i));
                        else
                                cvec.push_back(mu.op(i));
                }
                if (not cvec.empty())
                        return mul(cvec) * hyperg_rubi(mul(xvec), x);
                exvector bvec, evec;
                for (const auto& term : xvec) {
                        if (is_exactly_a<power>(term)) {
                                bvec.push_back(ex_to<power>(term).op(0));
                                evec.push_back(ex_to<power>(term).op(1));
                        }
                        else {
                                bvec.push_back(term);
                                evec.push_back(_ex1);
                        }
                }
                // exponentials ---> bailout
                for (const auto& eterm : evec)
                        if (has_symbol(eterm, x))
                                throw rubi_exception();

                if (xvec.size() == 2) {
                        ex a, b, c, d, j, k, m, n;
                        if (bvec[0].is_linear(x, a, b)
                            and bvec[1].is_linear(x, c, d))
                                return rubi112H(a, b, evec[0], c, d, evec[1], x);
                        
                        if (bvec[0].is_linear(x, c, d)
                            and c.is_zero()
                            and bvec[1].is_binomial(x, a, j, b, n)) {
                                if (j.is_zero())
                                        return rubi132H(d, evec[0], a, b, n, evec[1], x);
                                if (n.is_zero())
                                        return rubi132H(d, evec[0], b, a, j, evec[1], x);
                                return power(d,evec[0]) * rubi139H(evec[0], a, j, b, n, evec[1], x);
                        }
                        if (bvec[1].is_linear(x, a, b)
                            and a.is_zero()
                            and bvec[0].is_binomial(x, c, j, d, n)) {
                                if (j.is_zero())
                                        return rubi132H(b, evec[1], c, d, n, evec[0], x);
                                if (n.is_zero())
                                        return rubi132H(b, evec[1], d, c, j, evec[0], x);
                                return power(b,evec[1]) * rubi139H(evec[1], c, j, d, n, evec[0], x);
                        }
                        if (bvec[0].is_binomial(x, a, j, b, n)
                            and bvec[1].is_binomial(x, c, k, d, m)
                            and (j*n).is_zero()
                            and (k*m).is_zero()
                            and (j+n).is_equal(k+m)) {
                                if (n.is_zero()) {
                                        a.swap(b);
                                        j.swap(n);
                                }
                                if (m.is_zero()) {
                                        c.swap(d);
                                        k.swap(m);
                                }
                                return rubi133H(a,b,c,d,n,evec[0],evec[1],x);
                        }
                }
                if (xvec.size() == 3) {
                        ex a, b, c, d, ee, f;
                        if (bvec[0].is_linear(x, a, b)
                            and bvec[1].is_linear(x, c, d)
                            and bvec[2].is_linear(x, ee, f))
                                return rubi113H(a, b, evec[0], c, d, evec[1], ee, f, evec[2], x);
                        ex e1, e2, e3, e4, e5, e6;
                        if (bvec[0].is_binomial(x, a, e1, b, e2)
                            and bvec[1].is_binomial(x, c, e3, d, e4)
                            and bvec[2].is_binomial(x, ee, e5, f, e6)
                            and (e1*e2).is_zero()
                            and (e3*e4).is_zero()
                            and (e5*e6).is_zero()
                            and (a*c*ee*b*d*f).is_zero()) {
                                if (bvec[0].is_equal(x)) {
                                        if (e4.is_zero()) {
                                                e3.swap(e4);
                                                c.swap(d);
                                        }
                                        if (e6.is_zero()) {
                                                e5.swap(e6);
                                                ee.swap(f);
                                        }
                                        if (not e3.is_equal(e5))
                                                throw rubi_exception();
                                        return rubi134H(evec[0],c,d,e4,evec[1],ee,f,evec[2],x);
                                }
                                if (bvec[1].is_equal(x)) {
                                        if (e2.is_zero()) {
                                                e1.swap(e2);
                                                a.swap(b);
                                        }
                                        if (e6.is_zero()) {
                                                e5.swap(e6);
                                                ee.swap(f);
                                        }
                                        if (not e1.is_equal(e5))
                                                throw rubi_exception();
                                        return rubi134H(evec[1],a,b,e2,evec[0],ee,f,evec[2],x);
                                }
                                if (bvec[2].is_equal(x)) {
                                        if (e4.is_zero()) {
                                                e3.swap(e4);
                                                c.swap(d);
                                        }
                                        if (e2.is_zero()) {
                                                e1.swap(e2);
                                                a.swap(b);
                                        }
                                        if (not e3.is_equal(e1))
                                                throw rubi_exception();
                                        return rubi134H(evec[2],c,d,e4,evec[1],a,b,evec[0],x);
                                }
                        }
                }
                throw rubi_exception();
        }
        ex a, b, c, j, n;
        if (is_exactly_a<power>(e)) {
                const power& p = ex_to<power>(e);
                const ex& ebas = p.op(0);
                const ex& m = p.op(1);
                if (not has_symbol(ebas, x)
                    or has_symbol(m, x))
                        throw rubi_exception();
                if (ebas.is_binomial(x, a, j, b, n)) {
                        if (j.is_zero())
                                return rubi131H(a, b, n, m, ex(x));
                        else if (n.is_zero())
                                return rubi131H(b, a, j, m, ex(x));
                        else
                                return rubi138H(a, j, b, n, m, ex(x));
                }
                if (ebas.is_quadratic(x, a, b, c)) {
                        if (b.is_zero())
                                return rubi131H(a, c, _ex2, m, ex(x));
                        else
                                return rubi121H(a, b, c, m, ex(x));
                }
        }
        throw rubi_exception();
}

} // namespace GiNaC
