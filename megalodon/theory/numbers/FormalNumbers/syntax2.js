// File: syntax.js
// Author: Chad E Brown
// Modified by: Julian Backes
// constants (codes)
var otp = 0;
var basetp = 1;
var artp = 2;
var vartrm = 3;
var consttrm = 4;
var apptrm = 5;
var lamtrm = 6;
var deftrm = 7;

var optiontrm = 8;

// flag
var usemathsyms = true;

// globals
var knowncount;
var claimscount;

var typenames;
var termnames; // signature (consts/defns) + ctx (vars)
var varnames; // default types for some variable names
var prefixops;
var prefixopsprint;
var infixops;
var infixopsprint;
var known;
var hyp;
var claims;

var unknowns;

var disallowed;
var nnfbutton = true;
var bext = true;
var xiext = true;
var etaext = true;
var etanorm = true;
var useleo = true;
var eagerdelete = true;

// math symbols and io
var mathsym = null;

var io = null;

// init spec functions
var init_spec_fns = new Array();

function switch_usemathsyms(b) {
	if (usemathsyms) {
		usemathsyms = false;
		b.value = "Use Special Math Symbols";
	} else {
		usemathsyms = true;
		b.value = "ASCII Only (Turn Off Special Math Symbols)";
	}
}

function symbols() {
	if (usemathsyms) {
		this.not = "\u00AC";
		this.or = "\u2228";
		this.and = "\u2227";
		this.implies = "\u2192";
		this.equiv = "\u2194";
		this.all = "\u2200";
		this.ex = "\u2203";
		this.lambda = "\u03BB";
		this.neq = "\u2260";
                this.setmem = "\u2208";
	        this.leq = "\u2264";
	} else {
		this.not = '~';
		this.or = '|';
		this.and = '&';
		this.implies = '->';
		this.equiv = '<->';
		this.all = '!';
		this.ex = '?';
		this.lambda = '\\';
		this.neq = '!=';
                this.setmem = ":e";
	        this.leq = "<=";
	}
}

function ioobj() {
	this.outputtop = top.headerFrame.window.document.getElementById('outputtop');
	this.outputbot = top.footerFrame.window.document.getElementById('outputbot');
	this.inputtop = top.headerFrame.window.document.getElementById('inputtop');
	this.inputbot = top.footerFrame.window.document.getElementById('inputbot');
	this.main = top.mainFrame.window.document.getElementById('main');
	this.maintop = top.mainFrame.window.document.getElementById('maintop');
	this.thf = top.mainFrame.window.document.getElementById('thf');
	this.globaloptions = top.headerFrame.window.document.getElementById('globaloptions');
}

// simple types
function tp_p(a) {
	return ((a.kind == otp) || (a.kind == basetp) || (a.kind == artp));
}

function oo() {
	this.kind = otp;
}

var o = new oo();

function obase(name) {
	this.kind = basetp;
	this.name = name;
}

function base(name) {
	return new obase(name);
}

function oar(a, b) {
	this.kind = artp;
	this.dom = a;
	this.cod = b;
}

function ar(a, b) {
	return new oar(a, b);
}

var oo = ar(o, o);
var ooo = ar(o, oo);

var ltrue = lconst("True", o);
var lfalse = lconst("False", o);

var lnot = lconst("*not*", oo);
var lor = lconst("*or*", ooo);
var land = lconst("*and*", ooo);
var limp = lconst("*imp*", ooo);
var lequiv = lconst("*equiv*", ooo);

// tp to string
function tp_str_pr(a, i) {
	if (a.kind == otp) {
		return "prop";
	} else if (a.kind == basetp) {
		return a.name;
	} else if (a.kind == artp) {
		if (i > 0) {
			return '(' + tp_str_pr(a.dom, 1) + ' ' + tp_str_pr(a.cod, 0) + ')';
		} else {
			return tp_str_pr(a.dom, 1) + ' ' + tp_str_pr(a.cod, 0);
		}
	} else {
		throw ('not a type');
	}
}

function tp_str(a) {
	return tp_str_pr(a, 0);
}

function tp_or_ar(dom, cod) {
	if (cod == null) {
		return dom;
	} else {
		return ar(dom, cod);
	}
}

function eq_tps(a, b) {
	/* uncomment for debugging
    alert ("eq_tps: a = " + a + " b = " + b);
    alert ("a.kind = " + a.kind + " b.kind = " + b.kind);
    alert ("eq_tps: a = " + tp_str(a));
    alert ("eq_tps: b = " + tp_str(b));
*/
	if (a.kind == b.kind) {
		if (a.kind == basetp) {
			return (a.name == b.name);
		} else if (a.kind == artp) {
			eq_tps(a.dom, b.dom);
			eq_tps(a.cod, b.cod);
			return (eq_tps(a.dom, b.dom) && eq_tps(a.cod, b.cod));
		} else {
			return true;
		}
	} else {
		return false;
	}
}

// simply typed terms
function trm_p(m) {
	return ((m.kind == vartrm) || (m.kind == consttrm) || (m.kind == apptrm) || (m.kind == lamtrm) || (m.kind == deftrm));
}

function olvar(name, tp) {
	this.kind = vartrm;
	this.name = name;
	this.tp = tp;
}

function lvar(name, tp) {
	return new olvar(name, tp);
}

function olconst(name, tp) {
	this.kind = consttrm;
	this.name = name;
	this.tp = tp;
}

function lconst(name, tp) {
	return new olconst(name, tp);
}

function oldef(name, trm) {
	this.kind = deftrm;
	this.name = name;
	this.trm = trm;
	this.tp = trm.tp;
}

function ldef(name, trm) {
	return new oldef(name, trm);
}

function leq(a) {
	return new lconst("*eq*", ar(a, ar(a, o)));
}

function lall(a) {
	return new lconst("*all*", ar(ar(a, o), o));
}

function lex(a) {
	return new lconst("*ex*", ar(ar(a, o), o));
}

function oapp(f, m) {
	this.kind = apptrm;
	this.func = f;
	this.arg = m;
	this.tp = (f.tp).cod;
}

function app(f, m) {
	if ((f.tp.kind == artp) && (eq_tps(f.tp.dom, m.tp))) {
		return new oapp(f, m);
	} else {
		throw ("Error - Ill-typed term - Cannot Apply " + trm_str(f) + " of type " + tp_str(f.tp) + " to " + trm_str(m) + " of type " + tp_str(m.tp));
	}
}

function trm_or_app(f, m) {
	if (m == null) {
		return f;
	} else {
		return app(f, m);
	}
}

function olam(x, a, m) {
	this.kind = lamtrm;
	this.varname = x;
	this.dom = a;
	this.body = m;
	this.tp = ar(a, m.tp);
}

function lam(x, a, m) {
	return new olam(x, a, m);
}

// 'options' these are not terms in the ordinary sense, but several terms encoded as one
// ma: array of terms, must be nonempty and each elt must be a term of the same tp
function ooption(i, ma) {
	this.kind = optiontrm;
	this.id = i;
	this.trmarray = ma;
	this.tp = ma[0].tp;
}

function or(p1, p2) {
	return app(app(lor, p1), p2);
}

function and(p1, p2) {
	return app(app(land, p1), p2);
}

function imp(p1, p2) {
	return app(app(limp, p1), p2);
}

function equiv(p1, p2) {
	return app(app(lequiv, p1), p2);
}

function not(p) {
	return app(lnot, p);
}

function eq(m, n) {
	return app(app(leq(m.tp), m), n);
}

function All(m) {
	return app(lall(m.tp.dom), m);
}

function all(x, a, m) {
	return app(lall(a), lam(x, a, m));
}

function Ex(m) {
	return app(lall(m.tp.dom), m);
}

function ex(x, a, m) {
	return app(lex(a), lam(x, a, m));
}

function or_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == apptrm) && (m.func.func.kind == consttrm) && (m.func.func.name == "*or*"));
}

function and_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == apptrm) && (m.func.func.kind == consttrm) && (m.func.func.name == "*and*"));
}

function imp_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == apptrm) && (m.func.func.kind == consttrm) && (m.func.func.name == "*imp*"));
}

function equiv_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == apptrm) && (m.func.func.kind == consttrm) && (m.func.func.name == "*equiv*"));
}

function not_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == consttrm) && (m.func.name == "*not*"));
}

function gen_not_body(m) {
	if (not_p(m)) {
		return m.arg;
	} else {
		return not(m);
	}
}

function eq_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == apptrm) && (m.func.func.kind == consttrm) && (m.func.func.name == "*eq*"));
}

function all_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == consttrm) && (m.func.name == "*all*") && (m.arg.kind == lamtrm));
}

var all_p_func = new Function("x", "return all_p(x);");

function ex_p(m) {
	return ((m.kind == apptrm) && (m.func.kind == consttrm) && (m.func.name == "*ex*") && (m.arg.kind == lamtrm));
}

var ex_p_func = new Function("x", "return ex_p(x);");

function lam_p(m) {
	return (m.kind == lamtrm);
}

var lam_p_func = new Function("x", "return lam_p(x);");

function ae_var(m) {
	return m.arg.varname;
}

var ae_var_func = new Function("x", "return ae_var(x);");

function ae_dom(m) {
	return m.arg.dom;
}

var ae_dom_func = new Function("x", "return ae_dom(x);");

function ae_body(m) {
	return m.arg.body;
}

var ae_body_func = new Function("x", "return ae_body(x);");

var lam_var_func = new Function("m", "return m.varname;");
var lam_dom_func = new Function("m", "return m.dom;");
var lam_body_func = new Function("m", "return m.body;");

function lft(m) {
	return m.func.arg;
}

function rght(m) {
	return m.arg;
}

function logconst_p(m) {
	return ((m.kind == consttrm) && ((m.name == "*not*") || (m.name == "*or*") || (m.name == "*and*") || (m.name == "*imp*") || (m.name == "*equiv*") || (m.name == "*eq*") || (m.name == "*all*") || (m.name == "*ex*")));
}

function basetype_q_p(m) {
	return ((m.kind == consttrm) && (m.name == "*eq*") && (m.tp.dom.kind == basetp));
}

function basetype_eq_p(m) {
	return (eq_p(m) && basetype_q_p(m.func.func));
}

// trm to string
function trm_str(m) {
	return trm_str_pr(m, -1, -1);
}

function prtighter(pr1, pr2) {
	return (pr1 > pr2);
}

function trm_str_pr(m, prl, prr) {
	if (m.kind == optiontrm) { // only happens when m is a term with options -- these will not parse, I'm really including this for debugging purposes
		var str = null;
		for (i in m.trmarray) {
			if (str == null) {
				str = '{';
			} else {
				str = str + ',';
			}
			str = str + trm_str(m.trmarray[i]);
		}
		return str + '}';
	} else if (not_p(m) && eq_p(m.arg)) { // treat -(x=y) in a special way to print as x != y
		var iop = infixopsprint['*neq*'];
		if (prtighter(iop.left, prl) && prtighter(iop.right, prr)) {
			var lft = trm_str_pr(m.arg.func.arg, prl, iop.left);
			var rght = trm_str_pr(m.arg.arg, iop.right, prr);
			return (lft + mathsym.neq + rght);
		} else {
			var lft = trm_str_pr(m.arg.func.arg, -1, iop.left);
			var rght = trm_str_pr(m.arg.arg, iop.right, -1);
			return ('(' + lft + mathsym.neq + rght + ')');
		}
	} else if ((m.kind == apptrm) && ((m.func.kind == consttrm) || (m.func.kind == deftrm)) && (prefixopsprint[m.func.name])) {
		var prefixop = prefixopsprint[m.func.name];
		if (prtighter(prefixop.pr, prr)) {
			return (prefixop.prsymb + trm_str_pr(m.arg, prefixop.pr, prr));
		} else {
			return ('(' + prefixop.prsymb + trm_str_pr(m.arg, prefixop.pr, -1) + ')');
		}
	} else if ((m.kind == apptrm) && (m.func.kind == apptrm) && ((m.func.func.kind == consttrm) || (m.func.func.kind == deftrm)) && (infixopsprint[m.func.func.name])) {
		var iop = infixopsprint[m.func.func.name];
		if (prtighter(iop.left, prl) && prtighter(iop.right, prr)) {
			var lft = trm_str_pr(m.func.arg, prl, iop.left);
			var rght = trm_str_pr(m.arg, iop.right, prr);
			return (lft + iop.prsymb + rght);
		} else {
			var lft = trm_str_pr(m.func.arg, -1, iop.left);
			var rght = trm_str_pr(m.arg, iop.right, -1);
			return ('(' + lft + iop.prsymb + rght + ')');
		}
	} else if (all_p(m)) {
		if (0 > prr) {
			return mathsym.all + trm_binder_str(all_p_func, ae_var_func, ae_dom_func, ae_body_func, m);
		} else {
			return '(' + mathsym.all + trm_binder_str(all_p_func, ae_var_func, ae_dom_func, ae_body_func, m) + ')';
		}
	} else if (ex_p(m)) {
		if (0 > prr) {
			return mathsym.ex + trm_binder_str(ex_p_func, ae_var_func, ae_dom_func, ae_body_func, m);
		} else {
			return '(' + mathsym.ex + trm_binder_str(ex_p_func, ae_var_func, ae_dom_func, ae_body_func, m) + ')';
		}
	} else if (m.kind == lamtrm) {
		if (0 > prr) {
			return mathsym.lambda + trm_binder_str(lam_p_func, lam_var_func, lam_dom_func, lam_body_func, m);
		} else {
			return '(' + mathsym.lambda + trm_binder_str(lam_p_func, lam_var_func, lam_dom_func, lam_body_func, m) + ')';
		}
	} else if (m.kind == vartrm) {
		return (m.name);
	} else if (m.kind == consttrm) {
		return (m.name);
	} else if (m.kind == deftrm) {
		return (m.name);
	} else if (m.kind == apptrm) {
		if (prtighter(apbinop.left, prl) && prtighter(apbinop.right, prr)) {
			var lft = trm_str_pr(m.func, prl, apbinop.left);
			var rght = trm_str_pr(m.arg, apbinop.right, prr);
			return (lft + ' ' + rght);
		} else {
			var lft = trm_str_pr(m.func, -1, apbinop.left);
			var rght = trm_str_pr(m.arg, apbinop.right, -1);
			return ('(' + lft + ' ' + rght + ')');
		}
	} else {
		throw ('not a trm');
	}
}

function trm_binder_str(p, v, d, b, m) {
	var x = v(m);
	var dom = d(m);
	var body = b(m);
	var r;
	r = (x + trm_binder_str_impl(p, v, d, b, body)); // Chad - May 27 2009 - Hacked this so it never shows types.  Did this because database presentations don't handle reserved variables with types given.  Commented out test below.
	//    if (varnames[x] && (varnames[x].kind == vartrm) && eq_tps(varnames[x].tp,dom)) { // then no need for explicit type
	//	r = (x + trm_binder_str_impl(p,v,d,b,body));
	//    } else { // else explicit type must be given
	//	r = (x + trm_binder_str_expl(p,v,d,b,body,dom));
	//    }
	return r;
}

function trm_binder_str_impl(p, v, d, b, m) {
	var str = '';
	var co = p(m);
	while (co) {
		var x = v(m);
		var dom = d(m);
		if (varnames[x] && eq_tps(varnames[x].tp, dom)) {
			str = str + ' ' + x;
			m = b(m);
			co = p(m);
		} else {
			co = false;
		}
	}
	str = str + '.' + trm_str(m);
	return str;
}

function trm_binder_str_expl(p, v, d, b, m, qdom) {
	var str = '';
	var co = p(m);
	while (co) {
		var x = v(m);
		var dom = d(m);
		if (eq_tps(dom, qdom)) {
			str = str + ' ' + x;
			m = b(m);
			co = p(m);
		} else {
			co = false;
		}
	}
	str = str + ':' + tp_str(qdom) + '.' + trm_str(m);
	return str;
}

// alpha assoc list:
function alpha_cons(a, b, ab) {
	this.a = a;
	this.b = b;
	this.rst = ab;
}

function aeq_varnames(x, y, ab) {
	if (ab == null) {
		return (x == y);
	} else if (ab.a == x) {
		return (ab.b == y);
	} else if (ab.b == y) {
		return false;
	} else {
		return aeq_varnames(x, y, ab.rst);
	}
}

function alpha_list_str(ab) {
	if (ab == null) {
		return "nil";
	} else if (ab.rst == null) {
		return "(" + ab.a + "." + ab.b + ")";
	} else {
		return "(" + ab.a + "." + ab.b + ") " + alpha_list_str(ab.rst);
	}
}

function aeq_trms(m, n, ab) {
	/*
    alert ("aeq_trms: m = " + m + " n = " + n);
    alert (" m.kind = " + m.kind + " n.kind = " + n.kind);
    alert (" m = " + trm_str(m));
    alert (" n = " + trm_str(n));
    alert (" ab = " + alpha_list_str(ab));
*/
	if (m.kind == n.kind) {
		if (m.kind == apptrm) {
			return (eq_tps(m.func.tp, n.func.tp) && aeq_trms(m.func, n.func, ab) && aeq_trms(m.arg, n.arg, ab));
		} else if (m.kind == lamtrm) {
			return (eq_tps(m.dom, n.dom) && aeq_trms(m.body, n.body, new alpha_cons(m.varname, n.varname, ab)));
		} else if ((m.kind == consttrm) || (m.kind == deftrm)) {
			return ((m.name == n.name) && eq_tps(m.tp, n.tp));
		} else if (m.kind == vartrm) {
			return (eq_tps(m.tp, n.tp) && aeq_varnames(m.name, n.name, ab));
		} else {
			return false;
		}
	} else {
		return false;
	}
}

function eq_trms(m, n) {
	/*
    alert ("eq_trms: m = " + m + " n = " + n);
    alert ("e m.kind = " + m.kind + " n.kind = " + n.kind);
    alert ("e m = " + trm_str(m));
    alert ("e n = " + trm_str(n));
*/
	return aeq_trms(m, n, null);
}

function not_free_in(x, trm) {
	if (trm.kind == lamtrm) {
		if (trm.varname == x) {
			return true;
		} else {
			return not_free_in(x, trm.body);
		}
	} else if (trm.kind == apptrm) {
		return (not_free_in(x, trm.func) && not_free_in(x, trm.arg));
	} else if (trm.kind == vartrm) {
		return (trm.name != x);
	} else {
		return true;
	}
}

function free_in(x, trm) {
	return (! (not_free_in(x, trm)));
}

// destructively adds frees of m to 'frees' object, except those in a
function unionFreesOf(frees, m, a) {
	if (m.kind == apptrm) {
		unionFreesOf(frees, m.func, a);
		unionFreesOf(frees, m.arg, a);
	} else if (m.kind == lamtrm) {
		var x = m.varname;
		var ax = a[x];
		a[x] = true;
		unionFreesOf(frees, m.body, a);
		a[x] = ax;
	} else if ((m.kind == vartrm) && (a[m.name] != true)) {
		frees[m.name] = m;
	}
}

// unused?
function subfrees(frees1, frees2) {
	try {
		for (x in frees1) {
			if (! (frees2[x])) {
				throw ("notsubfree");
			}
		}
		return true;
	}
	catch(err) {
		if (err == "notsubfree") {
			return false;
		} else {
			throw (err);
		}
	}
}

function legal_varname_p(z) {
	if (identifier_p(z)) {
		var zz = termnames[z];
		if (zz == null) {
			return true;
		} else if (zz.kind == vartrm) {
			return true;
		} else {
			return false; // no consts or defns
		}
	} else {
		return false; // no keywords
	}
}

function simul_subst_legal(y, z, m, theta) {
	if (m.kind == apptrm) {
		return (simul_subst_legal(y, z, m.func, theta) && simul_subst_legal(y, z, m.arg, theta));
	} else if (m.kind == lamtrm) {
		var u = m.varname;
		if (u == z) {
			return not_free_in(y, m);
		} else {
			var saveu = theta[u];
			theta[u] = null;
			var w = simul_subst_legal(y, z, m.body, theta);
			theta[u] = saveu;
			return w;
		}
	} else if (m.name == y) {
		return true;
	} else {
		var x = m.name;
		var v = theta[x];
		if (v == null) {
			return true;
		} else {
			return not_free_in(z, v);
		}
	}
}

function simul_subst_debug(m, theta) {
	botmsg('* simul_subst_debug m ' + trm_str(m));
	for (z in theta) {
		if (theta[z] != null) {
			botmsg('theta[' + z + '] = ' + trm_str(theta[z]));
		}
	}
}

// simul subst
function simul_subst(m, theta) {
	//    simul_subst_debug(m,theta); // uncomment this when debugging
	if (m.kind == apptrm) {
		var m1 = simul_subst(m.func, theta);
		var m2 = simul_subst(m.arg, theta);
		if ((m1 == m.func) && (m2 == m.arg)) {
			return m;
		} else {
			return app(m1, m2);
		}
	} else if (m.kind == lamtrm) {
		var y = m.varname;
		var tp = m.dom;
		var body = m.body;
		var z = y;
		if (simul_subst_legal(y, y, body, theta)) {
			var savey = theta[y];
			theta[y] = null;
			var body1 = simul_subst(body, theta);
			theta[y] = savey;
			if (body == body1) {
				return m;
			} else {
				return lam(y, tp, body1);
			}
		} else {
			var z = y + "'";
			var savey = theta[y];
			while (! (legal_varname_p(z)) || !(simul_subst_legal(y, z, body, theta))) {
				z = z + "'";
			}
			theta[y] = lvar(z, tp);
			var body1 = simul_subst(body, theta);
			theta[y] = savey;
			return lam(z, tp, body1);
		}
	} else {
		var x = m.name;
		var v = theta[x];
		if (v == null) {
			return m;
		} else {
			return v;
		}
	}
}

// substitute 1
function subst(m, x, n) {
	var theta = new Object();
	theta[x] = n;
	return simul_subst(m, theta);
}

// app_lam(\x.n,m) gives n[x:=m]
// app_lam(f,m) gives (f m) if f is not a lambda abstraction
function app_lam(f, m) {
	if (f.kind == lamtrm) {
		return subst(f.body, f.varname, m);
	} else {
		return app(f, m);
	}
}

// does not beta normalize completely.  Given M, it gives M' where M ->* M':
// M ->* M' and N ->* N' and M not an abstraction ==> (M N) ->* (M' N')
// M ->* (\x.M') and N ->* N' ==> (M N) ->* M'[x:=N']
// M ->* M' ==> (\x.M) ->* (\x.M')
// w ->* w where w is a name
function par_beta_reduce(m) {
	if (m.kind == apptrm) {
		var m1 = par_beta_reduce(m.func);
		var n1 = par_beta_reduce(m.arg);
		if (m1.kind == lamtrm) {
			return subst(m1.body, m1.varname, n1);
		} else if ((m1 == m.func) && (n1 == m.arg)) {
			return m;
		} else {
			return app(m1, n1);
		}
	} else if (m.kind == lamtrm) {
		var m1 = par_beta_reduce(m.body);
		if (m1 == m.body) {
			return m;
		} else {
			return lam(m.varname, m.dom, m1);
		}
	} else {
		return m;
	}
}

// beta normalize:
function beta_normalize(m) {
	var mprev = m;
	m = par_beta_reduce(m);
	while (m != mprev) {
		mprev = m;
		m = par_beta_reduce(m);
	}
	return m;
}

// checks if m is beta normal
function beta_normal_p(m) {
	if (m.kind == apptrm) {
		if (m.func.kind == lamtrm) {
			return false;
		} else {
			return (beta_normal_p(m.func) && beta_normal_p(m.arg));
		}
	} else if (m.kind == lamtrm) {
		return beta_normal_p(m.body);
	} else {
		return true;
	}
}

// checks if m is *not* beta normal
function not_beta_normal_p(m) {
	return (!beta_normal_p(m));
}

// throws 'false' unless m is of the form (f t1 ... tn) [applications] with ti's eta_long_normal
function eta_long_extr(m) {
	if (m.kind == apptrm) {
		eta_long_extr(m.func);
		eta_long_normal(m.arg);
	} else if (m.kind == lamtrm) {
		throw ('false');
	}
}

// throws 'false' if not eta long normal
function eta_long_normal(m) {
	if (m.tp.kind == artp) {
		if (m.kind == lamtrm) {
			eta_long_normal(m.body);
		} else {
			throw ('false');
		}
	} else {
		eta_long_extr(m);
	}
}

// returns true iff m is beta normal and eta long
function beta_eta_long_p(m) {
	try {
		eta_long_normal(m);
		return true;
	}
	catch(err) {
		if (err == 'false') {
			return false;
		} else {
			throw (err);
		}
	}
}

function beta_normal_but_not_eta_long_p(m) {
	return (beta_normal_p(m) && !beta_eta_long_p(m));
}

// for eta short, we make exceptions for the quantifiers ! and ? -- so that the printing remains nice.
// logically, this is difficult to justify, but technically we don't need the eta rule for completeness anyway.
function eta_short_form(m) {
	if ((m.kind == lamtrm) && (m.body.kind == apptrm) && (m.body.arg.kind == vartrm) && (m.body.arg.name == m.varname) && not_free_in(m.varname, m.body.func)) { // eta redex
		return eta_short_form(m.body.func);
	} else if (m.kind == apptrm) {
		if ((m.func.kind == consttrm) && ((m.func.name == '*all*') || (m.func.name == '*ex*')) && (m.arg.kind == lamtrm)) { // don't eta reduce these eta redexes
			var m1 = eta_short_form(m.arg.body);
			if (m1 == m.arg.body) {
				return m;
			} else {
				return app(m.func, lam(m.arg.varname, m.arg.dom, m1));
			}
		} else {
			var m1 = eta_short_form(m.func);
			var m2 = eta_short_form(m.arg);
			if ((m1 == m.func) && (m2 == m.arg)) {
				return m;
			} else {
				return app(m1, m2);
			}
		}
	} else if (m.kind == lamtrm) {
		var m1 = eta_short_form(m.body);
		if (m1 == m.body) {
			return m;
		} else {
			return lam(m.varname, m.dom, m1);
		}
	} else {
		return m;
	}
}

function eta_short_p(m) {
	if ((m.kind == lamtrm) && (m.body.kind == apptrm) && (m.body.arg.kind == vartrm) && (m.body.arg.name == m.varname) && not_free_in(m.varname, m.body.func)) { // eta redex
		return false;
	} else if (m.kind == apptrm) {
		if ((m.func.kind == consttrm) && ((m.func.name == '*all*') || (m.func.name == '*ex*')) && (m.arg.kind == lamtrm)) { // don't eta reduce these eta redexes
			return eta_short_p(m.arg.body);
		} else {
			return (eta_short_p(m.func) && eta_short_p(m.arg));
		}
	} else if (m.kind == lamtrm) {
		return eta_short_p(m.body);
	} else {
		return true;
	}
}

function beta_normal_but_not_eta_short_p(m) {
	return (beta_normal_p(m) && !eta_short_p(m));
}

function contains_a_defn_p(m) {
	if (m.kind == apptrm) {
		return (contains_a_defn_p(m.func) || contains_a_defn_p(m.arg));
	} else if (m.kind == lamtrm) {
		return contains_a_defn_p(m.body);
	} else if (m.kind == deftrm) {
		return true;
	} else {
		return false;
	}
}

// Parses Strings with a specification item, type or term.
// A token is a string of one of the following forms:
// sort
// const
// var
// type
// term
// axiom
// lemma
// claim
// ID ::= [a-zA-Z_][a-zA-Z0-9_']*
// 0
// 1
// (
// )
// |
// &
// ->
// <->
// ~
// !
// ?
// /
// .
// :
// =
function prefixop(symb, prsymb, name, f, pr) {
	this.symb = symb;
	this.prsymb = prsymb;
	this.name = name;
	this.func = f;
	this.pr = pr;
}

function binop(symb, prsymb, name, f, left, right) {
	this.symb = symb;
	this.prsymb = prsymb;
	this.name = name;
	this.func = f;
	this.left = left;
	this.right = right;
}

function declare_prefixop(symb, prsymb, name, f, pr) {
	var op = new prefixop(symb, prsymb, name, f, pr);
	prefixops[symb] = op;
	prefixopsprint[name] = op;
}

function declare_binop(symb, prsymb, name, f, left, right) {
	var bop = new binop(symb, prsymb, name, f, left, right);
	infixops[symb] = bop;
	infixopsprint[name] = bop;
}

var appfunc = new Function("m", "n", "return app(m,n);");
var apbinop = new binop('', ' ', '', appfunc, 5000, 5001); // special case - Mar 2008 changed priority to be very high
// Create an object for parsing a string
// Input: par : Object with property value of type string
// Output: parse object <| str: string, loc: int (between 0 and length(str) - 1), token : null or token, par : Object |>
// Note: In case of an error, we may want to change par.value to highlight the location of the error.
function parse(par) {
	this.str = par.value;
	this.par = par;
	this.loc = 0;
	this.token = null;
}

// lexer
// peek at character
// Input: a is a parse object
// Output: character of a.str at a.loc
function peek(a) {
	if (a.loc < a.str.length) {
		botmsg('peek = *' + a.str.charAt(a.loc) + '*'); // delete me, really
		return a.str.charAt(a.loc);
	} else {
		throw "Unexpected End";
	}
}

function eos_p(a) {
	return (a.loc >= a.str.length);
}

function pinc(a) {
	a.loc = a.loc + 1;
}

// next character
// Input: a is a parse object
// Output: character of a.str at a.loc+1 or throws "Unexpected End"
// Side Effect: a.loc is increased by 1
function next(a) {
	pinc(a);
	botmsg('next = *' + a.str.charAt(a.loc) + '*'); // delete me, really
	return peek(a);
}

function skipComment(a) {
	if (peek(a) == '%') {
		pinc(a);
		while (peek(a) != '\n') {
			pinc(a);
		}
	}
}

// skip white space
// Input: a is a parse object
// Output: None or throws "Unexpected End"
// Side Effect: a.loc is increased until it is the location of the first non-white space
function skipSpace(a) {
	skipComment(a);
	while ((peek(a) == ' ') || (peek(a) == '\n') || (peek(a) == '\r') || (peek(a) == '\t')) {
		pinc(a);
		skipComment(a);
	}
}

function alphacharp(c) {
	return ((c == 'A') || (c == 'B') || (c == 'C') || (c == 'D') || (c == 'E') || (c == 'F') || (c == 'G') || (c == 'H') || (c == 'I') || (c == 'J') || (c == 'K') || (c == 'L') || (c == 'M') || (c == 'N') || (c == 'O') || (c == 'P') || (c == 'Q') || (c == 'R') || (c == 'S') || (c == 'T') || (c == 'U') || (c == 'V') || (c == 'W') || (c == 'X') || (c == 'Y') || (c == 'Z') || (c == '_') || (c == 'a') || (c == 'b') || (c == 'c') || (c == 'd') || (c == 'e') || (c == 'f') || (c == 'g') || (c == 'h') || (c == 'i') || (c == 'j') || (c == 'k') || (c == 'l') || (c == 'm') || (c == 'n') || (c == 'o') || (c == 'p') || (c == 'q') || (c == 'r') || (c == 's') || (c == 't') || (c == 'u') || (c == 'v') || (c == 'w') || (c == 'x') || (c == 'y') || (c == 'z'));
}

function digitcharp(c) {
	return ((c == '0') || (c == '1') || (c == '2') || (c == '3') || (c == '4') || (c == '5') || (c == '6') || (c == '7') || (c == '8') || (c == '9'));
}

function anbegp(c) {
	return (alphacharp(c) || digitcharp(c) || (c == '_') || (c == "'"));
}

function anrstp(c) {
	return (alphacharp(c) || digitcharp(c) || (c == '_') || (c == "'"));
}

function symbegp(c) {
	return ((c == '*') || (c == '+') || (c == '/') || (c == '#') || (c == '@') || (c == '$') || (c == '^') || (c == '>') || (c == '<') || (c == '-') || (c == '|') || (c == '&') || (c == '=') || (c == '!') || (c == '?') || (c == '\\'));
}

function symrstp(c) {
	return ((c == '*') || (c == '+') || (c == '/') || (c == '#') || (c == '@') || (c == '$') || (c == '^') || (c == '>') || (c == '<') || (c == '-') || (c == '|') || (c == '&') || (c == '=') || (c == '!') || (c == '?') || (c == '\\') || (c == '~'));
}

function idpatternp(str) {
	var j = str.length;
	if (j > 0) {
		if (anbegp(str.charAt(0))) {
			var i = 1;
			var r = true;
			while (i < j) {
				if (! (anrstp(str.charAt(i)))) {
					r = false;
					i = j;
				}
				i = i + 1;
			}
			return r;
		} else {
			if (symbegp(str.charAt(0))) {
				var i = 1;
				var r = true;
				while (i < j) {
					if (! (symrstp(str.charAt(i)))) {
						r = false;
						i = j;
					}
					i = i + 1;
				}
				return r;
			} else {
				return false;
			}
		}
	} else {
		return false;
	}
}

// read_token
// Input: a is a parse object
// Output: a token or throws "Unexpected End" or "syntax error"
// Assumes: mathsym is a symbols object
// Side Effect: a.loc may be increased
function read_token(a) {
	if (a.token) { // already read
		var tok = a.token;
		a.token = null;
		botmsg('already read tok = *' + tok + '*'); // delete me, really
		return tok;
	} else {
		var tok, c;
		skipSpace(a);
		a.lastloc = a.loc; // in case we need to know where the last token read started
		c = peek(a);
		if (anbegp(c)) {
			tok = c;
			botmsg('begin an tok = *' + tok + '*'); // delete me, really
			try {
				c = next(a);
				while (anrstp(c)) {
					tok = tok + c;
					c = next(a);
				}
			}
			catch(err) {
				if (err != "Unexpected End") {
					throw (err);
				}
			}
		} else if (symbegp(c)) {
			tok = c;
			botmsg('begin sym tok = *' + tok + '*'); // delete me, really
			try {
				c = next(a);
				while (symrstp(c)) {
					tok = tok + c;
					c = next(a);
				}
				if (tok == '<->') {
					tok = mathsym.equiv;
				} else if (tok == '!=') {
					tok = mathsym.neq;
				} else if (tok == '!') {
					tok = mathsym.all;
				} else if (tok == '?') {
					tok = mathsym.ex;
				} else if (tok == '\\') {
					tok = mathsym.lambda;
				} else if (tok == '->') {
					tok = mathsym.implies;
				} else if (tok == '|') {
					tok = mathsym.or;
				} else if (tok == '&') {
					tok = mathsym.and;
				}
			}
			catch(err) {
				if (err != "Unexpected End") {
					throw (err);
				}
			}
		} else {
			botmsg('am I here? c = *' + c + '* symbegp = ' + symbegp(c)); // delete me, really
			switch (c) {
			case '(':
			case ')':
			case '.':
			case ':':
				pinc(a);
				tok = c;
				break;
			case '~':
			case mathsym.not:
				pinc(a);
				tok = mathsym.not;
				break;
			case mathsym.or:
				pinc(a);
				tok = mathsym.or;
				break;
			case mathsym.and:
				pinc(a);
				tok = mathsym.and;
				break;
			case mathsym.implies:
				pinc(a);
				tok = mathsym.implies;
				break;
			case mathsym.equiv:
				pinc(a);
				tok = mathsym.equiv;
				break;
			case mathsym.all:
				pinc(a);
				tok = mathsym.all;
				break;
			case mathsym.ex:
				pinc(a);
				tok = mathsym.ex;
				break;
			case mathsym.lambda:
				pinc(a);
				tok = mathsym.lambda;
				break;
			default:
				throw "syntax error";
			}
		}
		return tok;
	}
}

function read_number(a) {
	var tok = read_token(a);
	var l = tok.length;
	var n = 0;
	for (var i = 0; i < l; i = i + 1) {
		if (tok.charAt(i) == "0") {
			n = n * 10;
		} else if (tok.charAt(i) == "1") {
			n = n * 10 + 1;
		} else if (tok.charAt(i) == "2") {
			n = n * 10 + 2;
		} else if (tok.charAt(i) == "3") {
			n = n * 10 + 3;
		} else if (tok.charAt(i) == "4") {
			n = n * 10 + 4;
		} else if (tok.charAt(i) == "5") {
			n = n * 10 + 5;
		} else if (tok.charAt(i) == "6") {
			n = n * 10 + 6;
		} else if (tok.charAt(i) == "7") {
			n = n * 10 + 7;
		} else if (tok.charAt(i) == "8") {
			n = n * 10 + 8;
		} else if (tok.charAt(i) == "9") {
			n = n * 10 + 9;
		} else {
			throw ("Expected a number, but found " + tok);
		}
	}
	return n;
}

function read_expected(exp, a) {
	if (read_token(a) != exp) {
		throw ("syntax error -- expected " + exp);
	}
}

function keyword_p(tok) {
	return ((tok == 'sort') || (tok == 'const') || (tok == 'var') || (tok == 'reserve') || (tok == 'type') || (tok == 'term') || (tok == 'infix') || (tok == 'axiom') || (tok == 'lemma') || (tok == 'hyp') || (tok == 'claim')
	//            || (tok == 'import') || (tok == 'rename') || (tok == 'end') // Jan 2009 - Chad - no longer importing this way
	|| (tok == 'unknown') // Jan 2009 - allow unknowns in problem
	);
}

function identifier_p(tok) {
	return (idpatternp(tok) && !(keyword_p(tok)) && !(infixops[tok]));
}

// list must be nonempty
function read_id_list(a) {
	var tok = read_token(a);
	if (identifier_p(tok)) {
		var ar = new Array();
		ar[0] = tok;
		try {
			tok = read_token(a);
			while (identifier_p(tok)) {
				ar.push(tok);
				tok = read_token(a);
			}
			a.token = tok;
			return ar;
		}
		catch(err) {
			if (err == "Unexpected End") {
				return ar;
			} else {
				throw (err);
			}
		}
	} else if (keyword_p(tok)) {
		throw ("syntax error - expected identifier but found keyword " + tok);
	} else if (infixops[tok]) {
		throw ("syntax error - expected identifier but found infix operator " + tok);
	} else {
		throw ("syntax error - expected identifier but found " + tok);
	}
}

// nonempty, even list of id's
// return an associative array
function read_id_assoc(a, aa) {
	var tok = read_token(a);
	var snd = true;
	var tok1;
	if (identifier_p(tok)) {
		tok1 = tok;
		try {
			tok = read_token(a);
			while (identifier_p(tok)) {
				if (snd) {
					if (aa[tok1]) {
						throw ("Attempt to redeclare " + tok1 + " to map to " + tok + " is not allowed");
					} else {
						aa[tok1] = tok;
						snd = false;
					}
				} else {
					tok1 = tok;
					snd = true;
				}
				tok = read_token(a);
			}
			if (snd) {
				throw "syntax error - expected an even number of identifiers";
			} else {
				a.token = tok;
				return aa;
			}
		}
		catch(err) {
			if (err == "Unexpected End") {
				return ar;
			} else {
				throw (err);
			}
		}
	} else if (keyword_p(tok)) {
		throw ("syntax error - expected identifier but found keyword " + tok);
	} else if (infixops[tok]) {
		throw ("syntax error - expected identifier but found infix operator " + tok);
	} else {
		throw ("syntax error - expected identifier but found " + tok);
	}
}

function initialize1() {
	mathsym = new symbols();
	io = new ioobj();
}

function initialize() {
	knowncount = 1;
	claimscount = 1;
	typenames = new Object();
	termnames = new Object(); // signature (consts/defns) + ctx (vars)
	varnames = new Object(); // default types for some variable names
	infixops = new Object();
	infixopsprint = new Object();
	known = new Array();
	hyp = new Array();
	claims = new Array();
        typenames['set'] = base('set');
	termnames['False'] = lfalse;
	termnames['True'] = ltrue;
	prefixops = new Object();
	prefixopsprint = new Object();
	leoprefixopsprint = new Array();
	infixops = new Object();
	infixopsprint = new Object();
	leoinfixopsprint = new Array();
	declare_prefixop(mathsym.not, mathsym.not, '*not*', new Function("m", "n", "return not(n);"), 1500);
	leoprefixopsprint['*not*'] = '~';
	declare_binop(mathsym.and, mathsym.and, '*and*', new Function("m", "n", "return and(m,n);"), 1440, 1441);
	leoinfixopsprint['*and*'] = '&';
	declare_binop(mathsym.or, mathsym.or, '*or*', new Function("m", "n", "return or(m,n);"), 1430, 1431);
	leoinfixopsprint['*or*'] = '|';
	declare_binop(mathsym.implies, mathsym.implies, '*imp*', new Function("m", "n", "return imp(m,n);"), 1421, 1420);
	leoinfixopsprint['*imp*'] = '=>';
	declare_binop(mathsym.equiv, mathsym.equiv, '*equiv*', new Function("m", "n", "return equiv(m,n);"), 1390, 1390);
	leoinfixopsprint['*equiv*'] = '<=>';
	declare_binop('=', '=', '*eq*', new Function("m", "n", "return eq(m,n);"), 1996, 1996);
	leoinfixopsprint['*eq*'] = '=';
	declare_binop(mathsym.neq, '!=', '*neq*', new Function("m", "n", "return not(eq(m,n));"), 1996, 1996);
}

function topmsg(str) {
//	var txt = top.headerFrame.window.document.createTextNode(str);
//	io.outputtop.appendChild(txt);
}

function botmsg(str) {
//	var txt = top.footerFrame.window.document.createTextNode(str);
//	var elt = top.footerFrame.window.document.createElement('P');
//	elt.appendChild(txt);
//	io.outputbot.appendChild(elt);
}

function clearElt(e) {
	while (e.firstChild) {
		e.removeChild(e.firstChild);
	}
}

function cleartop() {
	clearElt(io.inputtop);
	clearElt(io.outputtop);
}

function clearbot() {
	clearElt(io.inputbot);
	clearElt(io.outputbot);
}

// for debugging
function print_globals() {
	clearbot();
	for (g in typenames) {
		var tpstr = tp_str(typenames[g]);
		if (tpstr == g) {
			botmsg('sort ' + g + '; ');
		} else {
			botmsg('type ' + g + ' = ' + tp_str(typenames[g]) + '; ');
		}
	}
	for (c in termnames) {
		if ((c != 'true') && (c != 'false') && (termnames[c] != null)) {
			if (termnames[c].kind == deftrm) {
				botmsg('defn ' + c + ':' + tp_str(termnames[c].tp) + ' = ' + trm_str(termnames[c].trm) + '; ');
			} else if (termnames[c].kind == consttrm) {
				botmsg('const ' + c + ':' + tp_str(termnames[c].tp) + '; ');
			} else {
				botmsg(' unexpected term ' + c + ':' + tp_str(termnames[c].tp) + '; ');
			}
		}
	}
	for (x in varnames) {
		botmsg('var ' + x + ':' + tp_str(varnames[x].tp) + '; ');
	}
	for (k in known) {
		if (known[k].id == null) {
			botmsg('known ' + trm_str(known[k].prop) + '; ');
		} else {
			botmsg('known ' + known[k].id + ':' + trm_str(known[k].prop) + '; ');
		}
	}
	for (k in claims) {
		if (claims[k].id == null) {
			botmsg('claim ' + trm_str(claims[k].prop) + '; ');
		} else {
			botmsg('claim ' + claims[k].id + ':' + trm_str(claims[k].prop) + '; ');
		}
	}
}

function init_spec(s) {
	var spec = top.mainFrame.window.document.getElementById('spec');
	spec.value = s;
	initialize1();
	for (i in init_spec_fns) {
		init_spec_fns[i]();
	}
}

function disallow(c) {
	if (c == "nnf") {
		nnfbutton = false;
	} else if (c == "leo") {
		useleo = false;
	} else if (c == "bext") {
		bext = false;
	} else if (c == "xiext") {
		xiext = false;
	} else if (c == "etaext") {
		etaext = false;
	} else if (c == "etanorm") {
		etanorm = false;
	} else if (c == "eagerdelete") {
		eagerdelete = false;
	} else { // else disallowing a logical constant
		if (disallowed == null) {
			disallowed = new Object();
		}
		disallowed[c] = true;
	}
}

function parse_spec(eltid) {
	var spec = top.mainFrame.window.document.getElementById(eltid);
	var a = new parse(spec);
	initialize();
	unknowns = new Array();
	try {
		var more = true;
		while (more) {
			more = read_spec_item(a);
		}
		for (u in unknowns) {
			if (unknowns[u]) {
				throw ("Unknown " + u + " must be defined before proving.");
				leftoverunknown = true;
			}
		}
	}
	catch(err) {
		alert(err);
		setSelRange(spec, a.lastloc, a.loc);
		return false;
	}
	return true;
}

function read_spec_item(a) {
	var tok;
	try {
		tok = read_token(a);
	}
	catch(err) {
		if (err == "Unexpected End") {
			return false;
		} else {
			throw (err);
		}
	}
	switch (tok) {
	case 'sort':
		var idarray = read_id_list(a);
		for (var i in idarray) {
			var s = idarray[i];
			if ((typenames[s]) || (s == 'prop')) {
				throw ("error -- " + s + " already a type name");
			} else {
				typenames[s] = base(s);
			}
		}
		break;
	case 'unknown':
		// Jan 2009 - Chad - allow unknowns, treated as constants except must be changed to term defs before proving
	case 'var':
		var idarray = read_id_list(a);
		read_expected(':', a);
		var tp = parse_tp(a);
		if (tp == null) {
			throw "syntax error -- missing type for const declaration";
		} else {
			for (var i in idarray) {
				var c = idarray[i];
				if (tok == 'unknown') {
					unknowns[c] = tp;
				} // Jan 2009 - Chad
				if (termnames[c]) {
					throw ("error -- " + c + " already a term name");
				} else if (varnames[c]) {
					throw ("error -- " + c + " already a var name");
				} else {
				    termnames[c] = lvar(c, tp);
				}
			}
		}
		break;
	case 'const':
		var idarray = read_id_list(a);
		read_expected(':', a);
		var tp = parse_tp(a);
		if (tp == null) {
			throw "syntax error -- missing type for const declaration";
		} else {
			for (var i in idarray) {
				var c = idarray[i];
				if (tok == 'unknown') {
					unknowns[c] = tp;
				} // Jan 2009 - Chad
				if (termnames[c]) {
					throw ("error -- " + c + " already a term name");
				} else if (varnames[c]) {
					throw ("error -- " + c + " already a var name");
				} else {
				    termnames[c] = lconst(c, tp);
				}
			}
		}
		break;
	case 'reserve':
		var idarray = read_id_list(a);
		read_expected(':', a);
		var tp = parse_tp(a);
		if (tp == null) {
			throw "syntax error -- missing type for reserve declaration";
		} else {
			for (var i in idarray) {
				var c = idarray[i];
				if (termnames[c]) {
					throw ("error -- " + c + " already a term name");
				} else {
					varnames[c] = lvar(c, tp);
				}
			}
		}
		break;
	case 'type':
		var id = read_token(a);
		if (identifier_p(id)) {
			if (typenames[id]) {
				throw ("error -- " + id + " already a type name");
			} else {
				read_expected('=', a);
				var tp = parse_tp(a);
				if (tp == null) {
					throw ("syntax error -- missing type defining " + id);
				} else {
					typenames[id] = tp; // type abbrevs are transparent
				}
			}
		} else {
			throw ("syntax error -- expected identifier, but found " + id);
		}
		break;
	case 'term':
		var id = read_token(a);
		if (identifier_p(id)) {
			if ((termnames[id]) && (!(unknowns[id]))) { // Jan 2009 - Chad - unknowns can be defined here
				throw ("error -- " + id + " already a term name");
			} else {
				read_expected('=', a);
				var trm = parse_trm(a);
				if (trm == null) {
					throw ("syntax error -- missing term defining " + id);
				} else {
					termnames[id] = ldef(id, trm);
					if (unknowns[id]) { // Jan 2009 - Chad
						if (eq_tps(unknowns[id], trm.tp)) {
							unknowns[id] = false;
						} else {
							throw ("definition of unknown " + id + " has the wrong type");
						}
					}
				}
			}
		} else {
			throw ("syntax error -- expected identifier, but found " + id);
		}
		break;
	case 'infix':
		var id = read_token(a);
		if (identifier_p(id)) {
			var trm = termnames[id];
			if (trm) {
				var tp = trm.tp;
				if ((tp.kind == artp) && (tp.cod.kind == artp)) {
					var lpr = read_number(a);
					var rpr = read_number(a);
					var f = new Function("x", "y", "return app(app(termnames['" + id + "'],x),y);");
                                        if (id == 'iIn') {
                                          declare_binop(id, mathsym.setmem , id, f, lpr, rpr);
					} else if (id == '<=') {
					  declare_binop(id, mathsym.leq, id, f, lpr, rpr);
                                        } else {
					  declare_binop(id, ' ' + id + ' ', id, f, lpr, rpr);
                                        }
				} else {
					throw ("Identifier " + id + " cannot be infix because it takes less than two arguments.");
				}
			} else {
				throw ("Unknown term identifier " + id);
			}
		} else {
			throw ("Expected identifier, found " + id);
		}
		break;
	case 'axiom':
	case 'hyp':
	case 'lemma':
		var tok2 = read_token(a);
		try {
			skipSpace(a);
			if ((! (eos_p(a))) && (peek(a) == ':')) {
				if (identifier_p(tok2)) {
					pinc(a);
					var trm = parse_trm(a);
					if (trm == null) {
						throw ("syntax error -- missing term giving " + tok);
					} else if (eq_tps(trm.tp, o)) {
					    if (tok == 'hyp') {
						hyp.push({
							prop: trm,
							id: tok2
						});
					    } else {
						known.push({
							prop: trm,
							id: tok2
						});
					    }
					} else {
						throw ("error -- term giving " + tok + " does not have type o");
					}
				} else {
					throw ("syntax error -- expected identifier, but found " + tok2);
				}
			} else {
				throw ("No Label");
			}
		}
		catch(err) {
			if ((err == "No Label") || (err == "Unexpected End")) {
				a.token = tok2;
				var trm = parse_trm(a);
				if (trm == null) {
					throw ("syntax error -- missing term giving " + tok);
				} else if (eq_tps(trm.tp, o)) {
					if (tok == 'hyp') {
						hyp.push({
							prop: trm,
							id: tok2
						});
					} else if (tok == 'axiom') {
						known.push({
							prop: trm,
							id: 'Axiom ' + knowncount
						}); // identify as 'axiom n' or 'lemma n'
					} else {
						known.push({
							prop: trm,
							id: 'Lemma ' + knowncount
						}); // identify as 'axiom n' or 'lemma n'
					}
					knowncount = knowncount + 1;
				} else {
					throw ("error -- term giving " + tok + " does not have type o");
				}
			} else {
				throw (err);
			}
		}
		break;
	case 'claim':
		var tok2 = read_token(a);
		try {
			skipSpace(a);
			if ((! (eos_p(a))) && (peek(a) == ':')) {
				if (identifier_p(tok2)) {
					pinc(a);
					var trm = parse_trm(a);
					if (trm == null) {
						throw ("syntax error -- missing term giving " + tok);
					} else if (eq_tps(trm.tp, o)) {
						claims.push({
							prop: trm,
							id: tok2
						});
					} else {
						throw ("error -- term giving " + tok + " does not have type o");
					}
				} else {
					throw ("syntax error -- expected identifier, but found " + tok2);
				}
			} else {
				throw ("No Label");
			}
		}
		catch(err) {
			if ((err == "No Label") || (err == "Unexpected End")) {
				a.token = tok2;
				var trm = parse_trm(a);
				if (trm == null) {
					throw ("syntax error -- missing term giving " + tok);
				} else if (eq_tps(trm.tp, o)) {
					claims.push({
						prop: trm,
						id: 'Claim ' + claimscount
					}); // identify as 'Claim n'
					claimscount = claimscount + 1;
				} else {
					throw ("error -- term giving " + tok + " does not have type o");
				}
			} else {
				throw (err);
			}
		}
		break;
	case 'import':
		var presid = read_token(a);
		if (identifier_p(presid)) {
			read_import_spec(a, new Array());
		} else {
			throw "identifier (name of a presentation) expected after import";
		}
	default:
		throw "syntax error - expected specification item but found " + tok;
	}
	return true; // read a spec item and there may be more
}

// Dec 2008 - Chad E Brown, to interface with the database Julian Backes is building as part of his Bachelor's.
// specification of morphism for import is list of
// rename <idlist> (even number of id's)  -- EG, rename a b c d will declare b and d and map a to b and c to d
// type <id> = <type> -- where the <type> must make sense in the codomain
// term <id> = <term> -- where the <term> must make sense in the codomain
// const <idlist> -- imports defns as consts (creating proof obligation)
// axiom <idlist> -- avoids 'claims' for proof obligations
// lemmas <idlist> -- ditto
// terminated by 'end'
// rho is associative array containing the morphism info
function read_import_spec(a, rho) {
	var tok, done;
	b = false;
	while (b) {
		tok = read_token(a);
		switch (tok) {
		case 'end':
			// do the import -- no it must be more elaborate than this.
			b = false;
			break;
		case 'rename':
			read_id_assoc(a, rho);
			break;
		case 'type':
			var id = read_token(a);
			if (identifier_p(id)) {
				read_expected('=', a);
				var tp = parse_tp(a);
				// ??? cannot parse the type unless we've already partially imported - rethink
			} else {
				throw ("syntax error - expected identifier but got " + id);
			}
			break;
		case 'term':
			var id = read_token(a);
			if (identifier_p(id)) {} else {
				throw ("syntax error - expected identifier but got " + id);
			}
			break;
		default:
			throw "syntax error in import specification (missing 'end'?)";
		}
	}
}

// a is an object with properties loc:int and str:string
function parse_tp(a) {
	try {
		var tok = read_token(a);
		if (tok == 'prop') {
			var cod = parse_tp(a);
			return tp_or_ar(o, cod);
		} else if (tok == '(') {
			var dom = parse_tp(a);
			read_expected(')', a);
			return tp_or_ar(dom, parse_tp(a));
		} else if (typenames[tok]) {
			var dom = typenames[tok];
			return tp_or_ar(dom, parse_tp(a));
		} else {
			a.token = tok; // save the token for later
			return null;
		}
	}
	catch(err) {
		if (err == "Unexpected End") {
			return null;
		} else {
			throw (err);
		}
	}
}

// a is a parse object
function parse_trm(a) {
	var t1 = parse_trm_1(a);
	if (t1 == null) {
		return null;
	} else if (typeof(t1) == "string") {
		if (prefixops[t1]) {
			var p = prefixops[t1];
			return parse_trm_i_1(p.func, null, a, p.pr);
		} else if (infixops[t1]) {
			throw ("syntax error -- leading infix operator " + t1);
		} else {
			t1 = termnames[t1];
			return parse_trm_2(t1, a);
		}
	} else {
		return parse_trm_2(t1, a);
	}
}

function parse_trm_1(a) {
	try {
		var tok = read_token(a);
		//	alert('parse_trm_1 tok = ' + tok); // debugging
		if (tok == '(') {
			var t = parse_trm(a);
			//	    if (t == null) { alert ('parsed null term in parens'); } else { alert('in parse_trm_1, just parsed ' + trm_str(t) + ' looking for right paren'); } // debugging
			read_expected(')', a);
			return t;
		} else if ((tok == mathsym.lambda) || (tok == mathsym.all) || (tok == mathsym.ex)) {
			return parse_binder(tok, a); // let binders always have lowest priority so that \x.x x is \x.(x x) instead of (\x.x) x [nonstandard?]
		} else if ((prefixops[tok]) || infixops[tok] || termnames[tok]) {
			return tok;
		} else if ((keyword_p(tok)) || !(identifier_p(tok))) {
			a.token = tok;
			return null;
		} else {
			throw ('Unknown term ' + tok);
		}
	}
	catch(err) {
		if (err == "Unexpected End") {
			return null;
		} else {
			throw (err);
		}
	}
}

function parse_binder(bndr, a) {
	var idarray = read_id_list(a);
	var unknownvar = null

	for (var i in idarray) {
		var x = idarray[i];
		var t = varnames[x];
		var t2 = termnames[x];
		if (t == null) {
			unknownvar = x;
		}
		if ((t2 != null) && (t2.kind != vartrm)) {
			throw ("error - " + x + " cannot be used as a variable");
		}
	}
	var tok = read_token(a);
	if (tok == ':') { // type explicitly given
		var tp = parse_tp(a);
		if (tp == null) {
			throw "syntax error -- missing type for binder";
		} else {
			var saved = new Object();
			var save = new Object();
			read_expected('.', a);
			for (var i in idarray) {
				var x = idarray[i];
				if (saved[x] == null) {
					saved[x] = true;
					save[x] = termnames[x];
				}
				termnames[x] = lvar(x, tp);
			}
			var body = parse_trm(a);
			for (var i = idarray.length - 1; i >= 0; i = i - 1) {
				var x = idarray[i];
				body = bind_real(bndr, x, tp, body);
			}
			for (var x in save) {
				termnames[x] = save[x];
			}
			return body;
		}
	} else if (unknownvar == null) { // no type given, all var names were previously declared
		var saved = new Object();
		var save = new Object();
		for (var i in idarray) {
			var x = idarray[i];
			var xv = varnames[x];
			if (saved[x] == null) {
				saved[x] = true;
				save[x] = termnames[x];
			}
			termnames[x] = xv;
		}
		var body = parse_trm(a);
		for (var i = idarray.length - 1; i >= 0; i = i - 1) {
			var x = idarray[i];
			var xv = varnames[x];
			body = bind_real(bndr, x, xv.tp, body);
			termnames[x] = save[x];
		}
		return body;
	} else {
		throw ("error - unknown variable name " + unknownvar);
	}
}

function bind_real(bndr, x, tp, body) {
	var trm = lam(x, tp, body);
	if ((bndr == mathsym.all) || (bndr == mathsym.ex)) {
		if (eq_tps(body.tp, o)) {
			if (bndr == mathsym.all) {
				trm = app(lall(tp), trm);
			} else {
				trm = app(lex(tp), trm);
			}
		} else {
			throw ("type error - body of quantified formula does not have type o");
		}
	}
	return trm;
}

function parse_trm_2(t1, a) {
	//    alert('parse_trm_2 after ' + trm_str(t1) + ':' + tp_str(t1.tp)); // debugging
	var t2 = parse_trm_1(a);
	if (t2 == null) {
		return t1;
	} else if (typeof(t2) == "string") {
		if (prefixops[t2]) {
			var p = prefixops[t2];
			var t3 = parse_trm_i_1(p.func, null, a, p.pr);
			return app(t1, t3);
		} else if (infixops[t2]) {
			var i = infixops[t2];
			return parse_trm_i_1(i.func, t1, a, i.right);
		} else {
			return parse_trm_i_2(appfunc, t1, termnames[t2], a, apbinop.right);
		}
	} else {
		return parse_trm_i_2(appfunc, t1, t2, a, apbinop.right);
	}
}

function parse_trm_i_1(f, t1, a, pr) {
	//    if (t1 == null) { alert('parse_trm_i_1 with null and pr=' + pr); } else { alert('parse_trm_i_1 after ' + trm_str(t1) + ':' + tp_str(t1.tp) + " and pr=" + pr); } // debugging
	var trmstack = new Array();
	var opstack = new Array();
	var oplftstack = new Array();
	var oprghtstack = new Array();
	trmstack[0] = t1;
	opstack[0] = f;
	oprghtstack[0] = pr;
	return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, 1, a);
}

function parse_trm_i_2(f, t1, t2, a, pr) {
	//    if (t1==null) { alert('parse_trm_i_2 after null and ' + trm_str(t2) + ':' + tp_str(t2.tp)); } else { alert('parse_trm_i_2 after ' + trm_str(t1) + ':' + tp_str(t1.tp) + ' and ' + trm_str(t2) + ':' + tp_str(t2.tp)); } // debugging
	var trmstack = new Array();
	var opstack = new Array();
	var oplftstack = new Array();
	var oprghtstack = new Array();
	trmstack[0] = t1;
	trmstack[1] = t2;
	opstack[0] = f;
	oprghtstack[0] = pr;
	return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, 1, a);
}

function parse_trm_i_r_debug(trmstack, opstack, oplftstack, oprghtstack, i, a) {
	var j = i;
	while (j >= 0) {
		if (trmstack[j] == null) {
			topmsg(" trmstack[" + j + "] = null");
		} else {
			topmsg(" trmstack[" + j + "] = " + trm_str(trmstack[j]));
		}
		topmsg(" oplftstack[" + j + "] = " + oplftstack[j]);
		topmsg(" oprghtstack[" + j + "] = " + oprghtstack[j]);
		j = j - 1;
	}
}

function parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, i, a) {
	var f;
	//    topmsg(" * 1 a.loc = " + a.loc + " i = " + i);
	//    parse_trm_i_r_debug(trmstack,opstack,oplftstack,oprghtstack,i,a); // debugging
	while ((i > 1) && (oplftstack[i - 1] != null) && (oprghtstack[i - 2] > oplftstack[i - 1])) {
		i = i - 1;
		f = opstack[i - 1];
		trmstack[i - 1] = f(trmstack[i - 1], trmstack[i]);
		trmstack[i] = trmstack[i + 1];
		trmstack[i + 1] = null;
		opstack[i - 1] = opstack[i];
		oplftstack[i - 1] = oplftstack[i];
		oprghtstack[i - 1] = oprghtstack[i];
	}
	//    topmsg(" * 2 i = " + i);
	//    parse_trm_i_r_debug(trmstack,opstack,oplftstack,oprghtstack,i,a); // debugging
	if ((i > 1) && (oplftstack[i - 1] != null) && (oprghtstack[i - 2] == oplftstack[i - 1])) {
		throw ("syntax error - ambiguous use of prefix or infix operator; more parentheses are needed");
	}
	var t2 = parse_trm_1(a);
	if (t2 == null) { // done, pop all and return result
		if (trmstack[i] == null) { // missing last part of infix chain
			throw "syntax error";
		} else {
			var f;
			t2 = trmstack[i];
			while (i > 0) {
				i = i - 1;
				f = opstack[i];
				t2 = f(trmstack[i], t2);
			}
			return t2;
		}
	} else if (typeof(t2) == "string") {
		if (prefixops[t2]) {
			if (trmstack[i] == null) {
				opstack[i] = prefixops[t2].func;
				oplftstack[i] = null;
				oprghtstack[i] = prefixops[t2].pr;
				return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, i + 1, a);
			} else {
				throw ('syntax error -- use of prefix operator in infix position');
			}
		} else if (infixops[t2]) {
			if (trmstack[i] == null) {
				throw ("syntax error -- leading infix operator " + t2);
			} else {
				opstack[i] = infixops[t2].func;
				oplftstack[i] = infixops[t2].left;
				oprghtstack[i] = infixops[t2].right;
				return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, i + 1, a);
			}
		} else {
			if (trmstack[i] == null) {
				trmstack[i] = termnames[t2];
				return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, i, a);
			} else {
				trmstack[i + 1] = termnames[t2];
				opstack[i] = appfunc;
				oplftstack[i] = apbinop.left;
				oprghtstack[i] = apbinop.right;
				return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, i + 1, a);
			}
		}
	} else {
		if (trmstack[i] == null) {
			trmstack[i] = t2;
			return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, i, a);
		} else {
			trmstack[i + 1] = t2;
			opstack[i] = appfunc;
			oplftstack[i] = apbinop.left;
			oprghtstack[i] = apbinop.right;
			return parse_trm_i_r(trmstack, opstack, oplftstack, oprghtstack, i + 1, a);
		}
	}
}

// trm with options to dom for selecting among options
function trmopt_sel(p, m) {
	trmopt_sel_pr(p, m, -1, -1);
}

function trmopt_sel_pr(p, m, prl, prr) {
	if (m.kind == optiontrm) {
		var sel = top.headerFrame.window.document.createElement('select');
		addMouseOverHandler(sel, function() {
			this.focus();
		});
		sel.setAttribute('id', 'select' + m.id);
		var ma = m.trmarray;
		for (i in ma) {
			var mtxt = top.headerFrame.window.document.createTextNode(trm_str(ma[i]));
			var mopt = top.headerFrame.window.document.createElement('option');
			mopt.appendChild(mtxt);
			sel.appendChild(mopt);
		}
		p.appendChild(sel);
		// I don't print _!=_ for ~(_=_) here, though I could.
	} else if ((m.kind == apptrm) && ((m.func.kind == consttrm) || (m.func.kind == deftrm)) && (prefixopsprint[m.func.name])) {
		var prefixop = prefixopsprint[m.func.name];
		if (prtighter(prefixop.pr, prr)) {
			p.appendChild(top.headerFrame.window.document.createTextNode(prefixop.prsymb));
			trmopt_sel_pr(p, m.arg, prefixop.pr, prr);
		} else {
			p.appendChild(top.headerFrame.window.document.createTextNode('('));
			p.appendChild(top.headerFrame.window.document.createTextNode(prefixop.prsymb));
			trmopt_sel_pr(p, m.arg, prefixop.pr, -1);
			p.appendChild(top.headerFrame.window.document.createTextNode(')'));
		}
	} else if ((m.kind == apptrm) && (m.func.kind == apptrm) && ((m.func.func.kind == consttrm) || (m.func.func.kind == deftrm)) && (infixopsprint[m.func.func.name])) {
		var iop = infixopsprint[m.func.func.name];
		if (prtighter(iop.left, prl) && prtighter(iop.right, prr)) {
			trmopt_sel_pr(p, m.func.arg, prl, iop.left);
			p.appendChild(top.headerFrame.window.document.createTextNode(iop.prsymb));
			trmopt_sel_pr(p, m.arg, iop.right, prr);
		} else {
			p.appendChild(top.headerFrame.window.document.createTextNode('('));
			trmopt_sel_pr(p, m.func.arg, -1, iop.left);
			p.appendChild(top.headerFrame.window.document.createTextNode(iop.prsymb));
			trmopt_sel_pr(p, m.arg, iop.right, -1);
			p.appendChild(top.headerFrame.window.document.createTextNode(')'));
		}
	} else if (all_p(m)) {
		if (0 > prr) {
			p.appendChild(top.headerFrame.window.document.createTextNode(mathsym.all));
			trmopt_binder_sel(p, all_p_func, ae_var_func, ae_dom_func, ae_body_func, m);
		} else {
			p.appendChild(top.headerFrame.window.document.createTextNode('(' + mathsym.all));
			trmopt_binder_sel(p, all_p_func, ae_var_func, ae_dom_func, ae_body_func, m);
			p.appendChild(top.headerFrame.window.document.createTextNode(')'));
		}
	} else if (ex_p(m)) {
		if (0 > prr) {
			p.appendChild(top.headerFrame.window.document.createTextNode(mathsym.ex));
			trmopt_binder_sel(p, ex_p_func, ae_var_func, ae_dom_func, ae_body_func, m);
		} else {
			p.appendChild(top.headerFrame.window.document.createTextNode('(' + mathsym.ex));
			trmopt_binder_sel(p, ex_p_func, ae_var_func, ae_dom_func, ae_body_func, m);
			p.appendChild(top.headerFrame.window.document.createTextNode(')'));
		}
	} else if (m.kind == lamtrm) {
		if (0 > prr) {
			p.appendChild(top.headerFrame.window.document.createTextNode(mathsym.lambda));
			trmopt_binder_sel(p, lam_p_func, lam_var_func, lam_dom_func, lam_body_func, m);
		} else {
			p.appendChild(top.headerFrame.window.document.createTextNode('(' + mathsym.lambda));
			trmopt_binder_sel(p, lam_p_func, lam_var_func, lam_dom_func, lam_body_func, m);
			p.appendChild(top.headerFrame.window.document.createTextNode(')'));
		}
	} else if (m.kind == vartrm) {
		p.appendChild(top.headerFrame.window.document.createTextNode(m.name));
	} else if (m.kind == consttrm) {
		p.appendChild(top.headerFrame.window.document.createTextNode(m.name));
	} else if (m.kind == deftrm) {
		p.appendChild(top.headerFrame.window.document.createTextNode(m.name));
	} else if (m.kind == apptrm) {
		if (prtighter(apbinop.left, prl) && prtighter(apbinop.right, prr)) {
			trmopt_sel_pr(p, m.func, prl, apbinop.left);
			p.appendChild(top.headerFrame.window.document.createTextNode(' '));
			trmopt_sel_pr(p, m.arg, apbinop.right, prr);
		} else {
			p.appendChild(top.headerFrame.window.document.createTextNode('('));
			trmopt_sel_pr(p, m.func, -1, apbinop.left);
			p.appendChild(top.headerFrame.window.document.createTextNode(' '));
			trmopt_sel_pr(p, m.arg, apbinop.right, -1);
			p.appendChild(top.headerFrame.window.document.createTextNode(')'));
		}
	} else {
		throw ('not a trm with options');
	}
}

function trmopt_binder_sel(p, pred, v, d, b, m) {
	var x = v(m);
	var dom = d(m);
	var body = b(m);
	if (varnames[x] && (varnames[x].kind == vartrm) && eq_tps(varnames[x].tp, dom)) { // then no need for explicit type
		p.appendChild(top.headerFrame.window.document.createTextNode(x));
		trmopt_binder_sel_impl(p, pred, v, d, b, body);
	} else { // else explicit type must be given
		p.appendChild(top.headerFrame.window.document.createTextNode(x));
		trmopt_binder_sel_expl(p, pred, v, d, b, body, dom);
	}
}

function trmopt_binder_sel_impl(p, pred, v, d, b, m) {
	var co = pred(m);
	while (co) {
		var x = v(m);
		var dom = d(m);
		if (varnames[x] && eq_tps(varnames[x].tp, dom)) {
			p.appendChild(top.headerFrame.window.document.createTextNode(' ' + x));
			m = b(m);
			co = pred(m);
		} else {
			co = false;
		}
	}
	p.appendChild(top.headerFrame.window.document.createTextNode('.'));
	trmopt_sel(p, m);
}

function trmopt_binder_sel_expl(p, pred, v, d, b, m, qdom) {
	var co = pred(m);
	while (co) {
		var x = v(m);
		var dom = d(m);
		if (eq_tps(dom, qdom)) {
			p.appendChild(top.headerFrame.window.document.createTextNode(' ' + x));
			m = b(m);
			co = pred(m);
		} else {
			co = false;
		}
	}
	p.appendChild(top.headerFrame.window.document.createTextNode(':' + tp_str(qdom) + '.'));
	trmopt_sel(p, m);
}

// for most problems, nothing is disallowed, so don't bother checking
function uses_disallowed(m) {
	if (disallowed == null) {
		return false;
	} else {
		return uses_disallowed_rec(m);
	}
}

function uses_disallowed_rec(m) {
	if (m.kind == lamtrm) {
		return uses_disallowed_rec(m.body);
	} else if (m.kind == apptrm) {
		return (uses_disallowed_rec(m.func) || uses_disallowed_rec(m.arg));
	} else if ((m.kind == consttrm) || (m.kind == deftrm)) {
		if (disallowed[m.name]) {
			return true;
		} else {
			return false;
		}
	} else {
		return false;
	}
}

var dbspecmode_elements = 0;

// switches to db specification mode
function dbspecmode() {
	var doc = top.mainFrame.window.document;
	var main_div = doc.getElementById('main');

	dbspecmode_clear_node(main_div);
	dbspecmode_add_spec(false);
}

// removes all content from a dom node
function dbspecmode_clear_node(node) {
	while (node.childNodes.length > 0) {
		node.removeChild(node.firstChild);
	}
}

// adds buttons: add specification text, import from database or prove everything
function dbspecmode_add_spec(add_prove_button) {
	dbspecmode_elements++;

	var doc = top.mainFrame.window.document;
	var main_div = doc.getElementById('main');

	var ndiv = doc.createElement('div');
	ndiv.setAttribute('id', 'spec_' + dbspecmode_elements);

	var nbutton;

	if (add_prove_button) {
		nbutton = doc.createElement('button');
		nbutton.setAttribute('type', 'button');
		nbutton.appendChild(doc.createTextNode('Prove'));
		nbutton.setAttribute('onclick', 'top.dbspecmode_prove(' + dbspecmode_elements + ');');
		ndiv.appendChild(nbutton);
	}

	nbutton = doc.createElement('button');
	nbutton.setAttribute('type', 'button');
	nbutton.appendChild(doc.createTextNode('Add Specification Window'));
	nbutton.setAttribute('onclick', 'top.dbspecmode_add_specification_window(' + dbspecmode_elements + ');');
	ndiv.appendChild(nbutton);

	nbutton = doc.createElement('button');
	nbutton.setAttribute('type', 'button');
	nbutton.appendChild(doc.createTextNode('Import From Database'));
	nbutton.setAttribute('onclick', 'top.dbspecmode_add_import(' + dbspecmode_elements + ');');
	ndiv.appendChild(nbutton);

	main_div.appendChild(ndiv);
}

function dbspecmode_add_specification_window(spec_id) {
	var doc = top.mainFrame.window.document;
	var spec_div = doc.getElementById('spec_' + spec_id);

	dbspecmode_clear_node(spec_div);

	var narea = doc.createElement('textarea');
	narea.setAttribute('cols', '50');
	narea.setAttribute('rows', '8');
	narea.id = 'spec_text_' + spec_id;

	spec_div.appendChild(narea);
	dbspecmode_add_spec(true);
}

function dbspecmode_add_import(spec_id) {
	var doc = top.mainFrame.window.document;
	var spec_div = doc.getElementById('spec_' + spec_id);

	dbspecmode_clear_node(spec_div);

	var nselect = doc.createElement('select');
	nselect.id = 'spec_pres_sel' + spec_id;
	nselect.disabled = true;

	var nbutton = doc.createElement('input');
	nbutton.id = 'spec_pres_button' + spec_id;
	nbutton.value = 'Get presentation';
	nbutton.type = 'button';
	nbutton.onclick = function() {
		nselect.disabled = true;
		nbutton.disabled = true;
	}

	nbutton.disabled = true;

	spec_div.appendChild(nselect);
	spec_div.appendChild(nbutton);

}

function dbspecmode_ajax_handle_get_presentation(results, spec_id) {
	var doc = top.mainFrame.window.document;
	var spec_div = doc.getElementById('spec_' + spec_id);

	dbspecmode_clear_node(spec_div);

	var narea = doc.createElement('textarea');
	narea.setAttribute('cols', '50');
	narea.setAttribute('rows', '8');
	//narea.value = results[0]['result'];
	narea.appendChild(doc.createTextNode(results[0]['result']));
	narea.id = 'spec_text_' + spec_id;

	spec_div.appendChild(narea);
	dbspecmode_add_spec(true);
}

function dbspecmode_ajax_handle_get_presentations(results, spec_id) {
	var doc = top.mainFrame.window.document;
	var spec_div = doc.getElementById('spec_' + spec_id);

	var select_elem = doc.getElementById('spec_pres_sel' + spec_id);
	var button_elem = doc.getElementById('spec_pres_button' + spec_id);

	for (var i = 0; i < results.length; i++) {
		var noption = doc.createElement('option');
		noption.text = results[i]['presentationName'];
		noption.value = results[i]['presentationID'];
		select_elem.options[select_elem.options.length] = noption;
	}

	select_elem.disabled = false;
	button_elem.disabled = false;
}

function dbspecmode_prove(spec_id) {
	var doc = top.mainFrame.window.document;

	initialize();
	unknowns = new Array();

	var a;
	var spec;

	try {
		for (var i = 1; i < dbspecmode_elements; i++) {
			spec = doc.getElementById('spec_text_' + i);

			if (spec == null) continue;

			a = new parse(spec);
			var more = true;
			while (more) {
				more = read_spec_item(a);
			}
		}

		for (u in unknowns) {
			if (unknowns[u]) {
				throw ("Unknown " + u + " must be defined before proving.");
				leftoverunknown = true;
			}
		}
	} catch(err) {
		alert(err);
		setSelRange(spec, a.lastloc, a.loc);
		return false;
	}

	top.prove();
}
