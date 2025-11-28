// File: prover.js
// Author: Chad E Brown
// Modified By: Matthias Hoeschele
var numsteps = 0 // undo subtracts from numsteps
var currclaim;

var pfstate;
var undostack; // undo array remembering proof state (subgoals,subgoal,...)
var pftreeops; // remember how to construct the proof tree at the end - for displaying
var currstep; // building up 'current step' Branch -ruleapp-> Branches to put on allsteps
var allsteps; // collection of all steps taken (even those that were undone)
var allstepssaved;
var bottomoptions;
var extrabottomoptions;
var extendinput;
var extendbutton;
var cutbutton;
var trustedbutton;
var untrustedbutton;
var knownbutton;
var preclaimbutton;
var preclaims;
var undobutton;
var redobutton;
var delaybutton;
var knownmenu;
var preclaimmenu;
var entertext;

var extraproofoptions = new Array();

var returnclaimbutton;
var returnspecbutton;

var repRuleData;

var selectbutton;
var selectdefbutton;
var optionnum;
var opttrm;

var forwardrules;

var claimmenu;

var specarray;

var hovering = false;
var timeevent;
var delaytime = 500;

var allow_simplify = true;
var allow_auto = true;
function allow_simplify_p() {
	return (allow_simplify);
}
function allow_auto_p() {
	return (allow_auto);
}

var proveInitFns = new Array();

// multiple UI support
function UI(init) {
	this.redraw = null;
	init(this);
}

var branchView = new UI(new Function("x", "x.redraw = function() {eraseBranch(); displayBranch();}"));

var structuredView = new UI(new Function("x", "x.redraw = function() {eraseBranch(); testdraw();}"));

var view = branchView;

function refreshUI() {
	view.redraw();
}

function prove() {
	try {
		if (claims.length == 0) {
			alert('No Claims Given.');
		} else {
			cleartop();
			clearbot();
			specarray = new Array();
			while (io.main.firstChild) {
				specarray.push(io.main.firstChild);
				io.main.removeChild(io.main.firstChild);
			}
			nitialize_rules();
			for (k in proveInitFns) {
				proveInitFns[k]();
			}
			knownmenu = top.headerFrame.window.document.createElement('div');
			for (i in known) {
				var p = top.headerFrame.window.document.createElement('p');
				var button = top.headerFrame.window.document.createElement('Input');
				button.type = "button";
				button.value = known[i].id;
				addClickHandler(button, importParticularClosure(i));
				knownmenu.appendChild(p);
				// add properties to button - make use of 'id' if known[i].id is not null -- otherwise what?
				p.appendChild(button);
				p.appendChild(top.headerFrame.window.document.createTextNode(' ' + trm_str(known[i].prop) + ' '));
			}
			claimmenu = top.mainFrame.window.document.createElement('div');
			claimmenu.appendChild(top.mainFrame.window.document.createTextNode('Choose a Claim to Prove:'));
			for (c in claims) {
				var m = mynot(claims[c].prop);
				var txt = top.mainFrame.window.document.createTextNode(' ' + trm_str(m) + ' ');
				var node = {
					prop: m,
					txt: txt,
					altscomputed: false,
					alts: null
				};
				var branchArray = new Array(node);
			        for (h in hyp) {
                                   var m = hyp[h].prop;
                                   var txt = top.mainFrame.window.document.createTextNode(' ' + trm_str(m) + ' ');
				   var node = {
					prop: m,
					txt: txt,
					altscomputed: false,
					alts: null
				   };
                                   branchArray.push(node);
                                }
				var cl = closedBranch_p(branchArray);
				var pre = true;
				currclaim = claims[c];
				preclaims = false;
				preclaimmenu = top.headerFrame.window.document.createElement('div');
				var branchctx = new Object();
				for (x in termnames) {
					branchctx[x] = termnames[x];
				}
				pfstate = new ProofState(new Array(branchArray), new Array(branchctx), new Array(cl), 0);
				undostack = new Array(pfstate, null);
				pftreeops = new Array(txt); // first on the pftreeops array is just the root node text
				allsteps = new Array();
				claims[c].pfstate = pfstate;
				claims[c].undostack = undostack;
				claims[c].pftreeops = pftreeops;
				for (i in claims) {
					if (pre) {
						if (c == i) {
							pre = false;
						} else {
							var p = top.headerFrame.window.document.createElement('p');
							var button = top.headerFrame.window.document.createElement('Input');
							button.type = "button";
							button.value = claims[i].id;
							addClickHandler(button, importClaimClosure(i));
							preclaimmenu.appendChild(p);
							// add properties to button - make use of 'id' if claims[i].id is not null -- otherwise what?
							p.appendChild(button);
							p.appendChild(top.headerFrame.window.document.createTextNode(' ' + trm_str(claims[i].prop) + ' '));
							preclaims = true;
						}
					}
				}
				claims[c].preclaimmenu = preclaimmenu;
				claims[c].preclaims = preclaims;
				var d = top.headerFrame.window.document.createElement('div');
				var button = top.headerFrame.window.document.createElement('Input');
				button.type = "button";
				button.value = claims[c].id;
				addClickHandler(button, proveClaimClosure(c));
				claimmenu.appendChild(d);
				d.appendChild(button);
				d.appendChild(top.mainFrame.window.document.createTextNode(' ' + trm_str(claims[c].prop) + ' '));
				claims[c].numsteps = 1;
				claims[c].div = d;
				claims[c].proven = false;
			}
			eraseBranch();
			if (claims.length > 1) {
				io.globaloptions.appendChild(returnspecbutton);
				displayClaimMenu();
			} else {
				nitialize_tableau(currclaim);
				refreshUI();
			}
		}
	}
	catch(err) {
		alert(err);
	}
}

function addClickHandler(e, f) {
	if (e.addEventListener) {
		e.addEventListener('click', function() {
			cltimeevent();
			f();
		},
		false);
	} else if (e.attachEvent) {
		e.attachEvent('onclick', function() {
			cltimeevent();
			f();
		});
	} else {
		throw ('Sorry, but the prover will not run correctly in this browser.  Bye.');
	}
	// Hovering over it for 'delaytime' ms is same as clicking
	addMouseOverHandlerDelay(e, f);
}

// no hovering at all
function addClickOnlyHandler(e, f) {
	if (e.addEventListener) {
		e.addEventListener('click', function() {
			cltimeevent();
			f();
		},
		false);
	} else if (e.attachEvent) {
		e.attachEvent('onclick', function() {
			cltimeevent();
			f();
		});
	} else {
		throw ('Sorry, but the prover will not run correctly in this browser.  Bye.');
	}
}

function hoveringswitch(b) {
	if (hovering) {
		hovering = false;
		b.value = "Turn Hovering On";
	} else {
		hovering = true;
		b.value = "Turn Hovering Off";
	}
}

function cltimeevent() {
	if (timeevent) {
		window.clearTimeout(timeevent);
		timeevent = null;
	}
}

function addMouseOverHandlerDelay(e, f) {
	addMouseOverHandler(e, function() {
		if (hovering) {
			if (timeevent) {
				cltimeevent();
			} else {
				timeevent = window.setTimeout(function() {
					f();
					cltimeevent();
				},
				delaytime);
			}
		}
	});
	addMouseOutHandler(e, function() {
		cltimeevent();
	});
}

function addMouseOverHandler(e, f) {
	if (e.addEventListener) {
		e.addEventListener('mouseover', f, false);
	} else if (e.attachEvent) {
		e.attachEvent('onmouseover', f);
	} else {
		throw ('Sorry, but the prover will not run correctly in this browser.  Bye.');
	}
}

function addMouseOutHandler(e, f) {
	if (e.addEventListener) {
		e.addEventListener('mouseout', f, false);
	} else if (e.attachEvent) {
		e.attachEvent('onmouseout', f);
	} else {
		throw ('Sorry, but the prover will not run correctly in this browser.  Bye.');
	}
}

function ProofState(subgoals, ctxs, closed, branch) { // create proof state object...
	this.subgoals = subgoals;
	this.ctxs = ctxs;
	this.closed = closed;
	this.branch = branch;

	function numopen() {
		var n = 0;
		for (i in pfstate.closed) {
			if (pfstate.closed[i] != true) {
				n = n + 1;
			}
		}
		return n;
	}
	this.numopen = numopen;
	function numtrusted() {
		var n = 0;
		for (i in pfstate.closed) {
			if (pfstate.closed[i] == 2) {
				n = n + 1;
			}
		}
		return n;
	}
	this.numtrusted = numtrusted;
	function numuntrusted() {
		var n = 0;
		for (i in pfstate.closed) {
			if (pfstate.closed[i] == false) {
				n = n + 1;
			}
		}
		return n;
	}
	this.numuntrusted = numuntrusted;
}

function addForwardRule(name, pred, block, fun, branchfun) {
	forwardrules.push({
		name: name,
		pred: new Function('p', 'return ' + pred + '(p);'),
		block: new Function('p', 'return ' + block + '(p);'),
		fun: new Function('i', 'return ' + fun + '(i);'),
		branchfun: branchfun
	});
}

function drawUndoClosure(f) {
	return function(i) {
		f(i);
		refreshUI();
	};
}

// Class for forward rules
function ForwardRule(name, pred, block, fun) {
	this.name = name;
	this.pred = new Function('p', 'return ' + pred + '(p);');
	this.block = new Function('p', 'return ' + block + '(p);');
	this.fun = new Function('i', 'return ' + fun + '(i);');
}

// making rules directly available without having to search by name in the forewardrule array
// would be nice to move this this to the main program
// Negation Normalize
var NNRl = new ForwardRule('Negation Normalize', 'NNFRule_p', 'NNFRule_block', 'NNFRule');

// DeMorgan Rules (Can use Negation Normalize instead of these)
var DeMorganOrRl = new ForwardRule('DeMorgan', 'DeMorgan_1_p', 'DeMorgan_1_block', 'DeMorgan_1');
var DeMorganAndRl = new ForwardRule('DeMorgan', 'DeMorgan_2_p', 'DeMorgan_2_block', 'DeMorgan_2');
var DeMorganAllRl = new ForwardRule('DeMorgan', 'DeMorgan_3_p', 'DeMorgan_3_block', 'DeMorgan_3');
var DeMorganExistsRl = new ForwardRule('DeMorgan', 'DeMorgan_4_p', 'DeMorgan_4_block', 'DeMorgan_4');

// Neg Or/And/Forall/Exists (instead of DeMorgan Rules) // - Chad - May 2009
var NegOrRl = new ForwardRule('NegOr', 'DeMorgan_1_p', 'NegOr_block', 'NegOrRule');
var NegAndRl = new ForwardRule('NegAnd', 'DeMorgan_2_p', 'NegAnd_block', 'NegAndRule');
var NegForallRl = new ForwardRule('NegForall', 'DeMorgan_3_p', 'NegForall_block', 'NegForallRule');
var NegForallStarRl = new ForwardRule('NegForall*', 'NegForallStarRule_p', 'NegForall_block', 'NegForallStarRule');
var NegExistsRl = new ForwardRule('NegExists', 'DeMorgan_4_p', 'nevertrue', 'NegExistsRule');

// Double Negation
var DNegRl = new ForwardRule('Remove Double Negation', 'DNegRule_p', 'DNegRule_block', 'DNegRule');

// Conjunction/Disjunction Rules
var AndRl = new ForwardRule('And', 'and_p', 'AndRule_block', 'AndRule');
var AndMRl = new ForwardRule('And*', 'AndMRule_p', 'AndMRule_block', 'AndMRule');
var OrRl = new ForwardRule('Or', 'or_p', 'OrRule_block', 'OrRule');
var OrMRl = new ForwardRule('Or*', 'OrMRule_p', 'OrMRule_block', 'OrMRule');

// Implication
var ImpRl = new ForwardRule('Implication', 'imp_p', 'ImpliesRule_block', 'ImpliesRule');
var NegImpRl = new ForwardRule('Negated Implication', 'neg_imp_p', 'NImpliesRule_block', 'NImpliesRule');

// Equivalence, Boolean Equality
var EquivRl = new ForwardRule('Equiv', 'equiv_p', 'EqBRule_block', 'EqBRule');
var NegEquivRl = new ForwardRule('Negated Equiv', 'neg_equiv_p', 'NEqBRule_block', 'NEqBRule');
var EqBRl = new ForwardRule('Boolean =', 'EqBRule_p', 'EqBRule_block', 'EqBRule');
var NEqBRl = new ForwardRule('Boolean !=', 'NEqBRule_p', 'NEqBRule_block', 'NEqBRule');

// Mating
//var MatingAutoRl = new ForwardRule('Mating','MatingRule_p','MatingRule_block','MatingRuleAuto');
//var ConfrontationAutoRl = new ForwardRule('Confrontation','ConfrontationRule_p','ConfrontationRule_block','ConfrontationRuleAuto');
var MatingAutoRl = new ForwardRule('Mating', 'MatingRule_p', 'nevertrue', 'MatingRuleAuto');
var ConfrontationAutoRl = new ForwardRule('Confrontation', 'ConfrontationRule_p', 'nevertrue', 'ConfrontationRuleAuto');

// Quantifiers
var ForallRl = new ForwardRule('Forall', 'ForallRule_p', 'nevertrue', 'ForallRule'); // never block instantiating a universal quantifier
var ExistsRl = new ForwardRule('Exists', 'ExistsRule_p', 'ExistsRule_block', 'ExistsRule');
var ExistsMRl = new ForwardRule('Exists*', 'ExistsStarRule_p', 'ExistsRule_block', 'ExistsStarRule');
var ExistsARl = new ForwardRule('Exists*', 'ExistsAutoRule_p', 'ExistsRule_block', 'ExistsAutoRule');

// Functional Equality
//    var NameRule = new ForwardRule('Functional =','EqFRule_p','EqFRule_block','EqFRule'); // version that creates forall
var EqFnRl = new ForwardRule('Functional =', 'EqFRule_p', 'nevertrue', 'EqFRuleArg'); // version that asks for instantiation for argument without going through a forall
var DisEqFnRl = new ForwardRule('Functional !=', 'NEqFRule_p', 'NEqFRule_block', 'NEqFRule');
var DisEqFnARl = new ForwardRule('Functional !=', 'NEqFRule_p', 'NEqFRule_block', 'NEqFAutoRule');
// same as func != rule, except only applies if both sides are lambda abstractions
var XiRl = new ForwardRule('Xi Rule', 'NEqXiRule_p', 'NEqFRule_block', 'NEqFRule');

// Beta Eta Delta
var BetaNormRl = new ForwardRule('Beta Normalize', 'not_beta_normal_p', 'BetaRule_block', 'BetaRule');
// don't use eta long form since it would require generating names for variables
var EtaExtRl = new ForwardRule('Eta Normalize', 'beta_normal_but_not_eta_short_p', 'EtaShortRule_block', 'EtaShortRule');
var ExpandDefRl = new ForwardRule('Expand Definitions', 'contains_a_defn_p', 'nevertrue', 'DeltaRule'); // use terms with options for this too
// Equality
var RepRl = new ForwardRule('Apply Eqn', 'RepRule_p', 'nevertrue', 'RepRule');

// Decomposition arity 1
var Dec1Rl = new ForwardRule('Decomposition', 'DecompositionRule1_p', 'DecompositionRule_block', 'DecompositionRule');

// Weakening
var WeakenRl = new ForwardRule('Delete', 'alwaystrue', 'nevertrue', 'weaken');

function nitialize_rules() {
	forwardrules = new Array();

	// Negation Normalize
	if (nnfbutton) {
		addForwardRule('Negation Normalize', 'NNFRule_p', 'NNFRule_block', 'NNFRule', drawUndoClosure(NNFRule));
	}

	// DeMorgan Rules (Can use Negation Normalize instead of these) // Commented - Chad - May 2009
	//  addForwardRule('DeMorgan', 'DeMorgan_1_p', 'DeMorgan_1_block', 'DeMorgan_1', drawUndoClosure(DeMorgan_1));
	//  addForwardRule('DeMorgan', 'DeMorgan_2_p', 'DeMorgan_2_block', 'DeMorgan_2', drawUndoClosure(DeMorgan_2));
	//  addForwardRule('DeMorgan', 'DeMorgan_3_p', 'DeMorgan_3_block', 'DeMorgan_3', drawUndoClosure(DeMorgan_3));
	//  addForwardRule('DeMorgan', 'DeMorgan_4_p', 'DeMorgan_4_block', 'DeMorgan_4', drawUndoClosure(DeMorgan_4));
	// Neg Or/And/Forall/Exists (instead of DeMorgan Rules) // - Chad - May 2009
	addForwardRule('NegOr', 'DeMorgan_1_p', 'NegOr_block', 'NegOrRule', drawUndoClosure(NegOrRule));
	addForwardRule('NegAnd', 'DeMorgan_2_p', 'NegAnd_block', 'NegAndRule', drawUndoClosure(NegAndRule));
	addForwardRule('NegForall', 'DeMorgan_3_p', 'NegForall_block', 'NegForallRule', NegForallRule);
	addForwardRule('NegForall*', 'NegForallStarRule_p', 'NegForall_block', 'NegForallStarRule', drawUndoClosure(NegForallStarRule));
	addForwardRule('NegExists', 'DeMorgan_4_p', 'nevertrue', 'NegExistsRule', NegExistsRule);

	// Double Negation
	addForwardRule('Remove Double Negation', 'DNegRule_p', 'DNegRule_block', 'DNegRule', drawUndoClosure(DNegRule));

	// Conjunction/Disjunction Rules
	addForwardRule('And', 'and_p', 'AndRule_block', 'AndRule', drawUndoClosure(AndRule));
	addForwardRule('And*', 'AndMRule_p', 'AndMRule_block', 'AndMRule', drawUndoClosure(AndMRule));
	addForwardRule('Or', 'or_p', 'OrRule_block', 'OrRule', drawUndoClosure(OrRule));
	addForwardRule('Or*', 'OrMRule_p', 'OrMRule_block', 'OrMRule', drawUndoClosure(OrMRule));

	// Implication
	addForwardRule('Implication', 'imp_p', 'ImpliesRule_block', 'ImpliesRule', drawUndoClosure(ImpliesRule));
	addForwardRule('Negated Implication', 'neg_imp_p', 'NImpliesRule_block', 'NImpliesRule', drawUndoClosure(NImpliesRule));

	// Equivalence, Boolean Equality // Equivalence Rules may be buggy -- final display was incorrect in some example. - Chad May 2009
	addForwardRule('Equiv', 'equiv_p', 'EqBRule_block', 'EqBRule', drawUndoClosure(EqBRule));
	addForwardRule('Negated Equiv', 'neg_equiv_p', 'NEqBRule_block', 'NEqBRule', drawUndoClosure(NEqBRule));
	addForwardRule('Boolean =', 'EqBRule_p', 'EqBRule_block', 'EqBRule', drawUndoClosure(EqBRule));
	if (bext) { // only if Boolean extensionality is allowed
		addForwardRule('Boolean !=', 'NEqBRule_p', 'NEqBRule_block', 'NEqBRule', drawUndoClosure(NEqBRule));
	}

	// Quantifiers
	addForwardRule('Forall', 'ForallRule_p', 'nevertrue', 'ForallRule', ForallRule); // never block instantiating a universal quantifier
	addForwardRule('Exists', 'ExistsRule_p', 'ExistsRule_block', 'ExistsRule', ExistsRule);
	addForwardRule('Exists*', 'ExistsStarRule_p', 'ExistsRule_block', 'ExistsStarRule', drawUndoClosure(ExistsStarRule));

	// Functional Equality
	//    addForwardRule('Functional =','EqFRule_p','EqFRule_block','EqFRule'); // version that creates forall
	addForwardRule('Functional =', 'EqFRule_p', 'nevertrue', 'EqFRuleArg', EqFRuleArg); // version that asks for instantiation for argument without going through a forall
	if (xiext) {
		if (etaext) { // only if both xi and eta are allowed:
			addForwardRule('Functional !=', 'NEqFRule_p', 'NEqFRule_block', 'NEqFRule', NEqFRule);
		} else { // same as func != rule, except only applies if both sides are lambda abstractions
			addForwardRule('Xi Rule', 'NEqXiRule_p', 'NEqFRule_block', 'NEqFRule', NEqFRule);
		}
	}

	// Mating
	addForwardRule('Mating', 'MatingRule_p', 'MatingRule_block', 'weaken', MatingRule_BranchView);
	addForwardRule('Confrontation', 'ConfrontationRule_p', 'ConfrontationRule_block', 'weaken', Confrontation_BranchView);
	addForwardRule('Mating', 'MatingRule_p', 'nevertrue', 'weaken', MatingRule_BranchView); // Mating temporarily disabled - Chad May 2009
	addForwardRule('Confrontation', 'ConfrontationRule_p', 'nevertrue', 'weaken', Confrontation_BranchView);

	// Decomposition - Matthias Hoeschele - added March 2009
	addForwardRule('Decomposition', 'DecompositionRule_p', 'DecompositionRule_block', 'weaken', drawUndoClosure(DecompositionRule));

	// Beta Eta Delta
	addForwardRule('Beta Normalize', 'not_beta_normal_p', 'BetaRule_block', 'BetaRule', drawUndoClosure(BetaRule));
	// don't use eta long form since it would require generating names for variables
	//  if ((etaext) && (etanorm)) { // temporarily turning off eta -- Chad, May 2009
	//      addForwardRule('Eta Normalize', 'beta_normal_but_not_eta_short_p', 'EtaShortRule_block', 'EtaShortRule', drawUndoClosure(EtaShortRule))
	//  }
	addForwardRule('Expand Definitions', 'contains_a_defn_p', 'nevertrue', 'DeltaRule', DeltaRule); // use terms with options for this too
	// Equality // Commented - Chad - May 2009 - should make this rule optional.
	addForwardRule('Apply Eqn', 'RepRule_p', 'nevertrue', 'RepRule', RepRule);
	// Weakening
	addForwardRule('Delete', 'alwaystrue', 'nevertrue', 'weaken', drawUndoClosure(weaken));

	entertext = top.headerFrame.window.document.createElement('Input');
	entertext.type = "text";
	entertext.value = "";
	addMouseOverHandler(entertext, function() {
		this.focus();
	});

	extendinput = top.mainFrame.window.document.createElement('Input');
	extendinput.type = "text";
	extendinput.value = "";
	addMouseOverHandler(extendinput, function() {
		this.focus();
	});
	extendbutton = top.mainFrame.window.document.createElement('Input');
	extendbutton.type = "button";
	extendbutton.value = "Extend";
	addClickHandler(extendbutton, function() {
		extend();
		refreshUI();
	});
	cutbutton = top.mainFrame.window.document.createElement('Input');
	cutbutton.type = "button";
	cutbutton.value = "Cut";
	addClickHandler(cutbutton, function() {
		cut();
		refreshUI();
	});
	bottomoptions = new Array(extendinput, extendbutton, cutbutton);
	extrabottomoptions = new Array();
	trustedbutton = top.headerFrame.window.document.createElement('Input');
	trustedbutton.type = "button";
	trustedbutton.value = "Mark Branch as Trusted";
	addClickOnlyHandler(trustedbutton, function() {
		trusted();
		refreshUI();
	});
	untrustedbutton = top.headerFrame.window.document.createElement('Input');
	untrustedbutton.type = "button";
	untrustedbutton.value = "Mark Branch as Untrusted";
	addClickOnlyHandler(untrustedbutton, function() {
		untrusted();
		refreshUI();
	});
	returnclaimbutton = top.headerFrame.window.document.createElement('Input');
	returnclaimbutton.type = "button";
	returnclaimbutton.value = "Return to Claim Menu";
	addClickOnlyHandler(returnclaimbutton, function() {
		returnToClaimMenu();
	});
	returnspecbutton = top.headerFrame.window.document.createElement('Input');
	returnspecbutton.type = "button";
	returnspecbutton.value = "Return to Initial Specification Window";
	addClickOnlyHandler(returnspecbutton, function() {
		returnToSpec();
	});
	knownbutton = top.headerFrame.window.document.createElement('Input');
	knownbutton.type = "button";
	knownbutton.value = "Import Axiom or Lemma";
	addClickHandler(knownbutton, function() {
		importKnown();
	});
	preclaimbutton = top.headerFrame.window.document.createElement('Input');
	preclaimbutton.type = "button";
	preclaimbutton.value = "Import Previous Claim";
	addClickHandler(preclaimbutton, function() {
		importPreClaim();
	});
	undobutton = top.headerFrame.window.document.createElement('Input');
	undobutton.type = "button";
	undobutton.value = "Undo";
	addClickHandler(undobutton, function() {
		undo();
		refreshUI();
	});
	redobutton = top.headerFrame.window.document.createElement('Input');
	redobutton.type = "button";
	redobutton.value = "Redo";
	addClickHandler(redobutton, function() {
		redo();
		refreshUI();
	});
	delaybutton = top.headerFrame.window.document.createElement('Input');
	delaybutton.type = "button";
	delaybutton.value = "Delay Branch";
	addClickHandler(delaybutton, function() {
		delay();
		refreshUI();
	});
	selectbutton = top.headerFrame.window.document.createElement('Input');
	selectbutton.type = "button";
	selectbutton.value = "Use This";
	addClickHandler(selectbutton, function() {
		RepRule3();
		refreshUI();
	});
	selectdefbutton = top.headerFrame.window.document.createElement('Input');
	selectdefbutton.type = "button";
	selectdefbutton.value = "Use This";
	addClickHandler(selectdefbutton, function() {
		DeltaRule2();
		refreshUI();
	});
}

// m is a claim, extended with partial proof info
function nitialize_tableau(m) {
	pfstate = m.pfstate;
	undostack = m.undostack;
	pftreeops = m.pftreeops;
	preclaims = m.preclaims;
	preclaimmenu = m.preclaimmenu;
	numsteps = m.numsteps;
	currclaim = m;
}

function alertClosedBranch() {
	if (pfstate.closed[pfstate.branch] == true) {
		alert('Good Job! You closed a branch!');
	}
}

// change to 'next' open branch
function delay() {
	var i = pfstate.branch + 1;
	var l = pfstate.subgoals.length;
	while ((i < l) && (pfstate.closed[i] == true)) {
		i = i + 1;
	}
	if (i == l) {
		i = 0;
		while ((i < l) && (pfstate.closed[i] == true)) {
			i = i + 1;
		}
		if (i == l) {
			i = null; // no open subgoals
		}
	}
	pfstate = new ProofState(pfstate.subgoals, pfstate.ctxs, pfstate.closed, i);
	pushUndo();
}

function delay2() {
	var i = pfstate.branch + 1;
	var l = pfstate.subgoals.length;
	if (i == l) {
		i = null;
	}
	pfstate = new ProofState(pfstate.subgoals, pfstate.ctxs, pfstate.closed, i);
	pushUndo();
}

function pushUndo() {
	undostack[numsteps] = pfstate;
	numsteps = numsteps + 1;
	undostack[numsteps] = null; // preventing discontinuous redos
}

function undo() {
	if (numsteps > 1) {
		numsteps = numsteps - 1;
		pfstate = undostack[numsteps - 1];
		if ((pfstate.branch == null) || (pfstate.closed[pfstate.branch] == true)) { // undo until open branch
			undo();
		}
	} else {
		alert('Cannot Undo');
	}
}

function redo() {
	if (undostack[numsteps]) {
		pfstate = undostack[numsteps];
		numsteps = numsteps + 1;
	} else {
		alert('Cannot Redo');
	}
}

function extend() {
	if (extendinput.value == "") {
		alert('No Term Given');
	} else {
		var a = new parse(extendinput);
		try {
			var trm = parse_trm(a);
			if (trm == null) {
				alert('Could not read term');
			} else if (trm.tp != o) {
				alert('Term does not have type B');
			} else if (easy_consequence_p(trm)) {
				currstep = {
					dom: branchPres(),
					rule: {
						name: "extend",
						trm: trm
					},
					codl: new Array()
				};
				extendBranchWithProp(trm);
				allsteps.push(currstep);
			} else {
				alert('Cannot determine if term follows from branch');
			}
		}
		catch(err) {
			alert(err);
		}
	}
}

// set trusted attribute of branch (e.g., after LEO says it's proved it)
function trusted() {
	pfstate.closed[pfstate.branch] = 2; // false for open, true for closed, 2 for trusted
	delay();
}
function untrusted() {
	pfstate.closed[pfstate.branch] = false;
}

// Chad - Feb 2009 - enough information to save the branch as a presentation (with no claims)
function branchPres1(c, b, cl) {
	return ({
		sig: c,
		knowns: b,
		closed: cl
	});
}

function branchPres() {
	return ({
		sig: pfstate.ctxs[pfstate.branch],
		knowns: pfstate.subgoals[pfstate.branch],
		closed: pfstate.closed[pfstate.branch]
	});
}

// extend branch with s | ~s
function cut() {
	if (extendinput.value == "") {
		alert('No Term Given');
	} else {
		var a = new parse(extendinput);
		try {
			var trm = parse_trm(a);
			if (trm == null) {
				alert('Could not read term');
			} else if (trm.tp != o) {
				alert('Term does not have type B');
			} else {
				currstep = {
					dom: branchPres(),
					rule: {
						name: "cut",
						trm: trm
					},
					codl: new Array()
				};
				generalExtendBranch(new Array(new Array(trm), new Array(not(trm))));
				allsteps.push(currstep);
			}
		}
		catch(err) {
			alert(err);
		}
	}
}

// delete me
function obj_debug(fstr, a) {
	for (x in a) {
		fstr = fstr + ' ' + x + '=' + a[x];
	}
	alert(fstr);
}

// delete me
function pfstateDebug() {
	clearbot();
	botmsg('numsteps = ' + numsteps);
	botmsg('pfstate.subgoals.length = ' + pfstate.subgoals.length);
	botmsg('pfstate.ctxs.length = ' + pfstate.ctxs.length);
	botmsg('pfstate.closed.length = ' + pfstate.closed.length);
	botmsg('pfstate.numopen() = ' + pfstate.numopen());
	botmsg('pfstate.numtrusted() = ' + pfstate.numtrusted());
	botmsg('pfstate.numuntrusted() = ' + pfstate.numuntrusted());
	botmsg('pfstate.branch = ' + pfstate.branch);
	for (i in pfstate.subgoals) {
		botmsg('Subgoal ' + i);
		if (pfstate.closed[i]) {
			botmsg('Closed');
		} else {
			botmsg('Open');
		}
		var a = pfstate.subgoals[i];
		for (j in a) {
			botmsg(j + ': ' + a[j].nodeValue);
		}
		var fstr = 'Frees:';
		for (x in pfstate.ctxs[i]) {
			fstr = fstr + ' ' + x;
			//      alert(x+' free on branch '+i); // delete me
		}
		botmsg(fstr);
	}
}

function eraseBranch() {
	clearElt(io.inputtop);
	clearElt(io.inputbot);
	clearElt(io.outputtop);
	clearElt(io.outputbot);
	clearElt(io.globaloptions);
	while (io.main.firstChild) {
		io.main.removeChild(io.main.firstChild);
	}
	for (x in pfstate.ctxs[pfstate.branch]) {
		termnames[x] = null;
	}
}

function displayProofTree() {
	var tab = top.mainFrame.window.document.createElement('table');
	var tb = top.mainFrame.window.document.createElement('tbody');
	var tr = top.mainFrame.window.document.createElement('tr');
	var td = top.mainFrame.window.document.createElement('td');
	var leaves = 1;
	var leaf_par_array = new Array(tb);
	var tr1, td1, c;
	io.main.appendChild(tab);
	tab.appendChild(tb);
	tb.appendChild(tr);
	tr.appendChild(td);
	td.appendChild(pftreeops[0]);
	tab.setAttribute('border', '0');
	tab.style.textAlign = 'center';
	//      tab.foo = 0; // delete me
	var i = 1;
	var j, k, n, a, b, blp, bk;
	while (i < numsteps) {
		var p = pftreeops[i];
		//    	botmsg('* step ' + i + ' out of ' + numsteps); // delete me
		if (p != null) {
			b = p.branch;
			blp = leaf_par_array[b];
			//      	    botmsg('working on branch ' + b + ' out of ' + leaves); // delete me
			//      	    botmsg('leaf_par_array '); j = 0; while (j < leaves) { if (leaf_par_array[j]) { botmsg(j + ': ' + leaf_par_array[j].foo); } else { botmsg(j + ': null'); } j++; } // delete me
			if (p.extend1 != null) { // just one proposition extending a branch
				//       		botmsg('extending with one'); // delete me
				tr = top.mainFrame.window.document.createElement('tr');
				td = top.mainFrame.window.document.createElement('td');
				td.appendChild(p.extend1);
				tr.appendChild(td);
				blp.appendChild(tr);
			} else { // general case with an array, several propositions, several new branches
				//        		botmsg('extending with many'); // delete me
				a = p.extendArray;
				n = a.length;
				if (n > 1) {
					j = leaves - 1;
					while (j > b) {
						leaf_par_array[j + n - 1] = leaf_par_array[j];
						j--;
					}
					//          		    botmsg('leaf_par_array after copy '); j = 0; while (j < leaves + n - 1) { if (leaf_par_array[j]) { botmsg(j + ': ' + leaf_par_array[j].foo); } else { botmsg(j + ': null'); } j++; } // delete me
					tr = top.mainFrame.window.document.createElement('tr');
					td = top.mainFrame.window.document.createElement('td');
					c = top.mainFrame.window.document.createElement('center');
					tab = top.mainFrame.window.document.createElement('table');
					tb = top.mainFrame.window.document.createElement('tbody');
					tab.setAttribute('border', '1');
					tab.style.textAlign = 'center';
					blp.appendChild(tr);
					tr.appendChild(td);
					td.appendChild(c);
					c.appendChild(tab);
					tr = top.mainFrame.window.document.createElement('tr');
					tab.appendChild(tb);
					tb.appendChild(tr);
					k = 0;
					while (k < n) {
						td = top.mainFrame.window.document.createElement('td');
						tr.appendChild(td);
						tab = top.mainFrame.window.document.createElement('table');
						tb = top.mainFrame.window.document.createElement('tbody');
						tab.setAttribute('border', '0');
						tab.style.textAlign = 'center';
						td.appendChild(tab);
						//            			tab.foo = i + ':' + k; // delete me
						bk = b + k;
						//            			botmsg('should be inserting at index ' + bk); // delete me
						leaf_par_array[bk] = tb;
						for (j in a[k]) {
							tr1 = top.mainFrame.window.document.createElement('tr');
							td1 = top.mainFrame.window.document.createElement('td');
							tab.appendChild(tb);
							tb.appendChild(tr1);
							tr1.appendChild(td1);
							td1.appendChild(a[k][j]);
						}
						k++;
					}
					//          		    botmsg('leaf_par_array after work '); j = 0; while (j < leaves + n - 1) { if (leaf_par_array[j]) { botmsg(j + ': ' + leaf_par_array[j].foo); } else { botmsg(j + ': null'); } j++; } // delete me
					leaves = leaves + n - 1;
				} else {
					// no new branches -- keep it simple
					for (j in a[0]) {
						tr = top.mainFrame.window.document.createElement('tr');
						td = top.mainFrame.window.document.createElement('td');
						td.appendChild(a[0][j]);
						tr.appendChild(td);
						blp.appendChild(tr);
					}
				}
			}
		}
		i++;
	}
}

function displayBranch() {
	if (pfstate.branch == null) { // proof finished
		var h = top.mainFrame.window.document.createElement('H2');
		var txt;
		io.main.appendChild(h);
		if (claims.length > 1) {
			io.globaloptions.appendChild(returnclaimbutton);
		}
		io.globaloptions.appendChild(returnspecbutton);
		if (! (currclaim.proven)) {
			txt = top.mainFrame.window.document.createTextNode(' -- Proven ');
			currclaim.div.appendChild(txt);
			currclaim.div.style.color = 'red';
			currclaim.proven = true;
		}
		if (numsteps == 1) {
			txt = top.mainFrame.window.document.createTextNode('Complete Proof! (Completed in ' + numsteps + ' step)');
		} else {
			txt = top.mainFrame.window.document.createTextNode('Complete Proof! (Completed in ' + numsteps + ' steps)');
		}
		h.appendChild(txt);
		h.style.color = 'red';
		// should display proof tree here
		displayProofTree();
		for (k in extraproofoptions) {
			extraproofoptions[k]();
		}
	} else {
		alertClosedBranch(); // an alternative where we alert that the branch is closed before showing it.  // user must explicitly click to go to next open branch
		var branchArray = pfstate.subgoals[pfstate.branch];
		//    	pfstateDebug(); // uncomment while debugging - pf state will be written in the footer frame
		for (x in pfstate.ctxs[pfstate.branch]) {
			termnames[x] = pfstate.ctxs[pfstate.branch][x];
		}
		var l = branchArray.length;
		var i = 0;
		var numopen = pfstate.numopen();
		var numtrusted = pfstate.numtrusted();
		if (pfstate.closed[pfstate.branch] == true) {
			if (numopen > 1) {
				delaybutton.value = "Work On Next Open Branch";
				io.globaloptions.appendChild(delaybutton);
				cleartop();
				if (numtrusted > 0) {
					topmsg('This branch is closed.  There are ' + numopen + ' open branches, ' + numtrusted + ' of which are trusted.');
				} else {
					topmsg('This branch is closed.  There are ' + numopen + ' open branches.');
				}
			} else if (numopen == 1) {
				delaybutton.value = "Work On Remaining Open Branch";
				io.globaloptions.appendChild(delaybutton);
				cleartop();
				topmsg('This branch is closed.  There is only 1 open branch.');
			} else {
				delaybutton.value = "Show Completed Proof";
				io.globaloptions.appendChild(delaybutton);
				cleartop();
				topmsg('The Proof Is Complete!');
			}
			if (claims.length > 1) {
				io.globaloptions.appendChild(returnclaimbutton);
			}
			io.globaloptions.appendChild(returnspecbutton);
			while (i < l) {
				var p = top.mainFrame.window.document.createElement('P');
				p.appendChild(branchArray[i].txt);
				io.main.appendChild(p);
				i++;
			}
		} else if (pfstate.closed[pfstate.branch] == 2) { // trusted
			io.globaloptions.appendChild(untrustedbutton);
			if (numopen > 1) {
				delaybutton.value = "Work On Next Open Branch";
				io.globaloptions.appendChild(delaybutton);
				cleartop();
				topmsg('This branch is trusted.  There are ' + numopen + ' open branches, ' + numtrusted + ' of which are trusted.');
			} else {
				cleartop();
				topmsg('This branch is trusted and is the only open branch.');
			}
			if (claims.length > 1) {
				io.globaloptions.appendChild(returnclaimbutton);
			}
			io.globaloptions.appendChild(returnspecbutton);
			while (i < l) {
				var p = top.mainFrame.window.document.createElement('P');
				p.appendChild(branchArray[i].txt);
				io.main.appendChild(p);
				i++;
			}
		} else {
			// add possibly 'delay branch', possibly 'undo'
			if (known.length > 0) {
				io.globaloptions.appendChild(knownbutton);
			}
			if (preclaims) {
				io.globaloptions.appendChild(preclaimbutton);
			}
			if (numsteps > 1) {
				io.globaloptions.appendChild(undobutton);
			}
			if (undostack[numsteps]) {
				io.globaloptions.appendChild(redobutton);
			}
			io.globaloptions.appendChild(trustedbutton);
			if (numopen > 1) {
				delaybutton.value = "Delay Branch";
				io.globaloptions.appendChild(delaybutton);
				cleartop();
				topmsg('There are ' + numopen + ' open branches.');
			} else {
				cleartop();
				topmsg('This is the only open branch.');
			}
			if (claims.length > 1) {
				io.globaloptions.appendChild(returnclaimbutton);
			}
			io.globaloptions.appendChild(returnspecbutton);
			// precompute rule related data
			precomputeRepRule();
			while (i < l) {
				var p = top.mainFrame.window.document.createElement('P');
				p.appendChild(branchArray[i].txt);
				// add buttons for rule application
				for (j in forwardrules) {
					if ((forwardrules[j].pred(branchArray[i].prop)) && (!(forwardrules[j].block(branchArray[i].prop)))) {
						var button = top.mainFrame.window.document.createElement('Input');
						button.type = "button";
						button.value = forwardrules[j].name;
						addClickHandler(button, forwardRuleClosure(forwardrules[j].branchfun, i));
						p.appendChild(button);
					}
				}
				io.main.appendChild(p);
				i = i + 1;
			}
			extendinput.value = "";
			for (k in bottomoptions) {
				io.main.appendChild(bottomoptions[k]);
			}
			for (k in extrabottomoptions) {
				io.main.appendChild(extrabottomoptions[k]);
			}
		}
	}
}

function returnToClaimMenu() {
	// reset properties of current claim from globals
	currclaim.pfstate = pfstate;
	currclaim.undostack = undostack;
	currclaim.pftreeops = pftreeops;
	currclaim.preclaims = preclaims;
	currclaim.preclaimmenu = preclaimmenu;
	currclaim.numsteps = numsteps;

	eraseBranch();
	io.globaloptions.appendChild(returnspecbutton);
	displayClaimMenu();
}

function returnToSpec() {
	while (io.maintop.firstChild) {
		io.maintop.removeChild(io.maintop.firstChild);
	}
	eraseBranch();
	for (i in specarray) {
		io.main.appendChild(specarray[i]);
	}
}

function displayClaimMenu() {
	io.maintop.appendChild(claimmenu);
}

function reddenNode(n) {
	var d = top.mainFrame.window.document.createElement('div');
	d.appendChild(top.mainFrame.window.document.createTextNode(n.txt.nodeValue));
	d.style.color = 'red';
	return {
		prop: n.prop,
		txt: d,
		altscomputed: n.altscomputed,
		alts: n.alts
	};
}

// closed if one of the following:
// false is on it
// ~true is on it
// ~[t = t] is on it
// ~[t <-> t] is on it
// ~A and A are on it
// ~(a = b) and (b = a) are on it
// ~(a <-> b) and (b <-> a) are on it
// Change relevant ones to red
function closedBranch_p(seq) {
	var l = seq.length
	var i = 0;
	var j = 0;
	var open = true;
	while ((i < l) && open) {
		var si = seq[i];
		var mi = si.prop;
		if ((mi.kind == consttrm) && (mi.name == 'False')) {
			seq[i] = reddenNode(si);
			open = false;
		} else if (not_p(mi)) {
			if ((mi.arg.kind == consttrm) && (mi.arg.name == 'True')) {
				seq[i] = reddenNode(si);
				open = false;
			} else if ((eq_p(mi.arg) || equiv_p(mi.arg)) && eq_trms(mi.arg.func.arg, mi.arg.arg)) {
				seq[i] = reddenNode(si);
				open = false;
			} else {
				var mia = mi.arg;
				var q = null;
				var ql = null;
				var qr = null;
				if (eq_p(mia) || equiv_p(mia)) {
					q = mia.func.func;
					ql = mia.func.arg;
					qr = mia.arg;
				}
				j = 0;
				while ((j < l) && open) {
					if (eq_trms(seq[j].prop, mia)) {
						var sj = seq[j];
						seq[i] = reddenNode(si);
						seq[j] = reddenNode(sj);
						open = false;
					} else if (q != null) {
						var mj = seq[j].prop;
						if ((mj.kind == apptrm) && (mj.func.kind == apptrm) && eq_trms(mj.func.func, q) && eq_trms(mj.func.arg, qr) && eq_trms(mj.arg, ql)) {
							var sj = seq[j];
							seq[i] = reddenNode(si);
							seq[j] = reddenNode(sj);
							open = false;
						}
					}
					j++;
				}
			}
		}
		i++;
	}
	return (!open);
}

// assume p is *1 = *2 or *1 <-> *2, check if q is symmetric version
var upToSymEqF = new Function('p', 'q', 'return ((q.kind == apptrm) && (q.func.kind == apptrm) && eq_trms(p.func.func,q.func.func) && eq_trms(p.func.arg,q.arg) && eq_trms(p.arg,q.func.arg));');

// p is an easy consequence of branch if
// p is an instance of reflexivity of = or <->
// p is an instance of excluded middle
// Commented this - Apr 2009: // p is of the form (?x:<tp> . true) -- nonemptiness of types
// p is beta equal to something on the branch, possibly up to expansion of one defn (don't expand more than one defn at a time)
// p is of the form q[a'] where q[b'] and !x1...xn.a=b are on the branch and there is some theta with theta(a) = a' and theta(b) = b' (no beta eta) [or symmetric version]
function easy_consequence_p(p) {
	if ((eq_p(p) || equiv_p(p)) && eq_trms(p.func.arg, p.arg)) {
		return true;
	} else if (or_p(p) && ((not_p(p.func.arg) && eq_trms(p.func.arg.arg, p.arg)) || (not_p(p.arg) && eq_trms(p.func.arg, p.arg.arg)))) {
		return true;
		//  } else if (ex_p(p) && (eq_trms(p.arg.body, ltrue))) { // types are nonempty // now handled by allowing a new name to be an instantiation of Forall or EqF
		//    return true;
	} else if ((eq_p(p) || equiv_p(p)) && findOnBranchF(upToSymEqF, p)) {
		return true;
	} else if (findOnBranch_up_to_beta_delta1(p)) {
		return true;
	} else if (findOnBranch_up_to_eqn(p)) {
		return true;
	} else { // do the rest
		return false;
	}
}

function importKnown() {
	io.globaloptions.removeChild(knownbutton);
	io.inputtop.appendChild(knownmenu);
}

function importParticular(i) {
	var m = known[i];
	if ((m == null) || (m.prop == null) || (m.prop.tp != o)) {
		alert('Sorry, but there was a problem importing this.');
	} else {
		//	currstep = { dom: branchPres(), rule: { name: "import", trm: m}, codl: new Array() };
		extendBranchWithProp(m.prop);
		//        allsteps.push(currstep);
	}
}

function importParticularClosure(i) {
	return function() {
		importParticular(i);
		refreshUI();
	};
}

function importPreClaim() {
	io.globaloptions.removeChild(preclaimbutton);
	io.inputtop.appendChild(preclaimmenu);
}

function importClaim(i) {
	var m = claims[i];
	if ((m == null) || (m.prop == null) || (m.prop.tp != o)) {
		alert('Sorry, but there was a problem importing this claim.');
	} else {
		//    currstep = { dom: branchPres(), rule: { name:"import", trm: m.prop}, codl: new Array() };
		extendBranchWithProp(m.prop);
		//        allsteps.push(currstep);
	}
}

function importClaimClosure(i) {
	return function() {
		importClaim(i);
		refreshUI();
	};
}

function proveClaim(i) {
	var m = claims[i];
	if ((m == null) || (m.prop == null) || (m.prop.tp != o)) {
		alert('Sorry, but there was a problem importing this claim.');
	} else {
		while (io.maintop.firstChild) {
			io.maintop.removeChild(io.maintop.firstChild);
		}
		nitialize_tableau(m);
		refreshUI();
	}
}

function proveClaimClosure(i) {
	return function() {
		proveClaim(i);
	};
}

// generalExtendBranch
// given an array of n arrays of props, replace current branch with n branches where the i'th new branch adds all the props on the i'th array
// IE [[a,b],[c,d]] replaces the branch with 2 new branches, one of which has a and b and the other of which has c and d
// not really completely general since we don't add eigenvariables...
function generalExtendBranch(a) {
	var a2 = new Array();
	var oldsubgoals = pfstate.subgoals;
	var oldctxs = pfstate.ctxs;
	var oldclosed = pfstate.closed;
	var l = oldsubgoals.length;
	var b = pfstate.branch
	var newsubgoals = new Array();
	var newctxs = new Array();
	var newclosed = new Array();
	var oldbr = oldsubgoals[b];
	var i = 0;
	var i2 = 0;
	while (i < l) {
		if (i == b) {
			for (k in a) {
				var newbr = new Array();
				var a3 = new Array();
				var ak = a[k];
				for (j in oldbr) {
					newbr[j] = oldbr[j];
				}
				for (r in ak) {
					var m = ak[r];
					var txt = top.mainFrame.window.document.createTextNode(' ' + trm_str(m) + ' ');
					var node = {
						prop: m,
						txt: txt,
						altscomputed: false,
						alts: null
					};
					newbr.push(node);
					a3.push(txt);
				}
				a2.push(a3);
				newsubgoals[i2] = newbr;
				newctxs[i2] = oldctxs[i];
				newclosed[i2] = closedBranch_p(newbr);
				currstep.codl.push(branchPres1(newctxs[i2], newbr, newclosed[i2]));
				i2 = i2 + 1;
			}
		} else {
			newsubgoals[i2] = oldsubgoals[i];
			newctxs[i2] = oldctxs[i];
			newclosed[i2] = oldclosed[i];
			i2 = i2 + 1;
		}
		i = i + 1;
	}
	pfstate = new ProofState(newsubgoals, newctxs, newclosed, b);
	pftreeops[numsteps] = {
		branch: b,
		extend1: null,
		extendArray: a2
	};
	pushUndo();
}

// extendBranchWithProp --
// simplified version of generalExtendBranch where the current branch is replaced with a new branch that has one extra prop
// no change in eigen vars
function extendBranchWithProp(m) {
	var oldsubgoals = pfstate.subgoals;
	var oldctxs = pfstate.ctxs;
	var oldclosed = pfstate.closed;
	var l = oldsubgoals.length;
	var b = pfstate.branch
	var newsubgoals = new Array();
	var newctxs = new Array();
	var newclosed = new Array();
	var oldbr = oldsubgoals[b];
	var i = 0;
	while (i < l) {
		if (i == b) {
			var newbr = new Array();
			for (j in oldbr) {
				newbr[j] = oldbr[j];
			}
			var txt = top.mainFrame.window.document.createTextNode(' ' + trm_str(m) + ' ');
			var node = {
				prop: m,
				txt: txt,
				altscomputed: false,
				alts: null
			};
			newbr.push(node);
			newsubgoals[i] = newbr;
			newctxs[i] = oldctxs[i];
			newclosed[i] = closedBranch_p(newbr);
			currstep.codl.push(branchPres1(newctxs[i], newbr, newclosed[i]));
			pftreeops[numsteps] = {
				branch: b,
				extend1: txt,
				extendArray: null
			};
		} else {
			newsubgoals[i] = oldsubgoals[i];
			newctxs[i] = oldctxs[i];
			newclosed[i] = oldclosed[i];
		}
		i = i + 1;
	}
	pfstate = new ProofState(newsubgoals, newctxs, newclosed, b);
	pushUndo();
}

// extendBranchWithEigenVarAndProp --
function extendBranchWithEigenVarAndProp(yname, y, m) {
	var oldsubgoals = pfstate.subgoals;
	var oldctxs = pfstate.ctxs;
	var oldclosed = pfstate.closed;
	var l = oldsubgoals.length;
	var b = pfstate.branch
	var newsubgoals = new Array();
	var newctxs = new Array();
	var newclosed = new Array();
	var oldbr = oldsubgoals[b];
	var i = 0;
	while (i < l) {
		if (i == b) {
			var newbr = new Array();
			for (j in oldbr) {
				newbr[j] = oldbr[j];
			}
			var txt = top.mainFrame.window.document.createTextNode(' ' + trm_str(m) + ' ');
			var node = {
				prop: m,
				txt: txt,
				altscomputed: false,
				alts: null
			};
			newbr.push(node);
			newsubgoals[i] = newbr;
			var ctx = new Object();
			for (x in oldctxs[i]) {
				ctx[x] = oldctxs[i][x];
			}
			ctx[yname] = y;
			newctxs[i] = ctx;
			newclosed[i] = closedBranch_p(newbr);
			currstep.codl.push(branchPres1(ctx, newbr, newclosed[i]));
			pftreeops[numsteps] = {
				branch: b,
				extend1: txt,
				extendArray: null
			};
		} else {
			newsubgoals[i] = oldsubgoals[i];
			newctxs[i] = oldctxs[i];
			newclosed[i] = oldclosed[i];
		}
		i = i + 1;
	}
	pfstate = new ProofState(newsubgoals, newctxs, newclosed, b);
	pushUndo();
}

// extendBranchWithEigenVarsAndProp -- used for Exists*
function extendBranchWithEigenVarsAndProp(names, m) {
	var oldsubgoals = pfstate.subgoals;
	var oldctxs = pfstate.ctxs;
	var oldclosed = pfstate.closed;
	var l = oldsubgoals.length;
	var b = pfstate.branch
	var newsubgoals = new Array();
	var newctxs = new Array();
	var newclosed = new Array();
	var oldbr = oldsubgoals[b];
	var i = 0;
	var y;
	while (i < l) {
		if (i == b) {
			var newbr = new Array();
			for (j in oldbr) {
				newbr[j] = oldbr[j];
			}
			var txt = top.mainFrame.window.document.createTextNode(' ' + trm_str(m) + ' ');
			var node = {
				prop: m,
				txt: txt,
				altscomputed: false,
				alts: null
			};
			newbr.push(node);
			newsubgoals[i] = newbr;
			var ctx = new Object();
			for (x in oldctxs[i]) {
				ctx[x] = oldctxs[i][x];
				//	alert('old name '+x);
			}
			for (yname in names) {
				ctx[yname] = names[yname];
				//	alert('new name '+yname);
			}
			//      for (x in ctx) {
			//	  alert('remember '+x);
			//      }
			newctxs[i] = ctx;
			newclosed[i] = closedBranch_p(newbr);
			currstep.codl.push(branchPres1(ctx, newbr, newclosed[i]));
			pftreeops[numsteps] = {
				branch: b,
				extend1: txt,
				extendArray: null
			};
		} else {
			newsubgoals[i] = oldsubgoals[i];
			newctxs[i] = oldctxs[i];
			newclosed[i] = oldclosed[i];
		}
		i = i + 1;
	}
	pfstate = new ProofState(newsubgoals, newctxs, newclosed, b);
	pfstateDebug();
	pushUndo();
}

// application predicate for weakening rule (can always weaken)
function alwaystrue(p) {
	return true;
}

// blocking predicate for weakening rule (weakening is never blocked)
function nevertrue(p) {
	return false;
}

// weaken: delete k'th from branch
function weaken(k) {
	var oldsubgoals = pfstate.subgoals;
	var oldctxs = pfstate.ctxs;
	var l = oldsubgoals.length;
	var b = pfstate.branch
	var newsubgoals = new Array();
	var newctxs = new Array();
	var oldbr = oldsubgoals[b];
	var i = 0;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "weaken",
			princ: k
		},
		codl: new Array()
	};
	while (i < l) {
		if (i == b) {
			var newbr = new Array();
			var newctx = new Object();
			var bvars = new Object();
			for (j in oldbr) {
				if (j != k) {
					newbr.push(oldbr[j]);
					unionFreesOf(newctx, oldbr[j].prop, bvars);
					//		    alert('just added ' + trm_str(oldbr[j].prop)); obj_debug('newctx:',newctx); obj_debug('bvars:',bvars); // delete me
				}
			}
			newsubgoals[i] = newbr;
			newctxs[i] = newctx;
			currstep.codl.push(branchPres1(newctx, newbr, pfstate.closed[i]));
			allsteps.push(currstep);
		} else {
			newsubgoals[i] = oldsubgoals[i];
			newctxs[i] = oldctxs[i];
		}
		i = i + 1;
	}
	pfstate = new ProofState(newsubgoals, newctxs, pfstate.closed, b);
	pftreeops[numsteps] = null; // no change to proof tree -- note that the eigenvariable condition may not be satisfied on final proof tree, but the proof will be legal in the sense that one can always weaken away any formula on a branch that would cause a conflict
	pushUndo();
}

function forwardRuleClosure(f, i) {
	return function() {
		f(i);
	}
}

// function applyForwardRule (j,i) {
//    alert('applyForwardRule(' + j + ',' + i + ')');
//    alert('forwardrules[' + j + '] = ' + forwardrules[j]);
//    alert('forwardrules[' + j + '].name = ' + forwardrules[j].name);
//    alert('forwardrules[' + j + '].fun = ' + forwardrules[j].fun);
//    forwardrules[j].fun(i);
// }
function findOnSeq(m, seq) {
	var i = 0;
	var l = seq.length;
	var found = false;
	while ((i < l) && (!found)) {
		if (eq_trms(seq[i].prop, m)) {
			found = true;
		}
		i++;
	}
	return found;
}

function findOnBranch(m) {
	return findOnSeq(m, pfstate.subgoals[pfstate.branch]);
}

function findNegOnSeq(m, seq) {
	var i = 0;
	var l = seq.length;
	var found = false;
	while ((i < l) && (!found)) {
		if ((not_p(seq[i].prop)) && (eq_trms(seq[i].prop.arg, m))) {
			found = true;
		}
		i++;
	}
	return found;
}

function findNegOnBranch(m) {
	return findNegOnSeq(m, pfstate.subgoals[pfstate.branch]);
}

function findOnSeqF(f, p, seq) {
	var i = 0;
	var l = seq.length;
	var found = false;
	while ((i < l) && (!found)) {
		if (f(p, seq[i].prop)) {
			found = true;
		}
		i++;
	}
	return found;
}

function findOnBranchF(f, p) {
	return findOnSeqF(f, p, pfstate.subgoals[pfstate.branch]);
}

// returns an array of 'alternative forms' of m including:
// beta normal form of m
// beta normal form of result of instantiating an occurrence of an abbrev in m
function beta_delta1_alts(m) {
	var ma = new Array();
	ma.push(beta_normalize(m));
	beta_delta1_alts_2(m, ma);
	//    botmsg('** alt forms of m: ' + trm_str(m)); // delete me
	//    for (i in ma) { // delete me
	//	botmsg(i + ': ' + trm_str(ma[i])); // delete me
	//    } // delete me
	return ma;
}

// delete me
function aeq_trms_debug(m, n, ab) {
	botmsg("aeq_trms: m = " + m + " n = " + n);
	botmsg(" m.kind = " + m.kind + " n.kind = " + n.kind);
	botmsg(" m = " + trm_str(m));
	botmsg(" n = " + trm_str(n));
	if (m.kind == n.kind) {
		if (m.kind == apptrm) {
			return (aeq_trms_debug(m.func, n.func, ab) && aeq_trms_debug(m.arg, n.arg, ab));
		} else if (m.kind == lamtrm) {
			return (eq_tps(m.dom, n.dom) && aeq_trms_debug(m.body, n.body, alpha_cons(m.varname, n.varname, ab)));
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

// delete me
function eq_trms_debug(m, n) {
	var ms = trm_str(m);
	var ns = trm_str(n);
	if ((ms == ns) && (!(eq_trms(m, n)))) {
		alert('somehow ' + ms + ' and ' + ns + ' are not equal')
		aeq_trms_debug(m, n, null);
	}
}

function beta_delta1_alts_2(m, ma) {
	//    botmsg('now m is ' + trm_str(m)); // delete me
	//    botmsg('ma is '); // delete me
	//    for (i in ma) { // delete me
	//	botmsg(i + ': ' + trm_str(ma[i])); // delete me
	//    } // delete me
	if (m.kind == apptrm) {
		var m1 = m.func;
		var m2 = m.arg;
		var i = ma.length;
		beta_delta1_alts_2(m1, ma);
		var l = ma.length;
		while (i < l) {
			ma[i] = beta_normalize(app(ma[i], m2));
			i++;
		}
		beta_delta1_alts_2(m2, ma);
		l = ma.length;
		while (i < l) {
			//	    botmsg('about to apply ' + trm_str(m1) + ' to ' + trm_str(ma[i])); // delete me
			ma[i] = beta_normalize(app(m1, ma[i]));
			//	    botmsg('ok'); // delete me
			i++;
		}
	} else if (m.kind == lamtrm) {
		var x = m.varname;
		var dom = m.dom;
		var m1 = m.body;
		var i = ma.length;
		beta_delta1_alts_2(m1, ma);
		var l = ma.length;
		while (i < l) {
			ma[i] = beta_normalize(lam(x, dom, ma[i]));
			i++;
		}
	} else if (m.kind == deftrm) {
		ma.push(m.trm);
	}
}

function univ_eqn_p(m) {
	while (all_p(m)) {
		m = m.arg.body;
	}
	return (eq_p(m));
}

function findOnBranch_up_to_eqn(m) {
	var seq = pfstate.subgoals[pfstate.branch];
	var i = 0;
	var ls = seq.length;
	var found = false;
	while ((i < ls) && (!found)) {
		if (univ_eqn_p(seq[i].prop)) {
			var evars = new Array();
			var frees = new Object();
			var bvars = new Object();
			var e = seq[i].prop;
			unionFreesOf(frees, e, bvars);
			while (all_p(e)) {
				evars.push({
					name: e.arg.varname,
					tp: e.arg.dom
				});
				e = e.arg.body;
			}
			var l = e.func.arg;
			var r = e.arg;
			if (eq_p(m) || equiv_p(m)) {
				found = aeq_up_to_eqn(evars, l, r, m.func.arg, m.arg, null, frees); // reflexivity of = or <-> up to eqn
			}
			if (!found) {
				found = findOnBranch_up_to_eqn_2(evars, l, r, m, frees);
			}
		}
		i++;
	}
	return found;
}

function findOnBranch_up_to_eqn_2(evars, l, r, m, frees) {
	var seq = pfstate.subgoals[pfstate.branch];
	var i = 0;
	var ls = seq.length;
	var found = false;
	while ((i < ls) && (!found)) {
		found = aeq_up_to_eqn(evars, l, r, m, seq[i].prop, null, frees);
		i++;
	}
	return found;
}

function aeq_up_to_eqn(evars, l, r, m, n, ab, frees) {
	var tpseq = eq_tps(l.tp, m.tp);
	if (tpseq && fo_matches(new Array({
		lft: l,
		rght: m,
		ab: null
	},
	{
		lft: r,
		rght: n,
		ab: null
	}), evars)) {
		return true;
	} else if (tpseq && fo_matches(new Array({
		lft: r,
		rght: m,
		ab: null
	},
	{
		lft: l,
		rght: n,
		ab: null
	}), evars)) {
		return true;
	} else if (m.kind == n.kind) {
		if (m.kind == apptrm) {
			return (eq_tps(m.func.tp, n.func.tp) && aeq_up_to_eqn(evars, l, r, m.func, n.func, ab, frees) && aeq_up_to_eqn(evars, l, r, m.arg, n.arg, ab, frees));
		} else if (m.kind == lamtrm) {
			if (frees[m.varname]) {
				return aeq_trms(m, n, ab);
			} else {
				return aeq_up_to_eqn(evars, l, r, m.body, n.body, alpha_cons(m.varname, n.varname, ab), frees);
			}
		} else {
			return aeq_trms(m, n, ab);
		}
	} else {
		return false;
	}
}

function findOnBranch_up_to_beta_delta1(m) {
	var ma = beta_delta1_alts(m);
	var seq = pfstate.subgoals[pfstate.branch];
	var i = 0;
	var j = 0;
	var k = 0;
	var l = seq.length;
	var lma = ma.length;
	var la = 0;
	var found = false;
	while ((i < l) && (!found)) {
		if (seq[i].altscomputed != true) {
			seq[i].alts = beta_delta1_alts(seq[i].prop); // only compute these once...
			seq[i].altscomputed = true;
		}
		j = 0
		la = seq[i].alts.length;
		while ((j < la) && (!found)) {
			k = 0
			while ((k < lma) && (!found)) {
				//		eq_trms_debug(ma[k],seq[i].alts[j]); // delete me
				if (eq_trms(ma[k], seq[i].alts[j])) {
					found = true;
				} else {
					k++;
				}
			}
			j++;
		}
		i++;
	}
	return found;
}

function NNF_p(p) {
	if (not_p(p)) {
		return (! (not_p(p.arg) || or_p(p.arg) || and_p(p.arg) || imp_p(p.arg) || ex_p(p.arg) || all_p(p.arg)));
	} else if (imp_p(p)) {
		return false;
	} else if (or_p(p) || and_p(p)) {
		return (NNF_p(p.func.arg) && NNF_p(p.arg));
	} else if (ex_p(p) || all_p(p)) {
		return (NNF_p(p.arg.body));
	} else {
		return true;
	}
}

function NNF(p) {
	if (not_p(p)) {
		return NNF_neg(p.arg);
	} else if (imp_p(p)) {
		return or(NNF_neg(p.func.arg), NNF(p.arg));
	} else if (or_p(p)) {
		var m1 = NNF(p.func.arg);
		var m2 = NNF(p.arg);
		if ((m1 == p.func.arg) && (m2 == p.arg)) {
			return p;
		} else {
			return or(m1, m2);
		}
	} else if (and_p(p)) {
		var m1 = NNF(p.func.arg);
		var m2 = NNF(p.arg);
		if ((m1 == p.func.arg) && (m2 == p.arg)) {
			return p;
		} else {
			return and(m1, m2);
		}
	} else if (ex_p(p)) {
		var m1 = NNF(p.arg.body);
		if (m1 == p.arg.body) {
			return p;
		} else {
			return ex(p.arg.varname, p.arg.dom, NNF(p.arg.body));
		}
	} else if (all_p(p)) {
		var m1 = NNF(p.arg.body);
		if (m1 == p.arg.body) {
			return p;
		} else {
			return all(p.arg.varname, p.arg.dom, NNF(p.arg.body));
		}
	} else {
		return p;
	}
}

function NNF_neg(p) {
	if (not_p(p)) {
		return NNF(p.arg);
	} else if (imp_p(p)) {
		return and(NNF(p.func.arg), NNF_neg(p.arg));
	} else if (or_p(p)) {
		return and(NNF_neg(p.func.arg), NNF_neg(p.arg));
	} else if (and_p(p)) {
		return or(NNF_neg(p.func.arg), NNF_neg(p.arg));
	} else if (ex_p(p)) {
		return all(p.arg.varname, p.arg.dom, NNF_neg(p.arg.body));
	} else if (all_p(p)) {
		return ex(p.arg.varname, p.arg.dom, NNF_neg(p.arg.body));
	} else {
		return not(p);
	}
}

// Check if q is NNF of p
function NNF_cmp(p, q) {
	if (not_p(p)) {
		return NNF_neg_cmp(p.arg, q);
	} else if (imp_p(p)) {
		if (or_p(q)) {
			return (NNF_neg_cmp(p.func.arg, q.func.arg) && NNF_cmp(p.arg, q.arg));
		} else {
			return false;
		}
	} else if (or_p(p)) {
		if (or_p(q)) {
			return (NNF_cmp(p.func.arg, q.func.arg) && NNF_cmp(p.arg, q.arg));
		} else {
			return false;
		}
	} else if (and_p(p)) {
		if (and_p(q)) {
			return (NNF_cmp(p.func.arg, q.func.arg) && NNF_cmp(p.arg, q.arg));
		} else {
			return false;
		}
	} else if (ex_p(p)) {
		if (ex_p(q) && (p.arg.varname == q.arg.varname) && (eq_tps(p.arg.dom, q.arg.dom))) { // don't check up to alpha here (though we soundly could)
			return NNF_cmp(p.arg.body, q.arg.body);
		} else {
			return false;
		}
	} else if (all_p(p)) {
		if (all_p(q) && (p.arg.varname == q.arg.varname) && (eq_tps(p.arg.dom, q.arg.dom))) { // don't check up to alpha here (though we soundly could)
			return NNF_cmp(p.arg.body, q.arg.body);
		} else {
			return false;
		}
	} else {
		return eq_trms(p, q);
	}
}

// Check if q is NNF of p
function NNF_neg_cmp(p, q) {
	if (not_p(p)) {
		return NNF_cmp(p.arg, q);
	} else if (imp_p(p)) {
		if (and_p(q)) {
			return (NNF_cmp(p.func.arg, q.func.arg) && NNF_neg_cmp(p.arg, q.arg));
		} else {
			return false;
		}
	} else if (or_p(p)) {
		if (and_p(q)) {
			return (NNF_neg_cmp(p.func.arg, q.func.arg) && NNF_neg_cmp(p.arg, q.arg));
		} else {
			return false;
		}
	} else if (and_p(p)) {
		if (or_p(q)) {
			return (NNF_neg_cmp(p.func.arg, q.func.arg) && NNF_neg_cmp(p.arg, q.arg));
		} else {
			return false;
		}
	} else if (ex_p(p)) {
		if (all_p(q) && (p.arg.varname == q.arg.varname) && (eq_tps(p.arg.dom, q.arg.dom))) { // don't check up to alpha here (though we soundly could)
			return NNF_neg_cmp(p.arg.body, q.arg.body);
		} else {
			return false;
		}
	} else if (all_p(p)) {
		if (ex_p(q) && (p.arg.varname == q.arg.varname) && (eq_tps(p.arg.dom, q.arg.dom))) { // don't check up to alpha here (though we soundly could)
			return NNF_neg_cmp(p.arg.body, q.arg.body);
		} else {
			return false;
		}
	} else if (not_p(q)) {
		return eq_trms(p, q.arg);
	} else {
		return false;
	}
}

// check if p is in NNF (only at 'top level')
function NNFRule_p(p) {
	return ! NNF_p(p);
}

var NNFRule_block_f = new Function('p', 'q', 'return NNF_neg_cmp(p,q);');

function NNFRule_block(p) {
	return findOnBranchF(NNFRule_block_f, p.arg);
}

function NNFRule(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "nnf",
			princ: i
		},
		codl: new Array()
	};
	extendBranchWithProp(NNF(p));
	allsteps.push(currstep);
	eagerdelete_weaken(i, currstep.codl); // Chad - Mar 2009
}

// check if p is of the form ~(p1 | p2)
function DeMorgan_1_p(p) {
	return (not_p(p) && or_p(p.arg));
}

// assume p is of the form ~(p1 | p2) -- check if q is of the form (~p1 & ~p2)
var DeMorgan_1_block_f = new Function('p', 'q', 'return (and_p(q) && not_p(q.arg) && not_p(q.func.arg) && eq_trms(p.arg.func.arg,q.func.arg.arg) && eq_trms(p.arg.arg,q.arg.arg));');

function DeMorgan_1_block(p) {
	return findOnBranchF(DeMorgan_1_block_f, p);
}

// assume i'th prop on current branch is of the form ~(p1 | p2), extend with (~p1 & ~p2)
function DeMorgan_1(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "demorgan1",
			princ: i
		},
		codl: new Array()
	};
	extendBranchWithProp(and(not(p.arg.func.arg), not(p.arg.arg)));
	allsteps.push(currstep);
	eagerdelete_weaken(i, currstep.codl); // Chad - Mar 2009
}

// check if p is of the form ~(p1 & p2)
function DeMorgan_2_p(p) {
	return (not_p(p) && and_p(p.arg));
}

// assume p is of the form ~(p1 & p2) -- check if q is of the form (~p1 | ~p2)
var DeMorgan_2_block_f = new Function('p', 'q', 'return (or_p(q) && not_p(q.arg) && not_p(q.func.arg) && eq_trms(p.arg.func.arg,q.func.arg.arg) && eq_trms(p.arg.arg,q.arg.arg));');

function DeMorgan_2_block(p) {
	return findOnBranchF(DeMorgan_2_block_f, p);
}

// assume i'th prop on current branch is of the form ~(p1 & p2), extend with (~p1 | ~p2)
function DeMorgan_2(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "demorgan2",
			princ: i
		},
		codl: new Array()
	};
	extendBranchWithProp(or(not(p.arg.func.arg), not(p.arg.arg)));
	allsteps.push(currstep);
	eagerdelete_weaken(i, currstep.codl); // Chad - Mar 2009
}

// check if p is of the form ~(!x.p1)
function DeMorgan_3_p(p) {
	return (not_p(p) && all_p(p.arg));
}

// assume p is of the form ~(!x.p1) -- check if q is of the form (?x.~p1)
var DeMorgan_3_block_f = new Function('p', 'q', 'return (ex_p(q) && not_p(q.arg.body) && aeq_trms(p.arg.arg.body,q.arg.body.arg,alpha_cons(p.arg.arg.varname,q.arg.varname,null)));');

function DeMorgan_3_block(p) {
	return findOnBranchF(DeMorgan_3_block_f, p);
}

// assume i'th prop on current branch is of the form ~(!x.p1), extend with (?x.~p1)
function DeMorgan_3(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "demorgan3",
			princ: i
		},
		codl: new Array()
	};
	extendBranchWithProp(ex(p.arg.arg.varname, p.arg.arg.tp.dom, not(p.arg.arg.body)));
	allsteps.push(currstep);
	eagerdelete_weaken(i, currstep.codl); // Chad - Mar 2009
}

// check if p is of the form ~(?x.p1)
function DeMorgan_4_p(p) {
	return (not_p(p) && ex_p(p.arg));
}

// assume p is of the form ~(?x.p1) -- check if q is of the form (!x.~p1)
var DeMorgan_4_block_f = new Function('p', 'q', 'return (all_p(q) && not_p(q.arg.body) && aeq_trms(p.arg.arg.body,q.arg.body.arg,alpha_cons(p.arg.arg.varname,q.arg.varname,null)));');

function DeMorgan_4_block(p) {
	return findOnBranchF(DeMorgan_4_block_f, p);
}

// assume i'th prop on current branch is of the form ~(?x.p1), extend with (!x.~p1)
function DeMorgan_4(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "demorgan4",
			princ: i
		},
		codl: new Array()
	};
	extendBranchWithProp(all(p.arg.arg.varname, p.arg.arg.tp.dom, not(p.arg.arg.body)));
	allsteps.push(currstep);
	eagerdelete_weaken(i, currstep.codl); // Chad - Mar 2009
}

function DNegRule_p(p) {
	return ((not_p(p)) && (not_p(p.arg)));
}

function DNegRule_block(p) {
	return findOnBranch(p.arg.arg);
}

function DNegRule(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "dneg",
			princ: i
		},
		codl: new Array()
	};
	extendBranchWithProp(p.arg.arg);
	allsteps.push(currstep);
	eagerdelete_weaken(i, currstep.codl); // Chad - Mar 2009
}

function AndMRule_p(p) {
	return (and_p(p) && (and_p(p.func.arg) || and_p(p.arg)));
}

function OrMRule_p(p) {
	return (or_p(p) && (or_p(p.func.arg) || or_p(p.arg)));
}

function AndRule_block(p) {
	return (findOnBranch(p.func.arg) && findOnBranch(p.arg));
}

// Chad - May 2009
function NegOr_block(p) {
	return (findNegOnBranch(p.arg.func.arg) && findNegOnBranch(p.arg.arg));
}

function AndMRule_block(p) {
	if (and_p(p)) {
		return (AndMRule_block(p.func.arg) && AndMRule_block(p.arg));
	} else {
		return findOnBranch(p);
	}
}

function OrRule_block(p) {
	return (findOnBranch(p.func.arg) || findOnBranch(p.arg));
}

// Chad - May 2009
function NegAnd_block(p) {
	return (findNegOnBranch(p.arg.func.arg) || findNegOnBranch(p.arg.arg));
}

function OrMRule_block(p) {
	if (or_p(p)) {
		return (OrMRule_block(p.func.arg) || OrMRule_block(p.arg));
	} else {
		return findOnBranch(p);
	}
}

function AndRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "and",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(p.func.arg, p.arg)));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

// Chad - May 2009
function NegOrRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "negor",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(not(p.arg.func.arg), not(p.arg.arg))));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function conjunctArray(a, p) {
	if (and_p(p)) {
		conjunctArray(a, p.func.arg);
		conjunctArray(a, p.arg);
	} else {
		a.push(p);
	}
}

function AndMRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var a = new Array();
	conjunctArray(a, p);
	currstep = {
		dom: branchPres(),
		rule: {
			name: "andm",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(a));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function OrRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "or",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(p.func.arg), new Array(p.arg)));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

// Chad - May 2009
function NegAndRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "negand",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(not(p.arg.func.arg)), new Array(not(p.arg.arg))));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function disjunctArrayArray(a, p) {
	if (or_p(p)) {
		disjunctArrayArray(a, p.func.arg);
		disjunctArrayArray(a, p.arg);
	} else {
		a.push(new Array(p));
	}
}

function OrMRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var a = new Array();
	disjunctArrayArray(a, p);
	currstep = {
		dom: branchPres(),
		rule: {
			name: "orm",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(a);
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function ImpliesRule_block(p) {
	return (findOnBranch(gen_not_body(p.func.arg)) || findOnBranch(p.arg));
}

function ImpliesRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "implies",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(p.arg), new Array(gen_not_body(p.func.arg)))); // add conclusion to branch, delay showing antecedent (if neg of antecedent is already on branch, will be silently closed)
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function neg_imp_p(p) {
	return (not_p(p) && imp_p(p.arg));
}

function NImpliesRule_block(p) {
	return (findOnBranch(p.arg.func.arg) && findOnBranch(gen_not_body(p.arg.arg)));
}

function NImpliesRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "nimplies",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(p.arg.func.arg, gen_not_body(p.arg.arg))));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function neg_equiv_p(p) {
	return (not_p(p) && equiv_p(p.arg));
}

// p is [x=y] where x and y have type B
function EqBRule_p(p) {
	return (eq_p(p) && (p.arg.tp == o));
}

// works if p is x =(B) y or x <-> y
function EqBRule_block(p) {
	var m = p.func.arg;
	var n = p.arg;
	return ((findOnBranch(m) && findOnBranch(n)) || (findOnBranch(not(m)) && findOnBranch(not(n))));
}

// works if p is x=(B) y or x <-> y
function EqBRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "eqb",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(p.func.arg, p.arg), new Array(not(p.func.arg), not(p.arg))));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

// p is ~[x=y] where x and y have type B
function NEqBRule_p(p) {
	return (not_p(p) && eq_p(p.arg) && (p.arg.arg.tp == o));
}

// works if p is ~x=(B) y or ~(x<->y)
function NEqBRule_block(p) {
	var m = p.arg.func.arg;
	var n = p.arg.arg;
	return ((findOnBranch(m) && findOnBranch(not(n))) || (findOnBranch(n) && findOnBranch(not(m))));
}

// works if p is ~x=(B) y or ~(x <-> y)
function NEqBRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var m = p.arg.func.arg;
	var n = p.arg.arg;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "neqb",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(m, not(n)), new Array(n, not(m))));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

// This only lists the ones that are not blocked. - Chad Mar 2009
function MatingRule_getMatingIDs(p) {
	var matingIDs = new Array();
	var currentID = 0;
	var branchArray = pfstate.subgoals[pfstate.branch];
	if (not_p(p) && p.arg.kind == apptrm) {
		var matingFunction = p.arg;
		while (matingFunction.kind == apptrm) {
			matingFunction = matingFunction.func;
		}
		if ((! (logconst_p(matingFunction))) && (matingFunction.kind != lamtrm)) {
			for (i in branchArray) {
				var pTrm = p.arg;
				if (branchArray[i].prop.kind == apptrm) {
					var app = branchArray[i].prop;
					var blocked = false;
					while (app.kind == apptrm && pTrm.kind == apptrm) {
						if ((! (eq_tps(app.arg.tp, pTrm.arg.tp))) || findOnBranch(not(eq(app.arg, pTrm.arg))) || findOnBranch(not(eq(pTrm.arg, app.arg)))) { // checks up to symmetry of diseqn
							////				    alert("eq_tps " + (!(eq_tps(app.arg.tp,pTrm.arg.tp))));
							////				    alert("find1 "+findOnBranch(not(eq(app.arg,pTrm.arg))));
							////				    alert("find2 "+findOnBranch(not(eq(pTrm.arg,app.arg))));
							////				    alert("test "+(findOnBranch(not(eq(app.arg,pTrm.arg))) || findOnBranch(not(eq(pTrm.arg,app.arg)))));
							blocked = true;
							//				    alert("blocked: " + i);
						}
						app = app.func;
						pTrm = pTrm.func;
					}
					//			    alert('here 2 '+trm_str(matingFunction)+' '+trm_str(app)+' i='+i+' blocked='+blocked);
					if (eq_trms(app, matingFunction) && !blocked) {
						matingIDs[currentID] = i;
						currentID++;
					}
				}
			}
		}
	}
	else if (p.kind == apptrm) {
		var matingFunction = p;
		while (matingFunction.kind == apptrm) {
			matingFunction = matingFunction.func;
		}
		if ((! (logconst_p(matingFunction))) && (matingFunction.kind != lamtrm)) {
			for (i in branchArray) {
				var pTrm = p;
				if (not_p(branchArray[i].prop) && branchArray[i].prop.arg.kind == apptrm) {
					var app = branchArray[i].prop.arg;
					var blocked = false;
					while (app.kind == apptrm && pTrm.kind == apptrm) {
						if ((! (eq_tps(app.arg.tp, pTrm.arg.tp))) || findOnBranch(not(eq(app.arg, pTrm.arg))) || findOnBranch(not(eq(pTrm.arg, app.arg)))) {
							blocked = true;
							//alert("blocked: " + i);
						}
						app = app.func;
						pTrm = pTrm.func;
					}
					if (eq_trms(app, matingFunction) && !blocked) {
						matingIDs[currentID] = i;
						currentID++;
					}
				}
			}
		}
	}
	return matingIDs;
}

// This now only lists the ones that are not blocked. - Chad Mar 2009
function ConfrontationRule_getConfrontationIDs(p) {
	var confrontationIDs = new Array();
	var currentID = 0;
	var branchArray = pfstate.subgoals[pfstate.branch];
	if (not_p(p) && basetype_eq_p(p.arg)) {
		var dl = p.arg.func.arg;
		var dr = p.arg.arg;
		var tp = dr.tp;
		//	    alert('here 1 dl = '+trm_str(dl)+' dr = '+trm_str(dr)+' tp = '+tp_str(tp));
		for (i in branchArray) {
			if (basetype_eq_p(branchArray[i].prop) && eq_tps(branchArray[i].prop.arg.tp, tp)) {
				var el = branchArray[i].prop.func.arg;
				var er = branchArray[i].prop.arg;
				//		    alert('here 2 el = '+trm_str(el)+' er = '+trm_str(er));
				var d1 = not(eq(el, dl));
				var d1s = not(eq(dl, el));
				var d2 = not(eq(er, dl));
				var d2s = not(eq(dl, er));
				var d3 = not(eq(el, dr));
				var d3s = not(eq(dr, el));
				var d4 = not(eq(er, dr));
				var d4s = not(eq(dr, er));
				if (! (((findOnBranch(d1) || findOnBranch(d1s)) && (findOnBranch(d2) || findOnBranch(d2s))) || ((findOnBranch(d3) || findOnBranch(d3s)) && (findOnBranch(d4) || findOnBranch(d4s))))) {
					confrontationIDs[currentID] = i;
					currentID++;
				}
			}
		}
	}
	else if (basetype_eq_p(p)) {
		var el = p.func.arg;
		var er = p.arg;
		var tp = el.tp;
		for (i in branchArray) {
			if (not_p(branchArray[i].prop) && basetype_eq_p(branchArray[i].prop.arg) && eq_tps(branchArray[i].prop.arg.arg.tp, tp)) {
				var dl = branchArray[i].prop.arg.func.arg;
				var dr = branchArray[i].prop.arg.arg;
				var d1 = not(eq(el, dl));
				var d1s = not(eq(dl, el));
				var d2 = not(eq(er, dl));
				var d2s = not(eq(dl, er));
				var d3 = not(eq(el, dr));
				var d3s = not(eq(dr, el));
				var d4 = not(eq(er, dr));
				var d4s = not(eq(dr, er));
				if (! (((findOnBranch(d1) || findOnBranch(d1s)) && (findOnBranch(d2) || findOnBranch(d2s))) || ((findOnBranch(d3) || findOnBranch(d3s)) && (findOnBranch(d4) || findOnBranch(d4s))))) {
					confrontationIDs[currentID] = i;
					currentID++;
				}
			}
		}
	}
	return confrontationIDs;
}

function MatingRule_p(p) {
	//        alert("Number of Mating IDs: " + MatingRule_getMatingIDs(p).length);
	return MatingRule_getMatingIDs(p).length != 0;
}

function inArray(a, x) {
	for (i in a) {
		if (a[i] == x) {
			return true;
		}
	}
	return false;
}

function MatingRule(k, j) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = MatingRule_getMatingIDs(branchArray[k].prop);
	if (!inArray(IDList, j)) {
		return;
	}
	var kProp = branchArray[k].prop;
	var jProp = branchArray[j].prop;

	if (not_p(kProp)) {
		kProp = kProp.arg;
	}
	else {
		jProp = jProp.arg;
	}

	var disequalities = new Array();
	var currentPair = 0;

	while (kProp.kind == apptrm && jProp.kind == apptrm) {
		disequalities[currentPair] = not(eq(kProp.arg, jProp.arg));
		if (findOnBranch(disequalities[currentPair])) {
			return;
		}
		kProp = kProp.func;
		jProp = jProp.func;
		currentPair++;
	}

	var toAdd = new Array();

	for (i in disequalities) {
		toAdd[i] = new Array(disequalities[i]);
	}
	currstep = {
		dom: branchPres(),
		rule: {
			name: "mating",
			princ1: k,
			princ2: j
		},
		codl: new Array()
	};
	generalExtendBranch(toAdd);
	allsteps.push(currstep);
}

// unused - Chad Mar 2009
function MatingRule_block(p) {
	//return false;
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = MatingRule_getMatingIDs(p);
	var canApply = false;

	if (IDList.length < 1 || !MatingRule_p(p)) {
		return true;
	}

	for (hurz in IDList) {
		var kProp = p;
		var jProp = branchArray[IDList[hurz]].prop;

		if (not_p(kProp)) {
			kProp = kProp.arg;
		}
		else {
			jProp = jProp.arg;
		}

		while (kProp.kind == apptrm && jProp.kind == apptrm) {

			if (eq_tps(kProp.arg.tp, jProp.arg.tp) && !findOnBranch(not(eq(kProp.arg, jProp.arg))) && !findOnBranch(not(eq(jProp.arg, kProp.arg)))) { // Chad - Mar 2009 - fixed == comparison on types to be eq_tps
				canApply = true;
				//alert("found applicable: " + IDList[hurz]);
				//generalExtendBranch(new Array(new Array(not(eq(kProp.arg,jProp.arg)))));
				//refreshUI();
			}
			else {
				//alert("found no applicable: " + IDList[hurz]);
			}
			kProp = kProp.func;
			jProp = jProp.func;
		}
	}
	return ! canApply;
}

// unused - Chad Mar 2009
function ConfrontationRule_block(p) {
	//return false;
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = ConfrontationRule_getConfrontationIDs(p);
	var canApply = false;

	if (IDList.length < 1 || !ConfrontationRule_p(p)) {
		return true;
	}

	for (hurz in IDList) {
		var kProp = p;
		var jProp = branchArray[IDList[hurz]].prop;

		if (not_p(kProp)) {
			kProp = kProp.arg;
		}
		else {
			jProp = jProp.arg;
		}

		while (kProp.kind == apptrm && jProp.kind == apptrm) {

			if (eq_tps(kProp.arg.tp, jProp.arg.tp) && !findOnBranch(not(eq(kProp.arg, jProp.arg))) && !findOnBranch(not(eq(jProp.arg, kProp.arg)))) { // Chad - Mar 2009 - fixed == comparison on types to be eq_tps
				canApply = true;
				//alert("found applicable: " + IDList[hurz]);
				//generalExtendBranch(new Array(new Array(not(eq(kProp.arg,jProp.arg)))));
				//refreshUI();
			}
			else {
				//alert("found no applicable: " + IDList[hurz]);
			}
			kProp = kProp.func;
			jProp = jProp.func;
		}
	}
	return ! canApply;
}

function MatingRuleAuto(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = MatingRule_getMatingIDs(branchArray[k].prop);
	if (IDList.length < 1) {
		return;
	}
	MatingRule(k, IDList[0]);
}

function MatingRule_BranchView(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = MatingRule_getMatingIDs(branchArray[k].prop);
	// remove buttons on branch and replace with other buttons
	var p = io.main.firstChild;
	var c = null;
	var j = 0;
	var seq = pfstate.subgoals[pfstate.branch];
	var l = seq.length;
	while (p) {
		if ((j >= 0) && (j < l)) {
			c = p.firstChild;
			while (c) {
				if (c.type == "button") {
					var c0 = c;
					c = c.nextSibling;
					p.removeChild(c0);
				} else {
					c = c.nextSibling;
				}
			}
			try {
				if (inArray(IDList, j)) {
					var button = top.mainFrame.window.document.createElement('Input');
					button.type = "button";
					button.value = "Mate With";
					addClickHandler(button, new Function("MatingRule(" + k + ", " + j + "); refreshUI();"));
					p.appendChild(button);
					throw ("done");
				}
			}
			catch(err) {
				if (err != "done") {
					throw (err);
				}
			}
		}
		j++;
		p = p.nextSibling;
	}
}

function ConfrontationRule_p(p) {
	if (eq_p(p) && (p.arg.tp.kind == basetp)) { // Chad - added restriction to base type - Mar 2009
		return ConfrontationRule_getConfrontationIDs(p).length != 0;
	}
	if (not_p(p) && eq_p(p.arg) && (p.arg.arg.tp.kind == basetp)) { // Chad - added restriction to base type - Mar 2009
		return ConfrontationRule_getConfrontationIDs(p).length != 0;
	}
	return false;
}

function ConfrontationRule(k, j) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = ConfrontationRule_getConfrontationIDs(branchArray[k].prop);
	var IDListSwap = null;
	if (not_p(branchArray[k].prop)) {
		ConfrontationRule_1(j, k);
	} else {
		ConfrontationRule_1(k, j);
	}
}

// k is eqn, j is deqn
function ConfrontationRule_1(k, j) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var e = branchArray[k].prop;
	var d = branchArray[j].prop.arg;
	var el = e.func.arg;
	var er = e.arg;
	var dl = d.func.arg;
	var dr = d.arg;
	var d1 = not(eq(el, dl));
	var d2 = not(eq(er, dl));
	var d3 = not(eq(el, dr));
	var d4 = not(eq(er, dr));
	currstep = {
		dom: branchPres(),
		rule: {
			name: "confront",
			princ1: k,
			princ2: j
		},
		codl: new Array()
	};
	generalExtendBranch(new Array(new Array(d1, d2), new Array(d3, d4)));
	allsteps.push(currstep);
}

function ConfrontationRuleAuto(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = ConfrontationRule_getConfrontationIDs(branchArray[k].prop);
	var IDListSwap = null;
	if (not_p(branchArray[k].prop)) {
		IDListSwap = ConfrontationRule_getConfrontationIDs(not(eq(branchArray[k].prop.arg.arg, branchArray[k].prop.arg.func.arg)));
	}
	else {
		IDListSwap = ConfrontationRule_getConfrontationIDs(eq(branchArray[k].prop.arg, branchArray[k].prop.func.arg));
	}
	if (IDList.length < 1 && IDListSwap.length < 1) {
		return;
	}
	if (IDList.length > 0) {
		ConfrontationRule(k, IDList[0]);
	}
	else {
		ConfrontationRule(k, IDListSwap[0]);
	}
}

function Confrontation_BranchView(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var IDList = ConfrontationRule_getConfrontationIDs(branchArray[k].prop);
	var IDListSwap = null;
	if (not_p(branchArray[k].prop)) {
		IDListSwap = ConfrontationRule_getConfrontationIDs(not(eq(branchArray[k].prop.arg.arg, branchArray[k].prop.arg.func.arg)));
	}
	else {
		IDListSwap = ConfrontationRule_getConfrontationIDs(eq(branchArray[k].prop.arg, branchArray[k].prop.func.arg));
	}

	// remove buttons on branch and replace with other buttons
	var p = io.main.firstChild;
	var c = null;
	var j = 0;
	var seq = pfstate.subgoals[pfstate.branch];
	var l = seq.length;
	while (p) {
		if ((j >= 0) && (j < l)) {
			c = p.firstChild;
			while (c) {
				if (c.type == "button") {
					var c0 = c;
					c = c.nextSibling;
					p.removeChild(c0);
				} else {
					c = c.nextSibling;
				}
			}
			try {
				if (inArray(IDList, j) || inArray(IDListSwap, j)) {
					var button = top.mainFrame.window.document.createElement('Input');
					button.type = "button";
					button.value = "Confront Against";
					addClickHandler(button, new Function("ConfrontationRule(" + k + ", " + j + "); refreshUI();"));
					p.appendChild(button);
					throw ("done");
				}
			}
			catch(err) {
				if (err != "done") {
					throw (err);
				}
			}
		}
		j++;
		p = p.nextSibling;
	}
}

// Decomposition - Matthias Hoeschele - added March 2009
// Functions needed for the rule
function DecompositionRule_block(p) {
	if (not_p(p) && eq_p(p.arg)) {
		var r = p.arg.arg;
		var l = p.arg.func.arg;
		while (l.kind == apptrm && r.kind == apptrm) {
			if ((! (eq_tps(l.arg.tp, r.arg.tp))) || findOnBranch(not(eq(l.arg, r.arg))) || findOnBranch(not(eq(r.arg, l.arg)))) {
				return true;
			}
			l = l.func;
			r = r.func;
		}
		return false;
	}
}

function DecompositionRule_p(p) {
	if (not_p(p) && basetype_eq_p(p.arg)) { // Chad - added restriction to base type - Mar 2009
		var r = p.arg.arg;
		var l = p.arg.func.arg;
		while (l.kind == apptrm && r.kind == apptrm) {
			l = l.func;
			r = r.func;
		}
		return ((! (logconst_p(l))) && (l.kind == vartrm || l.kind == consttrm || l.kind == deftrm) && eq_trms(l, r));
	}
}

// arity 1 predicate - Chad - Apr 2009
function DecompositionRule1_p(p) {
	if (not_p(p) && basetype_eq_p(p.arg)) { // Chad - added restriction to base type - Mar 2009
		var r = p.arg.arg;
		var l = p.arg.func.arg;
		if (l.kind == apptrm && r.kind == apptrm) { // do exactly zero or one
			l = l.func;
			r = r.func;
		}
		return ((! (logconst_p(l))) && (l.kind == vartrm || l.kind == consttrm || l.kind == deftrm) && eq_trms(l, r));
	}
}

function DecompositionRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var r = p.arg.arg;
	var l = p.arg.func.arg;

	var disequalities = new Array();

	while (l.kind == apptrm && r.kind == apptrm) {
		disequalities.push(new Array(not(eq(l.arg, r.arg))));
		l = l.func;
		r = r.func;
	}
	currstep = {
		dom: branchPres(),
		rule: {
			name: "decompose",
			princ: k
		},
		codl: new Array()
	};
	generalExtendBranch(disequalities);
	allsteps.push(currstep);
}

// p is !x:a.p1
function ForallRule_p(p) {
	return ((p.kind == apptrm) && (p.func.kind == consttrm) && (p.func.name == "*all*"));
}

function ForallRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var tp = p.arg.tp.dom;
	var p1 = top.headerFrame.window.document.createElement('P');
	var p2 = top.headerFrame.window.document.createElement('P');
	var button = top.headerFrame.window.document.createElement('Input');
	button.type = "button";
	button.value = "Enter";
	currstep = {
		dom: branchPres(),
		rule: {
			name: "forall",
			princ: k,
			trm: null
		},
		codl: new Array()
	};
	addClickHandler(button, function() {
		ForallRule2();
	});
	p1.appendChild(top.headerFrame.window.document.createTextNode('Enter a term of type ' + tp_str(tp) + ':'));
	p2.appendChild(entertext);
	p2.appendChild(button);
	entertext.trm = p.arg;
	entertext.tp = tp;
	entertext.value = "";
	cleartop();
	io.inputtop.appendChild(p1);
	io.inputtop.appendChild(p2);
}

function ForallRule2() {
	//    alert('ForallRule2 termnames'); for (x in termnames) { alert(x+' is free'); } // delete me
	var a = new parse(entertext);
	var tp = entertext.tp;
	try {
		var trm = parse_trm(a);
		if (trm == null) {
			throw ('Could not read term');
		} else if (uses_disallowed(trm)) {
			throw ('Term Uses a Disallowed Constant');
		} else if (eq_tps(trm.tp, tp)) {
			var p = entertext.trm;
			var mm = app_lam(p, trm);
			currstep.rule.trm = trm;
			extendBranchWithProp(mm);
			allsteps.push(currstep);
		} else {
			throw ('Term does not have correct type');
		}
	}
	catch(err) {
		try {
			a = new parse(entertext); // Chad - added Apr 2009 to allow for a new name to be the instantiation
			var x = read_token(a);
			if (identifier_p(x) && (!(keyword_p(x))) && (!(prefixops[x])) && (!(infixops[x])) && (!(termnames[x]))) {
				var p = entertext.trm;
				var z = lvar(x, tp);
				var mm = app_lam(p, z);
				currstep.rule.trm = z;
				extendBranchWithEigenVarAndProp(x, z, mm); // call this to put the new name onto ctx
				allsteps.push(currstep);
			} else {
				throw (err);
			}
		}
		catch(err) {
			alert(err);
			return;
		}
	}
	refreshUI();
}

// Chad - May 2009
function NegExistsRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var tp = p.arg.arg.tp.dom;
	var p1 = top.headerFrame.window.document.createElement('P');
	var p2 = top.headerFrame.window.document.createElement('P');
	var button = top.headerFrame.window.document.createElement('Input');
	button.type = "button";
	button.value = "Enter";
	currstep = {
		dom: branchPres(),
		rule: {
			name: "negexists",
			princ: k,
			trm: null
		},
		codl: new Array()
	};
	addClickHandler(button, function() {
		NegExistsRule2();
	});
	p1.appendChild(top.headerFrame.window.document.createTextNode('Enter a term of type ' + tp_str(tp) + ':'));
	p2.appendChild(entertext);
	p2.appendChild(button);
	entertext.trm = p.arg.arg;
	entertext.tp = tp;
	entertext.value = "";
	cleartop();
	io.inputtop.appendChild(p1);
	io.inputtop.appendChild(p2);
}

function NegExistsRule2() {
	//    alert('NegExistsRule2 termnames'); for (x in termnames) { alert(x+' is free'); } // delete me
	var a = new parse(entertext);
	var tp = entertext.tp;
	try {
		var trm = parse_trm(a);
		if (trm == null) {
			throw ('Could not read term');
		} else if (uses_disallowed(trm)) {
			throw ('Term Uses a Disallowed Constant');
		} else if (eq_tps(trm.tp, tp)) {
			var p = entertext.trm;
			var mm = not(app_lam(p, trm));
			currstep.rule.trm = trm;
			extendBranchWithProp(mm);
			allsteps.push(currstep);
		} else {
			throw ('Term does not have correct type');
		}
	}
	catch(err) {
		try {
			a = new parse(entertext); // Chad - added Apr 2009 to allow for a new name to be the instantiation
			var x = read_token(a);
			if (identifier_p(x) && (!(keyword_p(x))) && (!(prefixops[x])) && (!(infixops[x])) && (!(termnames[x]))) {
				var p = entertext.trm;
				var z = lvar(x, tp);
				var mm = not(app_lam(p, z));
				currstep.rule.trm = z;
				extendBranchWithEigenVarAndProp(x, z, mm); // call this to put the new name onto ctx
				allsteps.push(currstep);
			} else {
				throw (err);
			}
		}
		catch(err) {
			alert(err);
			return;
		}
	}
	refreshUI();
}

// p is ?x:a.p1
function ExistsRule_p(p) {
	return ((p.kind == apptrm) && (p.func.kind == consttrm) && (p.func.name == "*ex*"));
}

function ExistsRule_block_f_real(x, a, p1, q) {
	return fo_matches(new Array({
		lft: p1,
		rght: q,
		ab: null
	}), new Array({
		name: x,
		tp: a
	}));
}

// assuming p is (*ex* p1), checks if q is of the form (p1 m) for some m,
// or the beta redex of (p1 m) for some m if p1 is an abstraction (the usual case)
var ExistsRule_block_f = new Function('p', 'q', 'if (p.arg.kind == lamtrm) { return ExistsRule_block_f_real(p.arg.varname,p.arg.dom,p.arg.body,q); } else { return ((q.kind == apptrm) && eq_tps(p.arg.tp,q.func.tp) && eq_trms(p.arg,q.func)); }');

function ExistsRule_block(p) {
	return findOnBranchF(ExistsRule_block_f, p);
}

// NegForall - Chad - May 2009
// This 'real' blocking func is the same as the one for ExistsRule
function NegForall_block_f_real(x, a, p1, q) {
	return fo_matches(new Array({
		lft: p1,
		rght: q,
		ab: null
	}), new Array({
		name: x,
		tp: a
	}));
}

// assuming p is (~ (*ex* p1)), checks if q is of the form (~ (p1 m)) for some m,
// or the beta redex of (~ (p1 m)) for some m if p1 is an abstraction (the usual case)
var NegForall_block_f = new Function('p', 'q', 'if (not_p(q)) { if (p.arg.arg.kind == lamtrm) { return NegForall_block_f_real(p.arg.arg.varname,p.arg.arg.dom,p.arg.arg.body,q.arg); } else { return ((q.arg.kind == apptrm) && eq_tps(p.arg.arg.tp,q.arg.func.tp) && eq_trms(p.arg.arg,q.arg.func)); }} else { return false; }');

function NegForall_block(p) {
	return findOnBranchF(NegForall_block_f, p);
}

var freeinbranch_f = new Function('x', 'q', 'return free_in(x,q);');

function legalwitnessname(x) {
	return ! (findOnBranchF(freeinbranch_f, x));
}

function getLegalWitnessName(x) {
	var name = x;
	while (findOnBranchF(freeinbranch_f, name) || ((termnames[name] != null) && ((termnames[name].kind == consttrm) || (termnames[name].kind == deftrm)))) {
		name = name + "'";
	}
	return name;
}

function ExistsRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var tp = p.arg.tp.dom;
	var p1 = top.headerFrame.window.document.createElement('P');
	var p2 = top.headerFrame.window.document.createElement('P');
	var button = top.headerFrame.window.document.createElement('Input');
	button.type = "button";
	button.value = "Enter";
	currstep = {
		dom: branchPres(),
		rule: {
			name: "exists",
			princ: k,
			varname: null
		},
		codl: new Array()
	};
	addClickHandler(button, function() {
		ExistsRule2();
	});
	p1.appendChild(top.headerFrame.window.document.createTextNode('Enter a parameter of type ' + tp_str(tp) + ':'));
	p2.appendChild(entertext);
	p2.appendChild(button);
	entertext.trm = p.arg;
	entertext.tp = tp;
	if ((p.arg.kind == lamtrm) && (legalwitnessname(p.arg.varname))) {
		entertext.value = p.arg.varname;
	} else {
		entertext.value = "";
	}
	cleartop();
	io.inputtop.appendChild(p1);
	io.inputtop.appendChild(p2);
}

function ExistsRule2() {
	var a = new parse(entertext);
	try {
		var id = read_token(a);
		var tp = entertext.tp;
		if (identifier_p(id)) {
			var z = termnames[id];
			if ((z != null) && ((z.kind == consttrm) || (z.kind == deftrm))) {
				alert('This identifier has already been used as a constant or definition.');
			} else if (!legalwitnessname(id)) {
				alert('This witness name causes a conflict since it occurs in the branch already.');
			} else {
				var p = entertext.trm;
				z = lvar(id, tp);
				currstep.rule.varname = id;
				extendBranchWithEigenVarAndProp(id, z, app_lam(p, z));
				allsteps.push(currstep);
				eagerdelete_weaken(currstep.rule.princ, currstep.codl); // Chad - Mar 2009
			}
		} else {
			alert('Expected an identifier');
		}
	}
	catch(err) {
		alert(err);
		return;
	}
	refreshUI();
}

// Chad - May 2009
function NegForallRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	var tp = p.arg.arg.tp.dom;
	var p1 = top.headerFrame.window.document.createElement('P');
	var p2 = top.headerFrame.window.document.createElement('P');
	var button = top.headerFrame.window.document.createElement('Input');
	button.type = "button";
	button.value = "Enter";
	currstep = {
		dom: branchPres(),
		rule: {
			name: "negforall",
			princ: k,
			varname: null
		},
		codl: new Array()
	};
	addClickHandler(button, function() {
		NegForallRule2();
	});
	p1.appendChild(top.headerFrame.window.document.createTextNode('Enter a parameter of type ' + tp_str(tp) + ':'));
	p2.appendChild(entertext);
	p2.appendChild(button);
	entertext.trm = p.arg.arg;
	entertext.tp = tp;
	if ((p.arg.arg.kind == lamtrm) && (legalwitnessname(p.arg.arg.varname))) {
		entertext.value = p.arg.arg.varname;
	} else {
		entertext.value = "";
	}
	cleartop();
	io.inputtop.appendChild(p1);
	io.inputtop.appendChild(p2);
}

function NegForallRule2() {
	var a = new parse(entertext);
	try {
		var id = read_token(a);
		var tp = entertext.tp;
		if (identifier_p(id)) {
			var z = termnames[id];
			if ((z != null) && ((z.kind == consttrm) || (z.kind == deftrm))) {
				alert('This identifier has already been used as a constant or definition.');
			} else if (!legalwitnessname(id)) {
				alert('This witness name causes a conflict since it occurs in the branch already.');
			} else {
				var p = entertext.trm;
				z = lvar(id, tp);
				currstep.rule.varname = id;
				extendBranchWithEigenVarAndProp(id, z, not(app_lam(p, z)));
				allsteps.push(currstep);
				eagerdelete_weaken(currstep.rule.princ, currstep.codl); // Chad - Mar 2009
			}
		} else {
			alert('Expected an identifier');
		}
	}
	catch(err) {
		alert(err);
		return;
	}
	refreshUI();
}

// p is ?x:a.p1 and x can be used as witness name
function ExistsStarRule_p(p) {
	return ((p.kind == apptrm) && (p.func.kind == consttrm) && (p.func.name == "*ex*") && (p.arg.kind == lamtrm) && (legalwitnessname(p.arg.varname)));
}

function ExistsStarRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var used = new Object();
	var p = branchArray[k].prop;
	var ok = true;
	while (ok) {
		used[p.arg.varname] = lvar(p.arg.varname, p.func.tp.dom.dom); // is this necessary?  Do I already have an lvar for this name, maybe in pfstate.ctxs[?] or in a global varnames variable?
		p = p.arg.body; // strip away exists x
		ok = (ExistsStarRule_p(p)) && (!(used[p.arg.varname]));
	}
	currstep = {
		dom: branchPres(),
		rule: {
			name: "exists*",
			princ: k,
			varnames: used
		},
		codl: new Array()
	};
	extendBranchWithEigenVarsAndProp(used, p);
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function ExistsAutoRule_p(p) {
	return ((p.kind == apptrm) && (p.func.kind == consttrm) && (p.func.name == "*ex*") && (p.arg.kind == lamtrm) && (legalwitnessname(getLegalWitnessName(p.arg.varname))));
}

function ExistsAutoRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var used = new Object();
	var p = branchArray[k].prop;
	var ok = true;
	while (ok) {
		var name = getLegalWitnessName(p.arg.varname);
		used[name] = lvar(name, p.func.tp.dom.dom); // is this necessary?  Do I already have an lvar for this name, maybe in pfstate.ctxs[?] or in a global varnames variable?
		p = p.arg.body; // strip away exists x
		ok = (ExistsAutoRule_p(p)) && (!(used[getLegalWitnessName(p.arg.varname)]));
	}
	currstep = {
		dom: branchPres(),
		rule: {
			name: "exists*",
			princ: k,
			varnames: used
		},
		codl: new Array()
	};
	extendBranchWithEigenVarsAndProp(used, p);
	allsteps.push(currstep);
}

// Chad - May 2009
// p is ~!x:a.p1 and x can be used as witness name
function NegForallStarRule_p(p) {
	return (not_p(p) && (NegForallStarRule2_p(p.arg)));
}

function NegForallStarRule2_p(p) {
	return ((p.kind == apptrm) && (p.func.kind == consttrm) && (p.func.name == "*all*") && (p.arg.kind == lamtrm) && (legalwitnessname(p.arg.varname)));
}

function NegForallStarRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var used = new Object();
	var p = branchArray[k].prop.arg; // p is !x.body (stripped negation already)
	var ok = true;
	while (ok) {
		used[p.arg.varname] = lvar(p.arg.varname, p.func.tp.dom.dom); // is this necessary?  Do I already have an lvar for this name, maybe in pfstate.ctxs[?] or in a global varnames variable?
		p = p.arg.body; // strip away forall x
		ok = (NegForallStarRule2_p(p)) && (!(used[p.arg.varname]));
	}
	currstep = {
		dom: branchPres(),
		rule: {
			name: "negforall*",
			princ: k,
			varnames: used
		},
		codl: new Array()
	};
	extendBranchWithEigenVarsAndProp(used, not(p));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

// function ExistsAutoRule(k) {
//   var branchArray = pfstate.subgoals[pfstate.branch];
//   var used = new Object();
//   var p = branchArray[k].prop;
//     var name = getLegalWitnessName(p.arg.varname);
//     used[name] = lvar(name, p.func.tp.dom.dom); // is this necessary?  Do I already have an lvar for this name, maybe in pfstate.ctxs[?] or in a global varnames variable?
//     p = p.arg.body; // strip away exists x
// 
//   extendBranchWithEigenVarsAndProp(used, p);
// }
// Functional Equality Rules
function EqFRule_p(p) {
	return (eq_p(p) && (p.arg.tp.kind == artp));
}

// f term of type a -> b
// x string (name of a variable of type a) (not in f or m)
// m term of type b
// check if either f is (\y.n) and n[y:=x] == m
// or f is not an abstraction and (f x) is m
function eq_app_lam_var_trm(f, x, m) {
	if (f.kind == lamtrm) {
		return aeq_trms(f.body, m, alpha_cons(f.varname, x, null));
	} else {
		return ((m.kind == apptrm) && (m.arg.kind == vartrm) && (m.arg.name == x) && eq_tps(f.tp, m.func.tp) && eq_trms(f, m.func));
	}
}

// assume p is f = g where f,g:A -> B
// check if q is of the form !x.(fx)'=(gx)',
// where m' is the beta reduct if m is a beta redex, and m otherwise
function EqFRule_block_1(p, q) {
	if (all_p(q) && eq_p(q.arg.body)) {
		var x = q.arg.varname;
		var pl = p.func.arg;
		var pr = p.arg;
		var ql = q.arg.body.func.arg;
		var qr = q.arg.body.arg;
		return (eq_app_lam_var_trm(pl, x, ql) && eq_app_lam_var_trm(pr, x, qr));
	} else {
		return false;
	}
}

var EqFRule_block_f = new Function('p', 'q', 'return EqFRule_block_1(p,q);');

function EqFRule_block(p) {
	return findOnBranchF(EqFRule_block_f, p);
}

// This version asks for instantiation for argument
function EqFRuleArg(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop;
	var tp = p.arg.tp.dom;
	var p1 = top.headerFrame.window.document.createElement('P');
	var p2 = top.headerFrame.window.document.createElement('P');
	var button = top.headerFrame.window.document.createElement('Input');
	button.type = "button";
	button.value = "Enter";
	currstep = {
		dom: branchPres(),
		rule: {
			name: "eqf",
			princ: i,
			trm: null
		},
		codl: new Array()
	};
	addClickHandler(button, function() {
		EqFRuleArg2();
	});
	p1.appendChild(top.headerFrame.window.document.createTextNode('Enter a term of type ' + tp_str(tp) + ':'));
	p2.appendChild(entertext);
	p2.appendChild(button);
	entertext.trm = p;
	entertext.tp = tp;
	entertext.value = "";
	cleartop();
	io.inputtop.appendChild(p1);
	io.inputtop.appendChild(p2);
}

function EqFRuleArg2() {
	var a = new parse(entertext);
	try {
		var trm = parse_trm(a);
		var tp = entertext.tp;
		if (trm == null) {
			throw ('Could not read term');
		} else if (uses_disallowed(trm)) {
			throw ('Term Uses a Disallowed Constant');
		} else if (eq_tps(trm.tp, tp)) {
			var p = entertext.trm;
			currstep.rule.trm = trm;
			extendBranchWithProp(eq(app_lam(p.func.arg, trm), app_lam(p.arg, trm)));
			allsteps.push(currstep);
		} else {
			throw ('Term does not have correct type');
		}
	}
	catch(err) {
		try {
			a = new parse(entertext); // Chad - added Apr 2009 to allow for a new name to be the instantiation
			var x = read_token(a);
			if (identifier_p(x) && (!(keyword_p(x))) && (!(prefixops[x])) && (!(infixops[x])) && (!(termnames[x]))) {
				var p = entertext.trm;
				var z = lvar(x, tp);
				var mm = eq(app_lam(p.func.arg, z), app_lam(p.arg, z));
				currstep.rule.trm = z;
				extendBranchWithEigenVarAndProp(x, z, mm); // call this to put the new name onto ctx
				allsteps.push(currstep);
			} else {
				throw (err);
			}
		}
		catch(err) {
			alert(err);
			return;
		}
	}
	refreshUI();
}

// This version creates a forall
// function EqFRule (i) {
//     var branchArray = pfstate.subgoals[pfstate.branch];
//     var p = branchArray[i].prop;
//     var tp = p.arg.tp.dom;
//     var p1 = top.headerFrame.window.document.createElement('P');
//     var p2 = top.headerFrame.window.document.createElement('P');
//     var button = top.headerFrame.window.document.createElement('Input');
//     button.type = "button";
//     button.value = "Enter";
//     addClickHandler(button,function () { EqFRule2(); });
//     p1.appendChild(top.headerFrame.window.document.createTextNode('Enter a variable of type ' + tp_str(tp) + ':'));
//     p2.appendChild(entertext);
//     p2.appendChild(button);
//     entertext.trm = p;
//     entertext.tp = tp;
//     if ((p.arg.kind == lamtrm) && (not_free_in(p.arg.varname,p))) {
// 	entertext.value = p.arg.varname;
//     } else if ((p.func.arg.kind == lamtrm) && (not_free_in(p.func.arg.varname,p))) {
// 	entertext.value = p.func.arg.varname;
//     } else {
// 	entertext.value = "";
//     }
//     cleartop();
//     io.inputtop.appendChild(p1);
//     io.inputtop.appendChild(p2);
// }
// function EqFRule2() {
//     var a = new parse(entertext);
//     try {
// 	var id = read_token(a);
// 	var p = entertext.trm;
// 	var tp = entertext.tp;
// 	if (identifier_p(id)) {
// 	    var z = termnames[id];
// 	    if ((z != null) && ((z.kind == consttrm) || (z.kind == deftrm))) {
// 		alert('This identifier has already been used as a constant or definition.');
// 	    } else if (not_free_in(id,p)) {
// 		z = lvar(id,tp);
// 		extendBranchWithProp(all(id,tp,eq(app_lam(p.func.arg,z),app_lam(p.arg,z))));
// 	    } else {
// 		alert('This variable name causes a conflict since it occurs free in the equation.');
// 	    }
// 	} else {
// 	    alert('Expected an identifier');
// 	}
//     }
//     catch (err)
//     {
// 	alert(err);
//     }
// }
function NEqFRule_p(p) {
	return (not_p(p) && eq_p(p.arg) && (p.arg.arg.tp.kind == artp));
}

// Like f, but both sides must be lambda abstractions
function NEqXiRule_p(p) {
	return (not_p(p) && eq_p(p.arg) && (p.arg.arg.tp.kind == artp) && (p.arg.arg.kind == lamtrm) && (p.arg.func.arg.kind == lamtrm));
}

function NEqFRule_block_f_real(f, g, q) {
	if (eq_p(q)) {
		var a = f.tp.dom;
		var a2 = q.arg.tp;
		var ql = q.func.arg;
		var qr = q.arg;
		if (eq_tps(a, a2)) {
			if (f.kind == lamtrm) {
				if (g.kind == lamtrm) {
					var x = f.varname;
					var y = g.varname;
					return fo_matches(new Array({
						lft: f.body,
						rght: ql,
						ab: null
					},
					{
						lft: subst(g.body, y, lvar(x, f.dom)),
						rght: qr,
						ab: null
					}), new Array({
						name: x,
						tp: a
					}));
					// no need to match in remaining cases, since we can see the witness term as the argument of an application on one side
				} else if ((qr.kind == apptrm) && (eq_trms(g, qr.func))) {
					var w = qr.arg;
					return eq_trms(subst(f.body, f.varname, w), ql);
				} else {
					return false;
				}
			} else if ((g.kind == lamtrm) && (ql.kind == apptrm) && (eq_trms(f, ql.func))) {
				var w = qr.arg;
				return eq_trms(subst(g.body, g.varname, w), ql);
			} else {
				return ((qr.kind == apptrm) && (eq_trms(g, qr.func)) && (ql.kind == apptrm) && (eq_trms(f, ql.func)) && (eq_trms(ql.arg, qr.arg)));
			}
		} else {
			return false;
		}
	} else {
		return false;
	}
}

var NEqFRule_block_f = new Function('p', 'q', 'return NEqFRule_block_f_real(p.func.arg,p.arg,q);');

function NEqFRule_block(p) {
	return findOnBranchF(NEqFRule_block_f, p.arg);
}

function NEqFRule(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop.arg;
	var tp = p.arg.tp.dom;
	var p1 = top.headerFrame.window.document.createElement('P');
	var p2 = top.headerFrame.window.document.createElement('P');
	var button = top.headerFrame.window.document.createElement('Input');
	button.type = "button";
	button.value = "Enter";
	currstep = {
		dom: branchPres(),
		rule: {
			name: "neqf",
			princ: i,
			varname: null
		},
		codl: new Array()
	};
	addClickHandler(button, function() {
		NEqFRule2();
	});
	p1.appendChild(top.headerFrame.window.document.createTextNode('Enter a variable of type ' + tp_str(tp) + ':'));
	p2.appendChild(entertext);
	p2.appendChild(button);
	entertext.trm = p;
	entertext.tp = tp;
	if ((p.arg.kind == lamtrm) && (not_free_in(p.arg.varname, p))) {
		entertext.value = p.arg.varname;
	} else if ((p.func.arg.kind == lamtrm) && (not_free_in(p.func.arg.varname, p))) {
		entertext.value = p.func.arg.varname;
	} else {
		entertext.value = "";
	}
	cleartop();
	io.inputtop.appendChild(p1);
	io.inputtop.appendChild(p2);
}

function NEqFRule2() {
	var a = new parse(entertext);
	try {
		var id = read_token(a);
		var tp = entertext.tp;
		if (identifier_p(id)) {
			var z = termnames[id];
			if ((z != null) && ((z.kind == consttrm) || (z.kind == deftrm))) {
				alert('This identifier has already been used as a constant or definition.');
			} else if (!legalwitnessname(id)) {
				alert('This witness name causes a conflict since it occurs in the branch already.');
			} else {
				var p = entertext.trm;
				z = lvar(id, tp);
				currstep.rule.varname = id;
				extendBranchWithEigenVarAndProp(id, z, not(eq(app_lam(p.func.arg, z), app_lam(p.arg, z))));
				allsteps.push(currstep);
				eagerdelete_weaken(currstep.rule.princ, currstep.codl); // Chad - Mar 2009
			}
		} else {
			alert('Expected an identifier');
			return;
		}
		refreshUI();
	}
	catch(err) {
		alert(err);
	}
}

function NEqFAutoRule(i) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[i].prop.arg;
	var id = getLegalWitnessName("feq");
	z = lvar(id, tp);
	currstep = {
		dom: branchPres(),
		rule: {
			name: "neqf",
			princ: i,
			varname: id
		},
		codl: new Array()
	};
	extendBranchWithEigenVarAndProp(id, z, not(eq(app_lam(p.func.arg, z), app_lam(p.arg, z))));
	allsteps.push(currstep);
}

function BetaRule_block(p) {
	return findOnBranch(beta_normalize(p));
}

function BetaRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "beta",
			princ: k
		},
		codl: new Array()
	};
	extendBranchWithProp(beta_normalize(p));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

// assume p is beta normal, but not eta short
function EtaShortRule_block(p) {
	return findOnBranch(eta_short_form(p));
}

function EtaShortRule(k) {
	var branchArray = pfstate.subgoals[pfstate.branch];
	var p = branchArray[k].prop;
	currstep = {
		dom: branchPres(),
		rule: {
			name: "etashort",
			princ: k
		},
		codl: new Array()
	};
	extendBranchWithProp(eta_short_form(p));
	allsteps.push(currstep);
	eagerdelete_weaken(k, currstep.codl); // Chad - Mar 2009
}

function repRuleDataDebug() {
	botmsg('*** repRuleData:');
	for (i in repRuleData) {
		var rr = repRuleData[i];
		botmsg(i + ': i=' + rr.i + ',j=' + rr.j);
		botmsg('lft ' + trm_str(rr.lft));
		botmsg('rght ' + trm_str(rr.rght));
	}
}

function precomputeRepRule() {
	var seq = pfstate.subgoals[pfstate.branch];
	repRuleData = new Array();
	for (i in seq) {
		var e = seq[i].prop;
		if (univ_eqn_p(e)) {
			var evars = new Array();
			var frees = new Object();
			var bvars = new Object();
			unionFreesOf(frees, e, bvars);
			while (all_p(e)) {
				evars.push({
					name: e.arg.varname,
					tp: e.arg.dom
				});
				e = e.arg.body;
			}
			var l = e.func.arg;
			var r = e.arg;
			var le = true;
			var re = true;
			for (xindex in evars) {
				var x = evars[xindex].name;
				if (not_free_in(x, l)) {
					le = false;
				}
				if (not_free_in(x, r)) {
					re = false;
				}
			}
			if (le) {
				if (re) {
					// both directions OK
					for (j in seq) {
						if (rew_applies_somewhere_p(evars, l, r, seq[j].prop, frees)) {
							repRuleData.push({
								evars: evars,
								lft: l,
								rght: r,
								frees: frees,
								dir: 3,
								i: i,
								j: j
							});
						} else if (rew_applies_somewhere_p(evars, r, l, seq[j].prop, frees)) {
							repRuleData.push({
								evars: evars,
								lft: l,
								rght: r,
								frees: frees,
								dir: 3,
								i: i,
								j: j
							});
						}
					}
				} else {
					// only rewrite l -> r
					for (j in seq) {
						if (rew_applies_somewhere_p(evars, l, r, seq[j].prop, frees)) {
							repRuleData.push({
								evars: evars,
								lft: l,
								rght: r,
								frees: frees,
								dir: 1,
								i: i,
								j: j
							});
						}
					}
				}
			} else if (re) {
				// only rewrite r -> l
				for (j in seq) {
					if (rew_applies_somewhere_p(evars, r, l, seq[j].prop, frees)) {
						repRuleData.push({
							evars: evars,
							lft: l,
							rght: r,
							frees: frees,
							dir: 2,
							i: i,
							j: j
						});
					}
				}
			}
		}
	}
}

function rew_applies_somewhere_p(evars, l, r, m, frees) {
	var tpseq = eq_tps(l.tp, m.tp);
	if (tpseq && fo_matches(new Array({
		lft: l,
		rght: m,
		ab: null
	}), evars)) {
		return true;
	} else if (m.kind == apptrm) {
		return (rew_applies_somewhere_p(evars, l, r, m.func, frees) || rew_applies_somewhere_p(evars, l, r, m.arg, frees));
	} else if (m.kind == lamtrm) {
		if (frees[m.varname]) {
			return false;
		} else {
			return rew_applies_somewhere_p(evars, l, r, m.body, frees);
		}
	} else {
		return false;
	}
}

function RepRule_p(e) {
	// use precomputed data in repRuleData -- array of objects which let us know if i can be used to rewrite j
	var seq = pfstate.subgoals[pfstate.branch];
	var rrd = repRuleData;
	try {
		for (r in rrd) {
			if (e == seq[rrd[r].i].prop) { // props should be pointer equal
				throw ("found");
			}
		}
		return false;
	}
	catch(err) {
		if (err == "found") {
			return true;
		} else {
			throw (err);
		}
	}
}

function RepRule(i) {
	// remove buttons on branch and replace with other buttons
	var p = io.main.firstChild;
	var c = null;
	var j = 0;
	var seq = pfstate.subgoals[pfstate.branch];
	var l = seq.length;
	var rrd = repRuleData;
	while (p) {
		if ((j >= 0) && (j < l)) {
			c = p.firstChild;
			while (c) {
				if (c.type == "button") {
					var c0 = c;
					c = c.nextSibling;
					p.removeChild(c0);
				} else {
					c = c.nextSibling;
				}
			}
			try {
				for (r in rrd) {
					if ((rrd[r].i == i) && (rrd[r].j == j)) {
						var button = top.mainFrame.window.document.createElement('Input');
						button.type = "button";
						button.value = "Replace Subterms";
						addClickHandler(button, RepRule2Closure(i, j));
						p.appendChild(button);
						throw ("done");
					}
				}
			}
			catch(err) {
				if (err != "done") {
					throw (err);
				}
			}
		}
		j++;
		p = p.nextSibling;
	}
}

function RepRule2(i, j) {
	try {
		RepRule2real(i, j);
	}
	catch(err) {
		alert(err);
	}
}

function RepRule2real(i, j) {
	var seq = pfstate.subgoals[pfstate.branch];
	var rrd = repRuleData;
	var rr = null;
	try {
		for (r in rrd) {
			if ((rrd[r].i == i) && (rrd[r].j == j)) {
				rr = rrd[r];
				throw ("found");
			}
		}
		throw ("Sorry! A bug was encountered. (RepRule2)");
	}
	catch(err) {
		if (err != "found") {
			throw (err);
		}
	}
	cleartop();
	// optionnum, opttrm, and selectbutton are globals
	optionnum = 0;
	opttrm = RepRuleOptTrm(rr, seq[j].prop); // trm with options -- adds a kind 'optiontrm' where an option term has a property 'id':int and a property 'options':Array of terms of the same tp
	var p0 = top.headerFrame.window.document.createElement('P');
	var p = top.headerFrame.window.document.createElement('P');
	p0.appendChild(top.headerFrame.window.document.createTextNode('Choose the subterms to replace and then click here: '));
	p0.appendChild(selectbutton);
	trmopt_sel(p, opttrm); // create an html version with select's for options
	io.inputtop.appendChild(p0);
	io.inputtop.appendChild(p);
}

function RepRule2Closure(i, j) {
	return function() {
		currstep = {
			dom: branchPres(),
			rule: {
				name: "rep",
				princ1: i,
				princ2: j,
				trm: null
			},
			codl: new Array()
		};
		RepRule2(i, j);
	};
}

function RepRule3() {
	try {
		RepRule3real();
	}
	catch(err) {
		alert(err);
		return;
	}
}

function RepRule3real() {
	var i = 0;
	var sel;
	var a = new Array();
	while (i < optionnum) {
		sel = top.headerFrame.window.document.getElementById('select' + i);
		if (sel) {
			a[i] = sel.selectedIndex;
		} else {
			throw ('Sorry!  There is a bug. (RepRule3)');
		}
		i++;
	}
	var trm = extractTrmFromOptTrm(opttrm, a);
	currstep.rule.trm = trm;
	extendBranchWithProp(trm);
	allsteps.push(currstep);
}

// extracts with no beta normalization
function extractTrmFromOptTrm(m, a) {
	if (m.kind == optiontrm) {
		var i = a[m.id];
		if (m.trmarray[i]) {
			return m.trmarray[i];
		} else { // default to 0
			return m.trmarray[0];
		}
	} else if (m.kind == apptrm) {
		var m1 = extractTrmFromOptTrm(m.func, a);
		var m2 = extractTrmFromOptTrm(m.arg, a);
		if ((m1 == m.func) && (m2 == m.arg)) {
			return m;
		} else {
			return app(m1, m2);
		}
	} else if (m.kind == lamtrm) {
		var m1 = extractTrmFromOptTrm(m.body, a);
		if (m1 == m.body) {
			return m;
		} else {
			return lam(m.varname, m.dom, m1);
		}
	} else {
		return m;
	}
}

function RepRuleOptTrm(rr, m) {
	var m1 = null;
	var m2 = null;
	if (eq_tps(rr.lft.tp, m.tp)) {
		if (rr.dir != 2) { // try matching l to m
			try {
				var theta = fo_matcher(new Array({
					lft: rr.lft,
					rght: m,
					ab: null
				}), rr.evars);
				m2 = simul_subst(rr.rght, theta);
			}
			catch(err) {
				if (err != "failure") {
					throw (err);
				}
			}
		}
		if (rr.dir != 1) { // try matching r to m
			try {
				var theta = fo_matcher(new Array({
					lft: rr.rght,
					rght: m,
					ab: null
				}), rr.evars);
				m1 = simul_subst(rr.lft, theta);
			}
			catch(err) {
				if (err != "failure") {
					throw (err);
				}
			}
		}
	}
	var ma = null;
	if ((m1 != null) || (m2 != null)) {
		ma = new Array();
		RepRuleOptSubTrms(rr, m, ma); // do this
		if (m1 != null) {
			pushIfNew(ma, m1);
		}
		if (m2 != null) {
			pushIfNew(ma, m2);
		}
		// add replaced subterms of m as further options:
	}
	if ((ma != null) && (ma.length > 1)) {
		var r = new ooption(optionnum, ma.reverse());
		optionnum++;
		return r;
	} else if (m.kind == apptrm) {
		m1 = RepRuleOptTrm(rr, m.func);
		m2 = RepRuleOptTrm(rr, m.arg);
		if ((m1 == m.func) && (m2 == m.arg)) {
			return m;
		} else {
			return app(m1, m2);
		}
	} else if ((m.kind == lamtrm) && (xiext)) { // only allow rewriting beneath binders if xi is allowed
		if (rr.frees[m.varname]) {
			return m;
		} else {
			m1 = RepRuleOptTrm(rr, m.body);
			if (m1 == m.body) {
				return m;
			} else {
				return lam(m.varname, m.dom, m1);
			}
		}
	} else {
		return m;
	}
}

function RepRuleOptSubTrms(rr, m, a) {
	if (m.kind == apptrm) {
		var a1 = new Array();
		var a2 = new Array();
		RepRuleOptSubTrms2(rr, m.func, a1);
		RepRuleOptSubTrms2(rr, m.arg, a2);
		for (i in a1) {
			for (j in a2) {
				a.push(app(a1[i], a2[j]));
			}
		}
	} else if (m.kind == lamtrm) {
		var a1 = new Array();
		RepRuleOptSubTrms2(rr, m.body, a1);
		for (i in a1) {
			a.push(lam(m.varname, m.dom, a1[i]));
		}
	} else {
		a.push(m);
	}
}

function RepRuleOptSubTrms2(rr, m, a) {
	if (eq_tps(rr.lft.tp, m.tp)) {
		if (rr.dir != 2) { // try matching l to m
			try {
				var theta = fo_matcher(new Array({
					lft: rr.lft,
					rght: m,
					ab: null
				}), rr.evars);
				pushIfNew(a, simul_subst(rr.rght, theta));
			}
			catch(err) {
				if (err != "failure") {
					throw (err);
				}
			}
		}
		if (rr.dir != 1) { // try matching r to m
			try {
				var theta = fo_matcher(new Array({
					lft: rr.rght,
					rght: m,
					ab: null
				}), rr.evars);
				pushIfNew(a, simul_subst(rr.lft, theta));
			}
			catch(err) {
				if (err != "failure") {
					throw (err);
				}
			}
		}
	}
	RepRuleOptSubTrms(rr, m, a);
}

function pushIfNew(a, m) {
	var n = true;
	var i = 0;
	var l = a.length;
	while (n && (i < l)) {
		if (eq_trms(a[i], m)) {
			n = false;
		}
		i++;
	}
	if (n) {
		a.push(m);
	}
}

function DeltaRule(i) {
	var seq = pfstate.subgoals[pfstate.branch];
	cleartop();
	// optionnum, opttrm, and selectdefbutton are globals
	optionnum = 0;
	opttrm = DeltaRuleOptTrm(seq[i].prop); // trm with options, though the option is not the defn expansion but a fake variable named 'Expand <DefnName>'
	var p0 = top.headerFrame.window.document.createElement('P');
	var p = top.headerFrame.window.document.createElement('P');
	p0.appendChild(top.headerFrame.window.document.createTextNode('Choose the definitions to expand and then click here: '));
	p0.appendChild(selectdefbutton);
	trmopt_sel(p, opttrm); // create an html version with select's for options
	io.inputtop.appendChild(p0);
	io.inputtop.appendChild(p);
	currstep = {
		dom: branchPres(),
		rule: {
			name: "delta",
			princ: i,
			trm: null
		},
		codl: new Array()
	};
}

function DeltaRule2() {
	try {
		DeltaRule2real();
	}
	catch(err) {
		alert(err);
		return;
	}
}

function DeltaRule2real() {
	var i = 0;
	var sel;
	var a = new Array();
	while (i < optionnum) {
		sel = top.headerFrame.window.document.getElementById('select' + i);
		if (sel) {
			a[i] = sel.selectedIndex;
		} else {
			throw ('Sorry!  There is a bug.  (DeltaRule2)');
		}
		i++;
	}
	var trm = extractDeltaTrmFromOptTrm(opttrm, a);
	currstep.rule.trm = trm;
	extendBranchWithProp(trm);
	allsteps.push(currstep);
}

function DeltaRuleOptTrm(m) {
	var m1 = null;
	var m2 = null;
	if (m.kind == deftrm) {
		var r = new ooption(optionnum, new Array(m, lvar('Expand ' + m.name, m.tp))); // bit of a hack, the space in the name of the fake variable ensures it won't conflict with an actual variable name
		optionnum++;
		return r;
	} else if (m.kind == apptrm) {
		m1 = DeltaRuleOptTrm(m.func);
		m2 = DeltaRuleOptTrm(m.arg);
		if ((m1 == m.func) && (m2 == m.arg)) {
			return m;
		} else {
			return app(m1, m2);
		}
	} else if (m.kind == lamtrm) {
		m1 = DeltaRuleOptTrm(m.body);
		if (m1 == m.body) {
			return m;
		} else {
			return lam(m.varname, m.dom, m1);
		}
	} else {
		return m;
	}
}

function extractDeltaTrmFromOptTrm(m, a) {
	try {
		return extractDeltaTrmFromOptTrm_real(m, a);
	}
	catch(err) {
		alert(err);
	}
}

// extracts with chosen expansion of abbreviations and some beta reduction
// assume each option has only two options: don't expand or do expand
function extractDeltaTrmFromOptTrm_real(m, a) {
	if (m.kind == optiontrm) {
		var i = a[m.id];
		if (i == 1) {
			var m0 = m.trmarray[0];
			if (m0.kind == deftrm) {
				var m1 = m0.trm;
				m1.reduce = true;
				return m1;
			} else {
				throw ('Something went wrong expanding a definition.  This is a bug.  (extractDeltaTrmFromOptTrm)');
			}
		} else { // default to 0
			return m.trmarray[0];
		}
	} else if (m.kind == apptrm) {
		var m1 = extractDeltaTrmFromOptTrm_real(m.func, a);
		var m2 = extractDeltaTrmFromOptTrm_real(m.arg, a);
		if ((m1 == m.func) && (m2 == m.arg)) {
			return m;
		} else {
			if ((m1.kind == lamtrm) && (m1.reduce)) {
				var m3 = subst(m1.body, m1.varname, m2);
				m3.reduce = true;
				return m3;
			} else {
				return app(m1, m2);
			}
		}
	} else if (m.kind == lamtrm) {
		var m1 = extractDeltaTrmFromOptTrm_real(m.body, a);
		if (m1 == m.body) {
			return m;
		} else {
			var m2 = lam(m.varname, m.dom, m1);
			if (m1.reduce) {
				m2.reduce = true;
			}
			return m2;
		}
	} else {
		return m;
	}
}

// dpairs is an Array of dpairs, where a dpair is an object with lft, rght, and ab
// evars is an Array of existential variables, where an existential variable is an object with a name and a tp
// return true if there is a legal instantiation for the evars (not in conflict with each ab local context)
//                 making each lft = to the right (not up to beta, so it really is first-order)
// and false otherwise
// Note: if x is an evar and <x,x> is a dpair (where x is not on the left or right of ab of dpair),
// then the left x is considered an evar and the right x is considered an ordinary var -- 'x' will be the value of the evar 'x'.
// This is because we are matching and not unifying.
// fo_matches returns a bool
// fo_matcher returns a simul_subst or throws "failure"
function fo_matches(dpairs, evars) {
	try {
		dpairs = fo_match_simplify(dpairs, evars);
		// if conflict, return false
		// now make sure each evar got at most one value:
		for (e in evars) {
			var x = evars[e].name;
			var xval = null;
			for (d in dpairs) {
				if (dpairs[d].lft.name == x) {
					if (xval == null) {
						xval = dpairs[d].rght;
					} else if (! (eq_trms(xval, dpairs[d].rght))) {
						throw ("conflict");
					}
				}
			}
		}
		return true;
	}
	catch(err) {
		if (err == "conflict") {
			return false;
		} else {
			throw (err);
		}
	}
}

function fo_matcher(dpairs, evars) {
	try {
		dpairs = fo_match_simplify(dpairs, evars);
		// if conflict, return false
		// now make sure each evar got at most one value and build simul subst
		var theta = new Object();
		for (e in evars) {
			var x = evars[e].name;
			var xval = null;
			for (d in dpairs) {
				if (dpairs[d].lft.name == x) {
					if (xval == null) {
						xval = dpairs[d].rght;
						theta[x] = xval;
					} else if (! (eq_trms(xval, dpairs[d].rght))) {
						throw ("conflict");
					}
				}
			}
		}
		return theta;
	}
	catch(err) {
		if (err == "conflict") {
			throw ("failure");
		} else {
			throw (err);
		}
	}
}

// simplify dpairs until all of them have an evar on left or get a problem (kinds/types do not match)
// upon conflict, throw "conflict"
// destructively modifies dpairs until they are all of the form { lft: <evar>, rght: <trm>[no evars], ab: ... }
function fo_match_simplify(dpairs, evars) {
	var ret = new Array();
	//    botmsg('entering fo_match_simplify');    dpairs_debug(dpairs);  // delete me
	while (dpairs.length > 0) {
		var d = dpairs.pop();
		var l = d.lft;
		var r = d.rght;
		var ab = d.ab;
		//	botmsg('looping fo_match_simplify');    dpairs_debug(dpairs);  // delete me
		if (l.kind == vartrm) {
			// first check if l is a of ab and if so, if r is the corresponding b
			try {
				if (r.kind == vartrm) {
					for (xy in ab) {
						if (xy.a == l.name) {
							if (xy.b == r.name) {
								throw ("ok");
							} else {
								throw ("conflict");
							}
						} else if (xy.b == r.name) {
							throw ("conflict");
						}
					}
				} else {
					for (xy in ab) {
						if (xy.a == l.name) {
							throw ("conflict");
						}
					}
				}
				// Check if left hand side is an evar and if so, if right hand side is a valid instantiation for the evar
				for (e in evars) {
					if (l.name == evars[e].name) {
						// check if b parts of b are in (value of evar cannot depend on locally bound vars)
						for (xy in ab) {
							if (free_in(xy.b, r)) {
								throw ("conflict");
							}
						}
						ret.push({
							lft: l,
							rght: r,
							ab: ab
						});
						throw ("ok");
					}
				}
				// Finally, check if the variables are just equal
				if ((r.kind != vartrm) || (l.name != r.name)) {
					throw ("conflict");
				}
			}
			catch(err) {
				if (err != "ok") {
					throw (err);
				}
			}
		} else if (l.kind == r.kind) {
			if (l.kind == apptrm) {
				if (eq_tps(l.func.tp, r.func.tp)) {
					dpairs.push({
						lft: l.func,
						rght: r.func,
						ab: ab
					});
					dpairs.push({
						lft: l.arg,
						rght: r.arg,
						ab: ab
					});
				} else {
					throw ("conflict");
				}
			} else if (l.kind == lamtrm) {
				if (eq_tps(l.tp, r.tp)) {
					dpairs.push({
						lft: l.body,
						rght: r.body,
						ab: alpha_cons(l.varname, r.varname, ab)
					});
				} else {
					throw ("conflict");
				}
			} else if (l.name != r.name) {
				throw ("conflict");
			}
		} else {
			throw ("conflict");
		}
	}
	//    botmsg('exiting fo_match_simplify'); dpairs_debug(ret);  // delete me
	return ret;
}

function dpairs_debug(dpairs) {
	botmsg('*** dpairs ***');
	for (d in dpairs) {
		botmsg('*dpair* <' + trm_str(dpairs[d].lft) + ',' + trm_str(dpairs[d].rght) + '> ' + dpairs[d].ab);
	}
}

function mynot(m) {
	if (not_p(m)) {
		return m.arg;
	} else {
		return not(m);
	}
}

function eagerdelete_weaken(i, codl) {
	var b = pfstate.branch;
	var pftreeop = pftreeops[numsteps];
	for (j in codl) {
		weaken(i);
		pfstate.branch++;
	}
	pfstate.branch = b;
	pftreeops[numsteps] = pftreeop;
}
