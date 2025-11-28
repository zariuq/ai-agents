% https://mgwiki.github.io/mgw_test/conj/fermat/FLT1.mg.html#FermatsLastTheorem
% Bounty in April 2025: 130 pfg bars ($10400)
include('fltheader.ax').
thf(conj_flt3,conjecture,(! [X0:$i] : (((c_In @ X0) @ int) => (! [X1:$i] : (((c_In @ X1) @ int) => (! [X2:$i] : (((c_In @ X2) @ int) => ((((add_5FSNo @ ((exp_5FSNo_5Fnat @ X0) @ (ordsucc @ (ordsucc @ (ordsucc @ c_Empty))))) @ ((exp_5FSNo_5Fnat @ X1) @ (ordsucc @ (ordsucc @ (ordsucc @ c_Empty))))) = ((exp_5FSNo_5Fnat @ X2) @ (ordsucc @ (ordsucc @ (ordsucc @ c_Empty))))) => (((X0 = c_Empty) | (X1 = c_Empty)) | (X2 = c_Empty)))))))))).
