% https://mgwiki.github.io/mgw_test/conj/fermat/FLT1.mg.html#FermatsLastTheorem
% Bounty in April 2025: 5000 pfg bars ($400000)
include('fltheader.ax').
thf(conj_flt,conjecture,(! [X0:$i] : (((c_In @ X0) @ int) => (((c_SNoLt @ (ordsucc @ (ordsucc @ c_Empty))) @ X0) => (! [X1:$i] : (((c_In @ X1) @ int) => (! [X2:$i] : (((c_In @ X2) @ int) => (! [X3:$i] : (((c_In @ X3) @ int) => ((((add_5FSNo @ ((exp_5FSNo_5Fnat @ X1) @ X0)) @ ((exp_5FSNo_5Fnat @ X2) @ X0)) = ((exp_5FSNo_5Fnat @ X3) @ X0)) => (((X1 = c_Empty) | (X2 = c_Empty)) | (X3 = c_Empty))))))))))))).
