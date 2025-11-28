% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A33595.mg.html#A33595
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => (! [X8:$i] : (((c_In @ X8) @ int) => ((c_In @ ((c_F0 @ X7) @ X8)) @ int)))))).
thf(c_HG0,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_In @ (c_G0 @ X7)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => (! [X8:$i] : (((c_In @ X8) @ int) => ((c_In @ ((c_U0 @ X7) @ X8)) @ int)))))).
thf(c_HV0,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_In @ (c_V0 @ X7)) @ int)))).
thf(c_HSMALL,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_In @ (c_SMALL @ X7)) @ int)))).
thf(c_HFAST,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_In @ (c_FAST @ X7)) @ int)))).
thf(c_H1,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => (! [X8:$i] : (((c_In @ X8) @ int) => (((c_F0 @ X7) @ X8) = ((add_5FSNo @ ((add_5FSNo @ X7) @ (minus_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))))) @ X8))))))).
thf(c_H2,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_G0 @ X7) = ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ X7) @ X7)))))).
thf(c_H3,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H4,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => (! [X8:$i] : (((c_In @ X8) @ int) => (((c_U0 @ X7) @ X8) = (((c_If_5Fi @ ((c_SNoLe @ X7) @ c_Empty)) @ X8) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X7) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X8)) @ X7)))))))).
thf(c_H5,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_V0 @ X7) = ((c_U0 @ (c_G0 @ X7)) @ c_H0))))).
thf(c_H6,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_SMALL @ X7) = (c_V0 @ X7))))).
thf(c_H7,axiom,(! [X7:$i] : (((c_In @ X7) @ int) => ((c_FAST @ X7) = ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ c_Empty)) @ (minus_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ X7) @ X7))))) @ ((add_5FSNo @ (ordsucc @ c_Empty)) @ (minus_5FSNo @ ((mul_5FSNo @ X7) @ X7)))))))).
thf(a33595,conjecture,(! [X7:$i] : (((c_In @ X7) @ int) => (((c_SNoLe @ c_Empty) @ X7) => ((c_SMALL @ X7) = (c_FAST @ X7)))))).
