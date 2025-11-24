% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A6625.mg.html#A6625
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > $i))).
thf(c_H1_tp,type,(c_H1 : ($i > $i))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => ((c_In @ ((c_F0 @ X12) @ X13)) @ int)))))).
thf(c_HG0,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_G0 @ X12)) @ int)))).
thf(c_HH0,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_H0 @ X12)) @ int)))).
thf(c_HU0,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => ((c_In @ ((c_U0 @ X12) @ X13)) @ int)))))).
thf(c_HV0,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_V0 @ X12)) @ int)))).
thf(c_HSMALL,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_SMALL @ X12)) @ int)))).
thf(c_HF1,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => ((c_In @ ((c_F1 @ X12) @ X13)) @ int)))))).
thf(c_HG1,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_G1 @ X12)) @ int)))).
thf(c_HH1,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_H1 @ X12)) @ int)))).
thf(c_HU1,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => ((c_In @ ((c_U1 @ X12) @ X13)) @ int)))))).
thf(c_HV1,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_V1 @ X12)) @ int)))).
thf(c_HFAST,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (c_FAST @ X12)) @ int)))).
thf(c_H1,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => (((c_F0 @ X12) @ X13) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ X12) @ X13)))))))).
thf(c_H2,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_G0 @ X12) = ((add_5FSNo @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X12)) @ (ordsucc @ (ordsucc @ c_Empty))))))).
thf(c_H3,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_H0 @ X12) = (((c_If_5Fi @ ((c_SNoLe @ X12) @ c_Empty)) @ c_Empty) @ (ordsucc @ c_Empty)))))).
thf(c_H4,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => (((c_U0 @ X12) @ X13) = (((c_If_5Fi @ ((c_SNoLe @ X12) @ c_Empty)) @ X13) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X12) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X13)) @ X12)))))))).
thf(c_H5,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_V0 @ X12) = ((c_U0 @ (c_G0 @ X12)) @ (c_H0 @ X12)))))).
thf(c_H6,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_SMALL @ X12) = (c_V0 @ X12))))).
thf(c_H7,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => (((c_F1 @ X12) @ X13) = ((add_5FSNo @ X12) @ X13))))))).
thf(c_H8,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_G1 @ X12) = ((add_5FSNo @ X12) @ (minus_5FSNo @ (ordsucc @ (ordsucc @ c_Empty)))))))).
thf(c_H9,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_H1 @ X12) = ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X12)) @ ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))))))).
thf(c_H10,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => (! [X13:$i] : (((c_In @ X13) @ int) => (((c_U1 @ X12) @ X13) = (((c_If_5Fi @ ((c_SNoLe @ X12) @ c_Empty)) @ X13) @ ((c_F1 @ ((c_U1 @ ((add_5FSNo @ X12) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X13)) @ X12)))))))).
thf(c_H11,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_V1 @ X12) = ((c_U1 @ (c_G1 @ X12)) @ (c_H1 @ X12)))))).
thf(c_H12,axiom,(! [X12:$i] : (((c_In @ X12) @ int) => ((c_FAST @ X12) = (c_V1 @ X12))))).
thf(a6625,conjecture,(! [X12:$i] : (((c_In @ X12) @ int) => (((c_SNoLe @ c_Empty) @ X12) => ((c_SMALL @ X12) = (c_FAST @ X12)))))).
