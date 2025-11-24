% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A20515.mg.html#A20515
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > $i))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : ($i > $i))).
thf(c_H1_tp,type,(c_H1 : $i)).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > $i))).
thf(c_G2_tp,type,(c_G2 : $i)).
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : ($i > $i))).
thf(c_H3_tp,type,(c_H3 : $i)).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_F0 @ X22)) @ int)))).
thf(c_HG0,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_G0 @ X22)) @ int)))).
thf(c_HF1,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_F1 @ X22)) @ int)))).
thf(c_HG1,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_G1 @ X22)) @ int)))).
thf(c_HH1,axiom,((c_In @ c_H1) @ int)).
thf(c_HU1,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => ((c_In @ ((c_U1 @ X22) @ X23)) @ int)))))).
thf(c_HV1,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_V1 @ X22)) @ int)))).
thf(c_HH0,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_H0 @ X22)) @ int)))).
thf(c_HU0,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => ((c_In @ ((c_U0 @ X22) @ X23)) @ int)))))).
thf(c_HV0,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_V0 @ X22)) @ int)))).
thf(c_HSMALL,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_SMALL @ X22)) @ int)))).
thf(c_HF2,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_F2 @ X22)) @ int)))).
thf(c_HG2,axiom,((c_In @ c_G2) @ int)).
thf(c_HF3,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_F3 @ X22)) @ int)))).
thf(c_HG3,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_G3 @ X22)) @ int)))).
thf(c_HH3,axiom,((c_In @ c_H3) @ int)).
thf(c_HU3,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => ((c_In @ ((c_U3 @ X22) @ X23)) @ int)))))).
thf(c_HV3,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_V3 @ X22)) @ int)))).
thf(c_HH2,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_H2 @ X22)) @ int)))).
thf(c_HU2,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => ((c_In @ ((c_U2 @ X22) @ X23)) @ int)))))).
thf(c_HV2,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_V2 @ X22)) @ int)))).
thf(c_HFAST,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (c_FAST @ X22)) @ int)))).
thf(c_H1,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_F0 @ X22) = ((add_5FSNo @ ((add_5FSNo @ X22) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X22))))).
thf(c_H2,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_G0 @ X22) = X22)))).
thf(c_H3,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_F1 @ X22) = ((add_5FSNo @ X22) @ X22))))).
thf(c_H4,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_G1 @ X22) = X22)))).
thf(c_H5,axiom,(c_H1 = (ordsucc @ c_Empty))).
thf(c_H6,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => (((c_U1 @ X22) @ X23) = (((c_If_5Fi @ ((c_SNoLe @ X22) @ c_Empty)) @ X23) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X22) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X23))))))))).
thf(c_H7,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_V1 @ X22) = ((c_U1 @ (c_G1 @ X22)) @ c_H1))))).
thf(c_H8,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_H0 @ X22) = (c_V1 @ X22))))).
thf(c_H9,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => (((c_U0 @ X22) @ X23) = (((c_If_5Fi @ ((c_SNoLe @ X22) @ c_Empty)) @ X23) @ (c_F0 @ ((c_U0 @ ((add_5FSNo @ X22) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X23))))))))).
thf(c_H10,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_V0 @ X22) = ((c_U0 @ (c_G0 @ X22)) @ (c_H0 @ X22)))))).
thf(c_H11,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_SMALL @ X22) = (c_V0 @ X22))))).
thf(c_H12,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_F2 @ X22) = ((add_5FSNo @ ((mul_5FSNo @ X22) @ X22)) @ (minus_5FSNo @ X22)))))).
thf(c_H13,axiom,(c_G2 = (ordsucc @ c_Empty))).
thf(c_H14,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_F3 @ X22) = ((add_5FSNo @ X22) @ X22))))).
thf(c_H15,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_G3 @ X22) = X22)))).
thf(c_H16,axiom,(c_H3 = (ordsucc @ c_Empty))).
thf(c_H17,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => (((c_U3 @ X22) @ X23) = (((c_If_5Fi @ ((c_SNoLe @ X22) @ c_Empty)) @ X23) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X22) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X23))))))))).
thf(c_H18,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_V3 @ X22) = ((c_U3 @ (c_G3 @ X22)) @ c_H3))))).
thf(c_H19,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_H2 @ X22) = (c_V3 @ X22))))).
thf(c_H20,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => (! [X23:$i] : (((c_In @ X23) @ int) => (((c_U2 @ X22) @ X23) = (((c_If_5Fi @ ((c_SNoLe @ X22) @ c_Empty)) @ X23) @ (c_F2 @ ((c_U2 @ ((add_5FSNo @ X22) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X23))))))))).
thf(c_H21,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_V2 @ X22) = ((c_U2 @ c_G2) @ (c_H2 @ X22)))))).
thf(c_H22,axiom,(! [X22:$i] : (((c_In @ X22) @ int) => ((c_FAST @ X22) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (c_V2 @ X22)))))).
thf(a20515,conjecture,(! [X22:$i] : (((c_In @ X22) @ int) => (((c_SNoLe @ c_Empty) @ X22) => ((c_SMALL @ X22) = (c_FAST @ X22)))))).
