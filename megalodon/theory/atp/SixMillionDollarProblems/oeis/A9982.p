% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A9982.mg.html#A9982
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : $i)).
thf(c_H1_tp,type,(c_H1 : $i)).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : $i)).
thf(c_F0_tp,type,(c_F0 : ($i > $i))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > $i))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > ($i > $i)))).
thf(c_G3_tp,type,(c_G3 : ($i > ($i > $i)))).
thf(c_H3_tp,type,(c_H3 : ($i > $i))).
thf(c_I3_tp,type,(c_I3 : $i)).
thf(c_J3_tp,type,(c_J3 : $i)).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > ($i > $i))))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > ($i > $i))))).
thf(c_W3_tp,type,(c_W3 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF1,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_F1 @ X25)) @ int)))).
thf(c_HG1,axiom,((c_In @ c_G1) @ int)).
thf(c_HH1,axiom,((c_In @ c_H1) @ int)).
thf(c_HU1,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ ((c_U1 @ X25) @ X26)) @ int)))))).
thf(c_HV1,axiom,((c_In @ c_V1) @ int)).
thf(c_HF0,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_F0 @ X25)) @ int)))).
thf(c_HG0,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_G0 @ X25)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ ((c_U0 @ X25) @ X26)) @ int)))))).
thf(c_HV0,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_V0 @ X25)) @ int)))).
thf(c_HSMALL,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_SMALL @ X25)) @ int)))).
thf(c_HF2,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_F2 @ X25)) @ int)))).
thf(c_HG2,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_G2 @ X25)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ ((c_U2 @ X25) @ X26)) @ int)))))).
thf(c_HV2,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_V2 @ X25)) @ int)))).
thf(c_HF3,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ ((c_F3 @ X25) @ X26)) @ int)))))).
thf(c_HG3,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ ((c_G3 @ X25) @ X26)) @ int)))))).
thf(c_HH3,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_H3 @ X25)) @ int)))).
thf(c_HI3,axiom,((c_In @ c_I3) @ int)).
thf(c_HJ3,axiom,((c_In @ c_J3) @ int)).
thf(c_HU3,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((c_In @ (((c_U3 @ X25) @ X26) @ X27)) @ int)))))))).
thf(c_HV3,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((c_In @ (((c_V3 @ X25) @ X26) @ X27)) @ int)))))))).
thf(c_HW3,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_W3 @ X25)) @ int)))).
thf(c_HFAST,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_In @ (c_FAST @ X25)) @ int)))).
thf(c_H1,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_F1 @ X25) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ X25) @ X25)))))).
thf(c_H2,axiom,(c_G1 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H3,axiom,(c_H1 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H4,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (((c_U1 @ X25) @ X26) = (((c_If_5Fi @ ((c_SNoLe @ X25) @ c_Empty)) @ X26) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X25) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X26))))))))).
thf(c_H5,axiom,(c_V1 = ((c_U1 @ c_G1) @ c_H1))).
thf(c_H6,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_F0 @ X25) = ((mul_5FSNo @ c_V1) @ X25))))).
thf(c_H7,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_G0 @ X25) = X25)))).
thf(c_H8,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H9,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (((c_U0 @ X25) @ X26) = (((c_If_5Fi @ ((c_SNoLe @ X25) @ c_Empty)) @ X26) @ (c_F0 @ ((c_U0 @ ((add_5FSNo @ X25) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X26))))))))).
thf(c_H10,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_V0 @ X25) = ((c_U0 @ (c_G0 @ X25)) @ c_H0))))).
thf(c_H11,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_SMALL @ X25) = (c_V0 @ X25))))).
thf(c_H12,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_F2 @ X25) = ((add_5FSNo @ X25) @ X25))))).
thf(c_H13,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_G2 @ X25) = X25)))).
thf(c_H14,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H15,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (((c_U2 @ X25) @ X26) = (((c_If_5Fi @ ((c_SNoLe @ X25) @ c_Empty)) @ X26) @ (c_F2 @ ((c_U2 @ ((add_5FSNo @ X25) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X26))))))))).
thf(c_H16,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_V2 @ X25) = ((c_U2 @ (c_G2 @ X25)) @ c_H2))))).
thf(c_H17,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (((c_F3 @ X25) @ X26) = ((mul_5FSNo @ X25) @ X26))))))).
thf(c_H18,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (((c_G3 @ X25) @ X26) = X26)))))).
thf(c_H19,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_H3 @ X25) = X25)))).
thf(c_H20,axiom,(c_I3 = (ordsucc @ c_Empty))).
thf(c_H21,axiom,(c_J3 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty))))))))).
thf(c_H22,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((((c_U3 @ X25) @ X26) @ X27) = (((c_If_5Fi @ ((c_SNoLe @ X25) @ c_Empty)) @ X26) @ ((c_F3 @ (((c_U3 @ ((add_5FSNo @ X25) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X26) @ X27)) @ (((c_V3 @ ((add_5FSNo @ X25) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X26) @ X27))))))))))).
thf(c_H23,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => (! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((((c_V3 @ X25) @ X26) @ X27) = (((c_If_5Fi @ ((c_SNoLe @ X25) @ c_Empty)) @ X27) @ ((c_G3 @ (((c_U3 @ ((add_5FSNo @ X25) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X26) @ X27)) @ (((c_V3 @ ((add_5FSNo @ X25) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X26) @ X27))))))))))).
thf(c_H24,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_W3 @ X25) = (((c_U3 @ (c_H3 @ X25)) @ c_I3) @ c_J3))))).
thf(c_H25,axiom,(! [X25:$i] : (((c_In @ X25) @ int) => ((c_FAST @ X25) = ((mul_5FSNo @ (c_V2 @ X25)) @ (c_W3 @ X25)))))).
thf(a9982,conjecture,(! [X25:$i] : (((c_In @ X25) @ int) => (((c_SNoLe @ c_Empty) @ X25) => ((c_SMALL @ X25) = (c_FAST @ X25)))))).
