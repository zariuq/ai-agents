% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A102714.mg.html#A102714
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > $i))).
thf(c_H1_tp,type,(c_H1 : ($i > ($i > $i)))).
thf(c_I1_tp,type,(c_I1 : $i)).
thf(c_J1_tp,type,(c_J1 : $i)).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > ($i > $i))))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > ($i > $i))))).
thf(c_W1_tp,type,(c_W1 : ($i > ($i > $i)))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_I2_tp,type,(c_I2 : $i)).
thf(c_J2_tp,type,(c_J2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > ($i > $i))))).
thf(c_V2_tp,type,(c_V2 : ($i > ($i > ($i > $i))))).
thf(c_W2_tp,type,(c_W2 : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > ($i > $i)))).
thf(c_G3_tp,type,(c_G3 : ($i > $i))).
thf(c_H3_tp,type,(c_H3 : ($i > $i))).
thf(c_I3_tp,type,(c_I3 : $i)).
thf(c_J3_tp,type,(c_J3 : $i)).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > ($i > $i))))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > ($i > $i))))).
thf(c_W3_tp,type,(c_W3 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF1,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ ((c_F1 @ X31) @ X32)) @ int)))))).
thf(c_HG1,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_G1 @ X31)) @ int)))).
thf(c_HH1,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ ((c_H1 @ X31) @ X32)) @ int)))))).
thf(c_HI1,axiom,((c_In @ c_I1) @ int)).
thf(c_HJ1,axiom,((c_In @ c_J1) @ int)).
thf(c_HU1,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((c_In @ (((c_U1 @ X31) @ X32) @ X33)) @ int)))))))).
thf(c_HV1,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((c_In @ (((c_V1 @ X31) @ X32) @ X33)) @ int)))))))).
thf(c_HW1,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ ((c_W1 @ X31) @ X32)) @ int)))))).
thf(c_HF0,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ ((c_F0 @ X31) @ X32)) @ int)))))).
thf(c_HG0,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_G0 @ X31)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ ((c_U0 @ X31) @ X32)) @ int)))))).
thf(c_HV0,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_V0 @ X31)) @ int)))).
thf(c_HSMALL,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_SMALL @ X31)) @ int)))).
thf(c_HF2,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ ((c_F2 @ X31) @ X32)) @ int)))))).
thf(c_HG2,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_G2 @ X31)) @ int)))).
thf(c_HH2,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_H2 @ X31)) @ int)))).
thf(c_HI2,axiom,((c_In @ c_I2) @ int)).
thf(c_HJ2,axiom,((c_In @ c_J2) @ int)).
thf(c_HU2,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((c_In @ (((c_U2 @ X31) @ X32) @ X33)) @ int)))))))).
thf(c_HV2,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((c_In @ (((c_V2 @ X31) @ X32) @ X33)) @ int)))))))).
thf(c_HW2,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_W2 @ X31)) @ int)))).
thf(c_HF3,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ ((c_F3 @ X31) @ X32)) @ int)))))).
thf(c_HG3,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_G3 @ X31)) @ int)))).
thf(c_HH3,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_H3 @ X31)) @ int)))).
thf(c_HI3,axiom,((c_In @ c_I3) @ int)).
thf(c_HJ3,axiom,((c_In @ c_J3) @ int)).
thf(c_HU3,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((c_In @ (((c_U3 @ X31) @ X32) @ X33)) @ int)))))))).
thf(c_HV3,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((c_In @ (((c_V3 @ X31) @ X32) @ X33)) @ int)))))))).
thf(c_HW3,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_W3 @ X31)) @ int)))).
thf(c_HFAST,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ (c_FAST @ X31)) @ int)))).
thf(c_H1,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (((c_F1 @ X31) @ X32) = ((add_5FSNo @ X31) @ X32))))))).
thf(c_H2,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_G1 @ X31) = X31)))).
thf(c_H3,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (((c_H1 @ X31) @ X32) = ((add_5FSNo @ X32) @ X32))))))).
thf(c_H4,axiom,(c_I1 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H5,axiom,(c_J1 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (ordsucc @ (ordsucc @ c_Empty))))).
thf(c_H6,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((((c_U1 @ X31) @ X32) @ X33) = (((c_If_5Fi @ ((c_SNoLe @ X31) @ c_Empty)) @ X32) @ ((c_F1 @ (((c_U1 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33)) @ (((c_V1 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33))))))))))).
thf(c_H7,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((((c_V1 @ X31) @ X32) @ X33) = (((c_If_5Fi @ ((c_SNoLe @ X31) @ c_Empty)) @ X33) @ (c_G1 @ (((c_U1 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33))))))))))).
thf(c_H8,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (((c_W1 @ X31) @ X32) = (((c_U1 @ ((c_H1 @ X31) @ X32)) @ c_I1) @ c_J1))))))).
thf(c_H9,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (((c_F0 @ X31) @ X32) = ((add_5FSNo @ ((c_W1 @ X31) @ X32)) @ (minus_5FSNo @ X31)))))))).
thf(c_H10,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_G0 @ X31) = X31)))).
thf(c_H11,axiom,(c_H0 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H12,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (((c_U0 @ X31) @ X32) = (((c_If_5Fi @ ((c_SNoLe @ X31) @ c_Empty)) @ X32) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32)) @ X31)))))))).
thf(c_H13,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_V0 @ X31) = ((c_U0 @ (c_G0 @ X31)) @ c_H0))))).
thf(c_H14,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_SMALL @ X31) = (c_V0 @ X31))))).
thf(c_H15,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (((c_F2 @ X31) @ X32) = ((add_5FSNo @ X31) @ X32))))))).
thf(c_H16,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_G2 @ X31) = X31)))).
thf(c_H17,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_H2 @ X31) = ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty))))))).
thf(c_H18,axiom,(c_I2 = (ordsucc @ c_Empty))).
thf(c_H19,axiom,(c_J2 = (ordsucc @ c_Empty))).
thf(c_H20,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((((c_U2 @ X31) @ X32) @ X33) = (((c_If_5Fi @ ((c_SNoLe @ X31) @ c_Empty)) @ X32) @ ((c_F2 @ (((c_U2 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33)) @ (((c_V2 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33))))))))))).
thf(c_H21,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((((c_V2 @ X31) @ X32) @ X33) = (((c_If_5Fi @ ((c_SNoLe @ X31) @ c_Empty)) @ X33) @ (c_G2 @ (((c_U2 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33))))))))))).
thf(c_H22,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_W2 @ X31) = (((c_U2 @ (c_H2 @ X31)) @ c_I2) @ c_J2))))).
thf(c_H23,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (((c_F3 @ X31) @ X32) = ((add_5FSNo @ X31) @ X32))))))).
thf(c_H24,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_G3 @ X31) = X31)))).
thf(c_H25,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_H3 @ X31) = X31)))).
thf(c_H26,axiom,(c_I3 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H27,axiom,(c_J3 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (ordsucc @ (ordsucc @ c_Empty))))).
thf(c_H28,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((((c_U3 @ X31) @ X32) @ X33) = (((c_If_5Fi @ ((c_SNoLe @ X31) @ c_Empty)) @ X32) @ ((c_F3 @ (((c_U3 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33)) @ (((c_V3 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33))))))))))).
thf(c_H29,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => (! [X33:$i] : (((c_In @ X33) @ int) => ((((c_V3 @ X31) @ X32) @ X33) = (((c_If_5Fi @ ((c_SNoLe @ X31) @ c_Empty)) @ X33) @ (c_G3 @ (((c_U3 @ ((add_5FSNo @ X31) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X32) @ X33))))))))))).
thf(c_H30,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_W3 @ X31) = (((c_U3 @ (c_H3 @ X31)) @ c_I3) @ c_J3))))).
thf(c_H31,axiom,(! [X31:$i] : (((c_In @ X31) @ int) => ((c_FAST @ X31) = ((mul_5FSNo @ (c_W2 @ X31)) @ (c_W3 @ X31)))))).
thf(a102714,conjecture,(! [X31:$i] : (((c_In @ X31) @ int) => (((c_SNoLe @ c_Empty) @ X31) => ((c_SMALL @ X31) = (c_FAST @ X31)))))).
