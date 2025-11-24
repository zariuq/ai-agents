% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A97770.mg.html#A97770
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : $i)).
thf(c_H1_tp,type,(c_H1 : ($i > $i))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > $i))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_I0_tp,type,(c_I0 : $i)).
thf(c_J0_tp,type,(c_J0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > ($i > $i))))).
thf(c_V0_tp,type,(c_V0 : ($i > ($i > ($i > $i))))).
thf(c_W0_tp,type,(c_W0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : $i)).
thf(c_H3_tp,type,(c_H3 : $i)).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : $i)).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_I2_tp,type,(c_I2 : $i)).
thf(c_J2_tp,type,(c_J2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > ($i > $i))))).
thf(c_V2_tp,type,(c_V2 : ($i > ($i > ($i > $i))))).
thf(c_W2_tp,type,(c_W2 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF1,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => ((c_In @ ((c_F1 @ X28) @ X29)) @ int)))))).
thf(c_HG1,axiom,((c_In @ c_G1) @ int)).
thf(c_HH1,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_H1 @ X28)) @ int)))).
thf(c_HU1,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => ((c_In @ ((c_U1 @ X28) @ X29)) @ int)))))).
thf(c_HV1,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_V1 @ X28)) @ int)))).
thf(c_HF0,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => ((c_In @ ((c_F0 @ X28) @ X29)) @ int)))))).
thf(c_HG0,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_G0 @ X28)) @ int)))).
thf(c_HH0,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_H0 @ X28)) @ int)))).
thf(c_HI0,axiom,((c_In @ c_I0) @ int)).
thf(c_HJ0,axiom,((c_In @ c_J0) @ int)).
thf(c_HU0,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (((c_U0 @ X28) @ X29) @ X30)) @ int)))))))).
thf(c_HV0,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (((c_V0 @ X28) @ X29) @ X30)) @ int)))))))).
thf(c_HW0,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_W0 @ X28)) @ int)))).
thf(c_HSMALL,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_SMALL @ X28)) @ int)))).
thf(c_HF3,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_F3 @ X28)) @ int)))).
thf(c_HG3,axiom,((c_In @ c_G3) @ int)).
thf(c_HH3,axiom,((c_In @ c_H3) @ int)).
thf(c_HU3,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => ((c_In @ ((c_U3 @ X28) @ X29)) @ int)))))).
thf(c_HV3,axiom,((c_In @ c_V3) @ int)).
thf(c_HF2,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => ((c_In @ ((c_F2 @ X28) @ X29)) @ int)))))).
thf(c_HG2,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_G2 @ X28)) @ int)))).
thf(c_HH2,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_H2 @ X28)) @ int)))).
thf(c_HI2,axiom,((c_In @ c_I2) @ int)).
thf(c_HJ2,axiom,((c_In @ c_J2) @ int)).
thf(c_HU2,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (((c_U2 @ X28) @ X29) @ X30)) @ int)))))))).
thf(c_HV2,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (((c_V2 @ X28) @ X29) @ X30)) @ int)))))))).
thf(c_HW2,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_W2 @ X28)) @ int)))).
thf(c_HFAST,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (c_FAST @ X28)) @ int)))).
thf(c_H1,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (((c_F1 @ X28) @ X29) = ((mul_5FSNo @ X28) @ X29))))))).
thf(c_H2,axiom,(c_G1 = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty))))).
thf(c_H3,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_H1 @ X28) = X28)))).
thf(c_H4,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (((c_U1 @ X28) @ X29) = (((c_If_5Fi @ ((c_SNoLe @ X28) @ c_Empty)) @ X29) @ ((c_F1 @ ((c_U1 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29)) @ X28)))))))).
thf(c_H5,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_V1 @ X28) = ((c_U1 @ c_G1) @ (c_H1 @ X28)))))).
thf(c_H6,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (((c_F0 @ X28) @ X29) = ((add_5FSNo @ (c_V1 @ X28)) @ X29))))))).
thf(c_H7,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_G0 @ X28) = X28)))).
thf(c_H8,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_H0 @ X28) = ((add_5FSNo @ X28) @ X28))))).
thf(c_H9,axiom,(c_I0 = (ordsucc @ c_Empty))).
thf(c_H10,axiom,(c_J0 = c_Empty)).
thf(c_H11,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((((c_U0 @ X28) @ X29) @ X30) = (((c_If_5Fi @ ((c_SNoLe @ X28) @ c_Empty)) @ X29) @ ((c_F0 @ (((c_U0 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29) @ X30)) @ (((c_V0 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29) @ X30))))))))))).
thf(c_H12,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((((c_V0 @ X28) @ X29) @ X30) = (((c_If_5Fi @ ((c_SNoLe @ X28) @ c_Empty)) @ X30) @ (c_G0 @ (((c_U0 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29) @ X30))))))))))).
thf(c_H13,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_W0 @ X28) = (((c_U0 @ (c_H0 @ X28)) @ c_I0) @ c_J0))))).
thf(c_H14,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_SMALL @ X28) = (c_W0 @ X28))))).
thf(c_H15,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_F3 @ X28) = ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ c_Empty)) @ X28)) @ ((mul_5FSNo @ X28) @ X28)))))).
thf(c_H16,axiom,(c_G3 = (ordsucc @ c_Empty))).
thf(c_H17,axiom,(c_H3 = ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))).
thf(c_H18,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (((c_U3 @ X28) @ X29) = (((c_If_5Fi @ ((c_SNoLe @ X28) @ c_Empty)) @ X29) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29))))))))).
thf(c_H19,axiom,(c_V3 = ((c_U3 @ c_G3) @ c_H3))).
thf(c_H20,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (((c_F2 @ X28) @ X29) = ((add_5FSNo @ ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ c_V3)) @ X28)) @ (minus_5FSNo @ X29)))))))).
thf(c_H21,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_G2 @ X28) = X28)))).
thf(c_H22,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_H2 @ X28) = X28)))).
thf(c_H23,axiom,(c_I2 = (ordsucc @ c_Empty))).
thf(c_H24,axiom,(c_J2 = (ordsucc @ c_Empty))).
thf(c_H25,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((((c_U2 @ X28) @ X29) @ X30) = (((c_If_5Fi @ ((c_SNoLe @ X28) @ c_Empty)) @ X29) @ ((c_F2 @ (((c_U2 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29) @ X30)) @ (((c_V2 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29) @ X30))))))))))).
thf(c_H26,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => (! [X29:$i] : (((c_In @ X29) @ int) => (! [X30:$i] : (((c_In @ X30) @ int) => ((((c_V2 @ X28) @ X29) @ X30) = (((c_If_5Fi @ ((c_SNoLe @ X28) @ c_Empty)) @ X30) @ (c_G2 @ (((c_U2 @ ((add_5FSNo @ X28) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X29) @ X30))))))))))).
thf(c_H27,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_W2 @ X28) = (((c_U2 @ (c_H2 @ X28)) @ c_I2) @ c_J2))))).
thf(c_H28,axiom,(! [X28:$i] : (((c_In @ X28) @ int) => ((c_FAST @ X28) = (c_W2 @ X28))))).
thf(a97770,conjecture,(! [X28:$i] : (((c_In @ X28) @ int) => (((c_SNoLe @ c_Empty) @ X28) => ((c_SMALL @ X28) = (c_FAST @ X28)))))).
