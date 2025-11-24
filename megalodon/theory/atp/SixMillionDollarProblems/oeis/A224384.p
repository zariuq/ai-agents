% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A224384.mg.html#A224384
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
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > ($i > $i)))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_I2_tp,type,(c_I2 : $i)).
thf(c_J2_tp,type,(c_J2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > ($i > $i))))).
thf(c_V2_tp,type,(c_V2 : ($i > ($i > ($i > $i))))).
thf(c_W2_tp,type,(c_W2 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF1,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_F1 @ X20)) @ int)))).
thf(c_HG1,axiom,((c_In @ c_G1) @ int)).
thf(c_HH1,axiom,((c_In @ c_H1) @ int)).
thf(c_HU1,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => ((c_In @ ((c_U1 @ X20) @ X21)) @ int)))))).
thf(c_HV1,axiom,((c_In @ c_V1) @ int)).
thf(c_HF0,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_F0 @ X20)) @ int)))).
thf(c_HG0,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_G0 @ X20)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => ((c_In @ ((c_U0 @ X20) @ X21)) @ int)))))).
thf(c_HV0,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_V0 @ X20)) @ int)))).
thf(c_HSMALL,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_SMALL @ X20)) @ int)))).
thf(c_HF2,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => ((c_In @ ((c_F2 @ X20) @ X21)) @ int)))))).
thf(c_HG2,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => ((c_In @ ((c_G2 @ X20) @ X21)) @ int)))))).
thf(c_HH2,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_H2 @ X20)) @ int)))).
thf(c_HI2,axiom,((c_In @ c_I2) @ int)).
thf(c_HJ2,axiom,((c_In @ c_J2) @ int)).
thf(c_HU2,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (((c_U2 @ X20) @ X21) @ X22)) @ int)))))))).
thf(c_HV2,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (! [X22:$i] : (((c_In @ X22) @ int) => ((c_In @ (((c_V2 @ X20) @ X21) @ X22)) @ int)))))))).
thf(c_HW2,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_W2 @ X20)) @ int)))).
thf(c_HFAST,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (c_FAST @ X20)) @ int)))).
thf(c_H1,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_F1 @ X20) = ((mul_5FSNo @ X20) @ X20))))).
thf(c_H2,axiom,(c_G1 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H3,axiom,(c_H1 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H4,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (((c_U1 @ X20) @ X21) = (((c_If_5Fi @ ((c_SNoLe @ X20) @ c_Empty)) @ X21) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X20) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X21))))))))).
thf(c_H5,axiom,(c_V1 = ((c_U1 @ c_G1) @ c_H1))).
thf(c_H6,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_F0 @ X20) = ((add_5FSNo @ ((mul_5FSNo @ c_V1) @ X20)) @ X20))))).
thf(c_H7,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_G0 @ X20) = X20)))).
thf(c_H8,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H9,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (((c_U0 @ X20) @ X21) = (((c_If_5Fi @ ((c_SNoLe @ X20) @ c_Empty)) @ X21) @ (c_F0 @ ((c_U0 @ ((add_5FSNo @ X20) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X21))))))))).
thf(c_H10,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_V0 @ X20) = ((c_U0 @ (c_G0 @ X20)) @ c_H0))))).
thf(c_H11,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_SMALL @ X20) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (c_V0 @ X20)))))).
thf(c_H12,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (((c_F2 @ X20) @ X21) = ((mul_5FSNo @ X20) @ X21))))))).
thf(c_H13,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (((c_G2 @ X20) @ X21) = X21)))))).
thf(c_H14,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_H2 @ X20) = X20)))).
thf(c_H15,axiom,(c_I2 = (ordsucc @ c_Empty))).
thf(c_H16,axiom,(c_J2 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))))).
thf(c_H17,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (! [X22:$i] : (((c_In @ X22) @ int) => ((((c_U2 @ X20) @ X21) @ X22) = (((c_If_5Fi @ ((c_SNoLe @ X20) @ c_Empty)) @ X21) @ ((c_F2 @ (((c_U2 @ ((add_5FSNo @ X20) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X21) @ X22)) @ (((c_V2 @ ((add_5FSNo @ X20) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X21) @ X22))))))))))).
thf(c_H18,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => (! [X21:$i] : (((c_In @ X21) @ int) => (! [X22:$i] : (((c_In @ X22) @ int) => ((((c_V2 @ X20) @ X21) @ X22) = (((c_If_5Fi @ ((c_SNoLe @ X20) @ c_Empty)) @ X22) @ ((c_G2 @ (((c_U2 @ ((add_5FSNo @ X20) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X21) @ X22)) @ (((c_V2 @ ((add_5FSNo @ X20) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X21) @ X22))))))))))).
thf(c_H19,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_W2 @ X20) = (((c_U2 @ (c_H2 @ X20)) @ c_I2) @ c_J2))))).
thf(c_H20,axiom,(! [X20:$i] : (((c_In @ X20) @ int) => ((c_FAST @ X20) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (c_W2 @ X20)))))).
thf(a224384,conjecture,(! [X20:$i] : (((c_In @ X20) @ int) => (((c_SNoLe @ c_Empty) @ X20) => ((c_SMALL @ X20) = (c_FAST @ X20)))))).
