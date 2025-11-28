% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A179135.mg.html#A179135
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > ($i > $i)))).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_I0_tp,type,(c_I0 : $i)).
thf(c_J0_tp,type,(c_J0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > ($i > $i))))).
thf(c_V0_tp,type,(c_V0 : ($i > ($i > ($i > $i))))).
thf(c_W0_tp,type,(c_W0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > $i))).
thf(c_H1_tp,type,(c_H1 : ($i > $i))).
thf(c_I1_tp,type,(c_I1 : $i)).
thf(c_J1_tp,type,(c_J1 : $i)).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > ($i > $i))))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > ($i > $i))))).
thf(c_W1_tp,type,(c_W1 : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > ($i > $i)))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_I2_tp,type,(c_I2 : $i)).
thf(c_J2_tp,type,(c_J2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > ($i > $i))))).
thf(c_V2_tp,type,(c_V2 : ($i > ($i > ($i > $i))))).
thf(c_W2_tp,type,(c_W2 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((c_In @ ((c_F0 @ X26) @ X27)) @ int)))))).
thf(c_HG0,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((c_In @ ((c_G0 @ X26) @ X27)) @ int)))))).
thf(c_HH0,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_H0 @ X26)) @ int)))).
thf(c_HI0,axiom,((c_In @ c_I0) @ int)).
thf(c_HJ0,axiom,((c_In @ c_J0) @ int)).
thf(c_HU0,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (((c_U0 @ X26) @ X27) @ X28)) @ int)))))))).
thf(c_HV0,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (((c_V0 @ X26) @ X27) @ X28)) @ int)))))))).
thf(c_HW0,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_W0 @ X26)) @ int)))).
thf(c_HSMALL,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_SMALL @ X26)) @ int)))).
thf(c_HF1,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((c_In @ ((c_F1 @ X26) @ X27)) @ int)))))).
thf(c_HG1,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_G1 @ X26)) @ int)))).
thf(c_HH1,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_H1 @ X26)) @ int)))).
thf(c_HI1,axiom,((c_In @ c_I1) @ int)).
thf(c_HJ1,axiom,((c_In @ c_J1) @ int)).
thf(c_HU1,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (((c_U1 @ X26) @ X27) @ X28)) @ int)))))))).
thf(c_HV1,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (((c_V1 @ X26) @ X27) @ X28)) @ int)))))))).
thf(c_HW1,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_W1 @ X26)) @ int)))).
thf(c_HF2,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((c_In @ ((c_F2 @ X26) @ X27)) @ int)))))).
thf(c_HG2,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => ((c_In @ ((c_G2 @ X26) @ X27)) @ int)))))).
thf(c_HH2,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_H2 @ X26)) @ int)))).
thf(c_HI2,axiom,((c_In @ c_I2) @ int)).
thf(c_HJ2,axiom,((c_In @ c_J2) @ int)).
thf(c_HU2,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (((c_U2 @ X26) @ X27) @ X28)) @ int)))))))).
thf(c_HV2,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((c_In @ (((c_V2 @ X26) @ X27) @ X28)) @ int)))))))).
thf(c_HW2,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_W2 @ X26)) @ int)))).
thf(c_HFAST,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_In @ (c_FAST @ X26)) @ int)))).
thf(c_H1,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (((c_F0 @ X26) @ X27) = ((add_5FSNo @ X26) @ X27))))))).
thf(c_H2,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (((c_G0 @ X26) @ X27) = ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X27) @ X27))) @ (minus_5FSNo @ X26)))))))).
thf(c_H3,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_H0 @ X26) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ X26) @ X26)))))).
thf(c_H4,axiom,(c_I0 = (ordsucc @ c_Empty))).
thf(c_H5,axiom,(c_J0 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H6,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((((c_U0 @ X26) @ X27) @ X28) = (((c_If_5Fi @ ((c_SNoLe @ X26) @ c_Empty)) @ X27) @ ((c_F0 @ (((c_U0 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28)) @ (((c_V0 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28))))))))))).
thf(c_H7,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((((c_V0 @ X26) @ X27) @ X28) = (((c_If_5Fi @ ((c_SNoLe @ X26) @ c_Empty)) @ X28) @ ((c_G0 @ (((c_U0 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28)) @ (((c_V0 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28))))))))))).
thf(c_H8,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_W0 @ X26) = (((c_U0 @ (c_H0 @ X26)) @ c_I0) @ c_J0))))).
thf(c_H9,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_SMALL @ X26) = (c_W0 @ X26))))).
thf(c_H10,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (((c_F1 @ X26) @ X27) = ((add_5FSNo @ ((add_5FSNo @ ((add_5FSNo @ X26) @ (minus_5FSNo @ X27))) @ X26)) @ X26))))))).
thf(c_H11,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_G1 @ X26) = X26)))).
thf(c_H12,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_H1 @ X26) = X26)))).
thf(c_H13,axiom,(c_I1 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (ordsucc @ (ordsucc @ c_Empty))))).
thf(c_H14,axiom,(c_J1 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H15,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((((c_U1 @ X26) @ X27) @ X28) = (((c_If_5Fi @ ((c_SNoLe @ X26) @ c_Empty)) @ X27) @ ((c_F1 @ (((c_U1 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28)) @ (((c_V1 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28))))))))))).
thf(c_H16,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((((c_V1 @ X26) @ X27) @ X28) = (((c_If_5Fi @ ((c_SNoLe @ X26) @ c_Empty)) @ X28) @ (c_G1 @ (((c_U1 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28))))))))))).
thf(c_H17,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_W1 @ X26) = (((c_U1 @ (c_H1 @ X26)) @ c_I1) @ c_J1))))).
thf(c_H18,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (((c_F2 @ X26) @ X27) = ((mul_5FSNo @ X26) @ X27))))))).
thf(c_H19,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (((c_G2 @ X26) @ X27) = X27)))))).
thf(c_H20,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_H2 @ X26) = X26)))).
thf(c_H21,axiom,(c_I2 = (ordsucc @ c_Empty))).
thf(c_H22,axiom,(c_J2 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))).
thf(c_H23,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((((c_U2 @ X26) @ X27) @ X28) = (((c_If_5Fi @ ((c_SNoLe @ X26) @ c_Empty)) @ X27) @ ((c_F2 @ (((c_U2 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28)) @ (((c_V2 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28))))))))))).
thf(c_H24,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => (! [X27:$i] : (((c_In @ X27) @ int) => (! [X28:$i] : (((c_In @ X28) @ int) => ((((c_V2 @ X26) @ X27) @ X28) = (((c_If_5Fi @ ((c_SNoLe @ X26) @ c_Empty)) @ X28) @ ((c_G2 @ (((c_U2 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28)) @ (((c_V2 @ ((add_5FSNo @ X26) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X27) @ X28))))))))))).
thf(c_H25,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_W2 @ X26) = (((c_U2 @ (c_H2 @ X26)) @ c_I2) @ c_J2))))).
thf(c_H26,axiom,(! [X26:$i] : (((c_In @ X26) @ int) => ((c_FAST @ X26) = ((mul_5FSNo @ (c_W1 @ X26)) @ (c_W2 @ X26)))))).
thf(a179135,conjecture,(! [X26:$i] : (((c_In @ X26) @ int) => (((c_SNoLe @ c_Empty) @ X26) => ((c_SMALL @ X26) = (c_FAST @ X26)))))).
