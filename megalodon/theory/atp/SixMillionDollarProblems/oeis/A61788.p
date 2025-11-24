% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A61788.mg.html#A61788
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > ($i > $i)))).
thf(c_H1_tp,type,(c_H1 : ($i > ($i > $i)))).
thf(c_I1_tp,type,(c_I1 : $i)).
thf(c_J1_tp,type,(c_J1 : ($i > ($i > $i)))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > ($i > $i))))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > ($i > $i))))).
thf(c_W1_tp,type,(c_W1 : ($i > ($i > $i)))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > ($i > $i)))).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_I0_tp,type,(c_I0 : $i)).
thf(c_J0_tp,type,(c_J0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > ($i > $i))))).
thf(c_V0_tp,type,(c_V0 : ($i > ($i > ($i > $i))))).
thf(c_W0_tp,type,(c_W0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F4_tp,type,(c_F4 : ($i > $i))).
thf(c_G4_tp,type,(c_G4 : $i)).
thf(c_F5_tp,type,(c_F5 : ($i > $i))).
thf(c_G5_tp,type,(c_G5 : ($i > $i))).
thf(c_H5_tp,type,(c_H5 : $i)).
thf(c_U5_tp,type,(c_U5 : ($i > ($i > $i)))).
thf(c_V5_tp,type,(c_V5 : ($i > $i))).
thf(c_H4_tp,type,(c_H4 : ($i > $i))).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > $i)))).
thf(c_V4_tp,type,(c_V4 : ($i > $i))).
thf(c_F6_tp,type,(c_F6 : ($i > ($i > $i)))).
thf(c_G6_tp,type,(c_G6 : ($i > ($i > $i)))).
thf(c_H6_tp,type,(c_H6 : ($i > $i))).
thf(c_I6_tp,type,(c_I6 : ($i > $i))).
thf(c_J6_tp,type,(c_J6 : ($i > $i))).
thf(c_U6_tp,type,(c_U6 : ($i > ($i > ($i > $i))))).
thf(c_V6_tp,type,(c_V6 : ($i > ($i > ($i > $i))))).
thf(c_W6_tp,type,(c_W6 : ($i > $i))).
thf(c_F7_tp,type,(c_F7 : ($i > ($i > $i)))).
thf(c_G7_tp,type,(c_G7 : ($i > ($i > $i)))).
thf(c_H7_tp,type,(c_H7 : ($i > $i))).
thf(c_I7_tp,type,(c_I7 : ($i > $i))).
thf(c_J7_tp,type,(c_J7 : ($i > $i))).
thf(c_U7_tp,type,(c_U7 : ($i > ($i > ($i > $i))))).
thf(c_V7_tp,type,(c_V7 : ($i > ($i > ($i > $i))))).
thf(c_W7_tp,type,(c_W7 : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : $i)).
thf(c_H3_tp,type,(c_H3 : ($i > ($i > $i)))).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > $i)))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_F1 @ X54) @ X55)) @ int)))))).
thf(c_HG1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_G1 @ X54) @ X55)) @ int)))))).
thf(c_HH1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_H1 @ X54) @ X55)) @ int)))))).
thf(c_HI1,axiom,((c_In @ c_I1) @ int)).
thf(c_HJ1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_J1 @ X54) @ X55)) @ int)))))).
thf(c_HU1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_U1 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HV1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_V1 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HW1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_W1 @ X54) @ X55)) @ int)))))).
thf(c_HF0,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_F0 @ X54) @ X55)) @ int)))))).
thf(c_HG0,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_G0 @ X54) @ X55)) @ int)))))).
thf(c_HH0,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_H0 @ X54)) @ int)))).
thf(c_HI0,axiom,((c_In @ c_I0) @ int)).
thf(c_HJ0,axiom,((c_In @ c_J0) @ int)).
thf(c_HU0,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_U0 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HV0,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_V0 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HW0,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_W0 @ X54)) @ int)))).
thf(c_HSMALL,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_SMALL @ X54)) @ int)))).
thf(c_HF4,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_F4 @ X54)) @ int)))).
thf(c_HG4,axiom,((c_In @ c_G4) @ int)).
thf(c_HF5,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_F5 @ X54)) @ int)))).
thf(c_HG5,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_G5 @ X54)) @ int)))).
thf(c_HH5,axiom,((c_In @ c_H5) @ int)).
thf(c_HU5,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_U5 @ X54) @ X55)) @ int)))))).
thf(c_HV5,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_V5 @ X54)) @ int)))).
thf(c_HH4,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_H4 @ X54)) @ int)))).
thf(c_HU4,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_U4 @ X54) @ X55)) @ int)))))).
thf(c_HV4,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_V4 @ X54)) @ int)))).
thf(c_HF6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_F6 @ X54) @ X55)) @ int)))))).
thf(c_HG6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_G6 @ X54) @ X55)) @ int)))))).
thf(c_HH6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_H6 @ X54)) @ int)))).
thf(c_HI6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_I6 @ X54)) @ int)))).
thf(c_HJ6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_J6 @ X54)) @ int)))).
thf(c_HU6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_U6 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HV6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_V6 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HW6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_W6 @ X54)) @ int)))).
thf(c_HF7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_F7 @ X54) @ X55)) @ int)))))).
thf(c_HG7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_G7 @ X54) @ X55)) @ int)))))).
thf(c_HH7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_H7 @ X54)) @ int)))).
thf(c_HI7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_I7 @ X54)) @ int)))).
thf(c_HJ7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_J7 @ X54)) @ int)))).
thf(c_HU7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_U7 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HV7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (((c_V7 @ X54) @ X55) @ X56)) @ int)))))))).
thf(c_HW7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_W7 @ X54)) @ int)))).
thf(c_HF3,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_F3 @ X54)) @ int)))).
thf(c_HG3,axiom,((c_In @ c_G3) @ int)).
thf(c_HH3,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_H3 @ X54) @ X55)) @ int)))))).
thf(c_HU3,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_U3 @ X54) @ X55)) @ int)))))).
thf(c_HV3,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_V3 @ X54) @ X55)) @ int)))))).
thf(c_HF2,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_F2 @ X54) @ X55)) @ int)))))).
thf(c_HG2,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_G2 @ X54)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => ((c_In @ ((c_U2 @ X54) @ X55)) @ int)))))).
thf(c_HV2,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_V2 @ X54)) @ int)))).
thf(c_HFAST,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_In @ (c_FAST @ X54)) @ int)))).
thf(c_H1,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_F1 @ X54) @ X55) = ((mul_5FSNo @ X54) @ X55))))))).
thf(c_H2,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_G1 @ X54) @ X55) = X55)))))).
thf(c_H3,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_H1 @ X54) @ X55) = X55)))))).
thf(c_H4,axiom,(c_I1 = (ordsucc @ c_Empty))).
thf(c_H5,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_J1 @ X54) @ X55) = X55)))))).
thf(c_H6,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_U1 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ ((c_F1 @ (((c_U1 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V1 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H7,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_V1 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X56) @ ((c_G1 @ (((c_U1 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V1 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H8,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_W1 @ X54) @ X55) = (((c_U1 @ ((c_H1 @ X54) @ X55)) @ c_I1) @ ((c_J1 @ X54) @ X55)))))))).
thf(c_H9,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_F0 @ X54) @ X55) = ((add_5FSNo @ ((c_W1 @ X54) @ X55)) @ X54))))))).
thf(c_H10,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_G0 @ X54) @ X55) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X55))))))).
thf(c_H11,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_H0 @ X54) = ((add_5FSNo @ X54) @ (ordsucc @ c_Empty)))))).
thf(c_H12,axiom,(c_I0 = c_Empty)).
thf(c_H13,axiom,(c_J0 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H14,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_U0 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ ((c_F0 @ (((c_U0 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V0 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H15,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_V0 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X56) @ ((c_G0 @ (((c_U0 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V0 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H16,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_W0 @ X54) = (((c_U0 @ (c_H0 @ X54)) @ c_I0) @ c_J0))))).
thf(c_H17,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_SMALL @ X54) = (c_W0 @ X54))))).
thf(c_H18,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_F4 @ X54) = ((mul_5FSNo @ X54) @ X54))))).
thf(c_H19,axiom,(c_G4 = (ordsucc @ c_Empty))).
thf(c_H20,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_F5 @ X54) = ((add_5FSNo @ X54) @ X54))))).
thf(c_H21,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_G5 @ X54) = X54)))).
thf(c_H22,axiom,(c_H5 = (ordsucc @ c_Empty))).
thf(c_H23,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_U5 @ X54) @ X55) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ (c_F5 @ ((c_U5 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55))))))))).
thf(c_H24,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_V5 @ X54) = ((c_U5 @ (c_G5 @ X54)) @ c_H5))))).
thf(c_H25,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_H4 @ X54) = (c_V5 @ X54))))).
thf(c_H26,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_U4 @ X54) @ X55) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ (c_F4 @ ((c_U4 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55))))))))).
thf(c_H27,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_V4 @ X54) = ((c_U4 @ c_G4) @ (c_H4 @ X54)))))).
thf(c_H28,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_F6 @ X54) @ X55) = ((mul_5FSNo @ X54) @ X55))))))).
thf(c_H29,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_G6 @ X54) @ X55) = X55)))))).
thf(c_H30,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_H6 @ X54) = X54)))).
thf(c_H31,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_I6 @ X54) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X54))))).
thf(c_H32,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_J6 @ X54) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X54))))).
thf(c_H33,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_U6 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ ((c_F6 @ (((c_U6 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V6 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H34,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_V6 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X56) @ ((c_G6 @ (((c_U6 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V6 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H35,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_W6 @ X54) = (((c_U6 @ (c_H6 @ X54)) @ (c_I6 @ X54)) @ (c_J6 @ X54)))))).
thf(c_H36,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_F7 @ X54) @ X55) = ((mul_5FSNo @ X54) @ X55))))))).
thf(c_H37,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_G7 @ X54) @ X55) = X55)))))).
thf(c_H38,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_H7 @ X54) = X54)))).
thf(c_H39,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_I7 @ X54) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X54))))).
thf(c_H40,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_J7 @ X54) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X54))))).
thf(c_H41,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_U7 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ ((c_F7 @ (((c_U7 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V7 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H42,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (! [X56:$i] : (((c_In @ X56) @ int) => ((((c_V7 @ X54) @ X55) @ X56) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X56) @ ((c_G7 @ (((c_U7 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56)) @ (((c_V7 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55) @ X56))))))))))).
thf(c_H43,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_W7 @ X54) = (((c_U7 @ (c_H7 @ X54)) @ (c_I7 @ X54)) @ (c_J7 @ X54)))))).
thf(c_H44,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_F3 @ X54) = ((mul_5FSNo @ ((mul_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (c_V4 @ X54))) @ (c_W6 @ X54))) @ (c_W7 @ X54)))))).
thf(c_H45,axiom,(c_G3 = (ordsucc @ c_Empty))).
thf(c_H46,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_H3 @ X54) @ X55) = X55)))))).
thf(c_H47,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_U3 @ X54) @ X55) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55))))))))).
thf(c_H48,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_V3 @ X54) @ X55) = ((c_U3 @ c_G3) @ ((c_H3 @ X54) @ X55)))))))).
thf(c_H49,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_F2 @ X54) @ X55) = ((add_5FSNo @ ((c_V3 @ X54) @ X55)) @ X54))))))).
thf(c_H50,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_G2 @ X54) = X54)))).
thf(c_H51,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H52,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => (! [X55:$i] : (((c_In @ X55) @ int) => (((c_U2 @ X54) @ X55) = (((c_If_5Fi @ ((c_SNoLe @ X54) @ c_Empty)) @ X55) @ ((c_F2 @ ((c_U2 @ ((add_5FSNo @ X54) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X55)) @ X54)))))))).
thf(c_H53,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_V2 @ X54) = ((c_U2 @ (c_G2 @ X54)) @ c_H2))))).
thf(c_H54,axiom,(! [X54:$i] : (((c_In @ X54) @ int) => ((c_FAST @ X54) = ((add_5FSNo @ ((mul_5FSNo @ (c_V2 @ X54)) @ (ordsucc @ (ordsucc @ c_Empty)))) @ (ordsucc @ (ordsucc @ c_Empty))))))).
thf(a61788,conjecture,(! [X54:$i] : (((c_In @ X54) @ int) => (((c_SNoLe @ c_Empty) @ X54) => ((c_SMALL @ X54) = (c_FAST @ X54)))))).
