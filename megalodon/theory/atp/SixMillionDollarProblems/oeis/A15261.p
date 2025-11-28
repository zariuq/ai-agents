% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A15261.mg.html#A15261
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : ($i > ($i > $i)))).
thf(c_H3_tp,type,(c_H3 : $i)).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > $i)))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_F4_tp,type,(c_F4 : ($i > ($i > $i)))).
thf(c_G4_tp,type,(c_G4 : ($i > ($i > $i)))).
thf(c_H4_tp,type,(c_H4 : ($i > $i))).
thf(c_I4_tp,type,(c_I4 : $i)).
thf(c_J4_tp,type,(c_J4 : $i)).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > ($i > $i))))).
thf(c_V4_tp,type,(c_V4 : ($i > ($i > ($i > $i))))).
thf(c_W4_tp,type,(c_W4 : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : $i)).
thf(c_H1_tp,type,(c_H1 : ($i > ($i > $i)))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > $i)))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F7_tp,type,(c_F7 : ($i > ($i > $i)))).
thf(c_G7_tp,type,(c_G7 : ($i > ($i > $i)))).
thf(c_H7_tp,type,(c_H7 : ($i > $i))).
thf(c_I7_tp,type,(c_I7 : $i)).
thf(c_J7_tp,type,(c_J7 : $i)).
thf(c_U7_tp,type,(c_U7 : ($i > ($i > ($i > $i))))).
thf(c_V7_tp,type,(c_V7 : ($i > ($i > ($i > $i))))).
thf(c_W7_tp,type,(c_W7 : ($i > $i))).
thf(c_F8_tp,type,(c_F8 : ($i > ($i > $i)))).
thf(c_G8_tp,type,(c_G8 : ($i > ($i > $i)))).
thf(c_H8_tp,type,(c_H8 : ($i > $i))).
thf(c_I8_tp,type,(c_I8 : $i)).
thf(c_J8_tp,type,(c_J8 : $i)).
thf(c_U8_tp,type,(c_U8 : ($i > ($i > ($i > $i))))).
thf(c_V8_tp,type,(c_V8 : ($i > ($i > ($i > $i))))).
thf(c_W8_tp,type,(c_W8 : ($i > $i))).
thf(c_F6_tp,type,(c_F6 : ($i > $i))).
thf(c_G6_tp,type,(c_G6 : $i)).
thf(c_H6_tp,type,(c_H6 : ($i > ($i > $i)))).
thf(c_U6_tp,type,(c_U6 : ($i > ($i > $i)))).
thf(c_V6_tp,type,(c_V6 : ($i > ($i > $i)))).
thf(c_F5_tp,type,(c_F5 : ($i > ($i > $i)))).
thf(c_G5_tp,type,(c_G5 : ($i > $i))).
thf(c_H5_tp,type,(c_H5 : $i)).
thf(c_U5_tp,type,(c_U5 : ($i > ($i > $i)))).
thf(c_V5_tp,type,(c_V5 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF3,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_F3 @ X56)) @ int)))).
thf(c_HG3,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_G3 @ X56) @ X57)) @ int)))))).
thf(c_HH3,axiom,((c_In @ c_H3) @ int)).
thf(c_HU3,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_U3 @ X56) @ X57)) @ int)))))).
thf(c_HV3,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_V3 @ X56) @ X57)) @ int)))))).
thf(c_HF2,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_F2 @ X56) @ X57)) @ int)))))).
thf(c_HG2,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_G2 @ X56)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_U2 @ X56) @ X57)) @ int)))))).
thf(c_HV2,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_V2 @ X56)) @ int)))).
thf(c_HF4,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_F4 @ X56) @ X57)) @ int)))))).
thf(c_HG4,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_G4 @ X56) @ X57)) @ int)))))).
thf(c_HH4,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_H4 @ X56)) @ int)))).
thf(c_HI4,axiom,((c_In @ c_I4) @ int)).
thf(c_HJ4,axiom,((c_In @ c_J4) @ int)).
thf(c_HU4,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((c_In @ (((c_U4 @ X56) @ X57) @ X58)) @ int)))))))).
thf(c_HV4,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((c_In @ (((c_V4 @ X56) @ X57) @ X58)) @ int)))))))).
thf(c_HW4,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_W4 @ X56)) @ int)))).
thf(c_HF1,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_F1 @ X56)) @ int)))).
thf(c_HG1,axiom,((c_In @ c_G1) @ int)).
thf(c_HH1,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_H1 @ X56) @ X57)) @ int)))))).
thf(c_HU1,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_U1 @ X56) @ X57)) @ int)))))).
thf(c_HV1,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_V1 @ X56) @ X57)) @ int)))))).
thf(c_HF0,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_F0 @ X56) @ X57)) @ int)))))).
thf(c_HG0,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_G0 @ X56)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_U0 @ X56) @ X57)) @ int)))))).
thf(c_HV0,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_V0 @ X56)) @ int)))).
thf(c_HSMALL,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_SMALL @ X56)) @ int)))).
thf(c_HF7,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_F7 @ X56) @ X57)) @ int)))))).
thf(c_HG7,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_G7 @ X56) @ X57)) @ int)))))).
thf(c_HH7,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_H7 @ X56)) @ int)))).
thf(c_HI7,axiom,((c_In @ c_I7) @ int)).
thf(c_HJ7,axiom,((c_In @ c_J7) @ int)).
thf(c_HU7,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((c_In @ (((c_U7 @ X56) @ X57) @ X58)) @ int)))))))).
thf(c_HV7,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((c_In @ (((c_V7 @ X56) @ X57) @ X58)) @ int)))))))).
thf(c_HW7,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_W7 @ X56)) @ int)))).
thf(c_HF8,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_F8 @ X56) @ X57)) @ int)))))).
thf(c_HG8,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_G8 @ X56) @ X57)) @ int)))))).
thf(c_HH8,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_H8 @ X56)) @ int)))).
thf(c_HI8,axiom,((c_In @ c_I8) @ int)).
thf(c_HJ8,axiom,((c_In @ c_J8) @ int)).
thf(c_HU8,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((c_In @ (((c_U8 @ X56) @ X57) @ X58)) @ int)))))))).
thf(c_HV8,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((c_In @ (((c_V8 @ X56) @ X57) @ X58)) @ int)))))))).
thf(c_HW8,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_W8 @ X56)) @ int)))).
thf(c_HF6,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_F6 @ X56)) @ int)))).
thf(c_HG6,axiom,((c_In @ c_G6) @ int)).
thf(c_HH6,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_H6 @ X56) @ X57)) @ int)))))).
thf(c_HU6,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_U6 @ X56) @ X57)) @ int)))))).
thf(c_HV6,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_V6 @ X56) @ X57)) @ int)))))).
thf(c_HF5,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_F5 @ X56) @ X57)) @ int)))))).
thf(c_HG5,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_G5 @ X56)) @ int)))).
thf(c_HH5,axiom,((c_In @ c_H5) @ int)).
thf(c_HU5,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => ((c_In @ ((c_U5 @ X56) @ X57)) @ int)))))).
thf(c_HV5,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_V5 @ X56)) @ int)))).
thf(c_HFAST,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_In @ (c_FAST @ X56)) @ int)))).
thf(c_H1,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_F3 @ X56) = ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X56) @ X56))) @ X56)))))).
thf(c_H2,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_G3 @ X56) @ X57) = X57)))))).
thf(c_H3,axiom,(c_H3 = (ordsucc @ c_Empty))).
thf(c_H4,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_U3 @ X56) @ X57) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57))))))))).
thf(c_H5,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_V3 @ X56) @ X57) = ((c_U3 @ ((c_G3 @ X56) @ X57)) @ c_H3))))))).
thf(c_H6,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_F2 @ X56) @ X57) = ((add_5FSNo @ ((c_V3 @ X56) @ X57)) @ (minus_5FSNo @ X56)))))))).
thf(c_H7,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_G2 @ X56) = X56)))).
thf(c_H8,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H9,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_U2 @ X56) @ X57) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ ((c_F2 @ ((c_U2 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57)) @ X56)))))))).
thf(c_H10,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_V2 @ X56) = ((c_U2 @ (c_G2 @ X56)) @ c_H2))))).
thf(c_H11,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_F4 @ X56) @ X57) = ((mul_5FSNo @ X56) @ X57))))))).
thf(c_H12,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_G4 @ X56) @ X57) = X57)))))).
thf(c_H13,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_H4 @ X56) = X56)))).
thf(c_H14,axiom,(c_I4 = (ordsucc @ c_Empty))).
thf(c_H15,axiom,(c_J4 = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty))))))).
thf(c_H16,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((((c_U4 @ X56) @ X57) @ X58) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ ((c_F4 @ (((c_U4 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58)) @ (((c_V4 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58))))))))))).
thf(c_H17,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((((c_V4 @ X56) @ X57) @ X58) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X58) @ ((c_G4 @ (((c_U4 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58)) @ (((c_V4 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58))))))))))).
thf(c_H18,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_W4 @ X56) = (((c_U4 @ (c_H4 @ X56)) @ c_I4) @ c_J4))))).
thf(c_H19,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_F1 @ X56) = ((mul_5FSNo @ (c_V2 @ X56)) @ (c_W4 @ X56)))))).
thf(c_H20,axiom,(c_G1 = (ordsucc @ c_Empty))).
thf(c_H21,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_H1 @ X56) @ X57) = X57)))))).
thf(c_H22,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_U1 @ X56) @ X57) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57))))))))).
thf(c_H23,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_V1 @ X56) @ X57) = ((c_U1 @ c_G1) @ ((c_H1 @ X56) @ X57)))))))).
thf(c_H24,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_F0 @ X56) @ X57) = ((add_5FSNo @ ((c_V1 @ X56) @ X57)) @ X56))))))).
thf(c_H25,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_G0 @ X56) = X56)))).
thf(c_H26,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H27,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_U0 @ X56) @ X57) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57)) @ X56)))))))).
thf(c_H28,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_V0 @ X56) = ((c_U0 @ (c_G0 @ X56)) @ c_H0))))).
thf(c_H29,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_SMALL @ X56) = (c_V0 @ X56))))).
thf(c_H30,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_F7 @ X56) @ X57) = ((add_5FSNo @ X57) @ (minus_5FSNo @ X56)))))))).
thf(c_H31,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_G7 @ X56) @ X57) = ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X57) @ X57))) @ X57)))))))).
thf(c_H32,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_H7 @ X56) = X56)))).
thf(c_H33,axiom,(c_I7 = (ordsucc @ c_Empty))).
thf(c_H34,axiom,(c_J7 = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty))))))).
thf(c_H35,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((((c_U7 @ X56) @ X57) @ X58) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ ((c_F7 @ (((c_U7 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58)) @ (((c_V7 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58))))))))))).
thf(c_H36,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((((c_V7 @ X56) @ X57) @ X58) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X58) @ ((c_G7 @ (((c_U7 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58)) @ (((c_V7 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58))))))))))).
thf(c_H37,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_W7 @ X56) = (((c_U7 @ (c_H7 @ X56)) @ c_I7) @ c_J7))))).
thf(c_H38,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_F8 @ X56) @ X57) = ((mul_5FSNo @ X56) @ X57))))))).
thf(c_H39,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_G8 @ X56) @ X57) = X57)))))).
thf(c_H40,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_H8 @ X56) = X56)))).
thf(c_H41,axiom,(c_I8 = (ordsucc @ c_Empty))).
thf(c_H42,axiom,(c_J8 = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty))))))).
thf(c_H43,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((((c_U8 @ X56) @ X57) @ X58) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ ((c_F8 @ (((c_U8 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58)) @ (((c_V8 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58))))))))))).
thf(c_H44,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (! [X58:$i] : (((c_In @ X58) @ int) => ((((c_V8 @ X56) @ X57) @ X58) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X58) @ ((c_G8 @ (((c_U8 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58)) @ (((c_V8 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57) @ X58))))))))))).
thf(c_H45,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_W8 @ X56) = (((c_U8 @ (c_H8 @ X56)) @ c_I8) @ c_J8))))).
thf(c_H46,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_F6 @ X56) = ((mul_5FSNo @ (c_W7 @ X56)) @ (c_W8 @ X56)))))).
thf(c_H47,axiom,(c_G6 = (ordsucc @ c_Empty))).
thf(c_H48,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_H6 @ X56) @ X57) = X57)))))).
thf(c_H49,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_U6 @ X56) @ X57) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ (c_F6 @ ((c_U6 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57))))))))).
thf(c_H50,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_V6 @ X56) @ X57) = ((c_U6 @ c_G6) @ ((c_H6 @ X56) @ X57)))))))).
thf(c_H51,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_F5 @ X56) @ X57) = ((add_5FSNo @ ((c_V6 @ X56) @ X57)) @ X56))))))).
thf(c_H52,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_G5 @ X56) = X56)))).
thf(c_H53,axiom,(c_H5 = (ordsucc @ c_Empty))).
thf(c_H54,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => (! [X57:$i] : (((c_In @ X57) @ int) => (((c_U5 @ X56) @ X57) = (((c_If_5Fi @ ((c_SNoLe @ X56) @ c_Empty)) @ X57) @ ((c_F5 @ ((c_U5 @ ((add_5FSNo @ X56) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X57)) @ X56)))))))).
thf(c_H55,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_V5 @ X56) = ((c_U5 @ (c_G5 @ X56)) @ c_H5))))).
thf(c_H56,axiom,(! [X56:$i] : (((c_In @ X56) @ int) => ((c_FAST @ X56) = (c_V5 @ X56))))).
thf(a15261,conjecture,(! [X56:$i] : (((c_In @ X56) @ int) => (((c_SNoLe @ c_Empty) @ X56) => ((c_SMALL @ X56) = (c_FAST @ X56)))))).
