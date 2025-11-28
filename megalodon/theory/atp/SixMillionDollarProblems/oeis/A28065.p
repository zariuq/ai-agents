% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A28065.mg.html#A28065
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : ($i > $i))).
thf(c_F4_tp,type,(c_F4 : ($i > $i))).
thf(c_G4_tp,type,(c_G4 : ($i > $i))).
thf(c_H4_tp,type,(c_H4 : $i)).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > $i)))).
thf(c_V4_tp,type,(c_V4 : ($i > $i))).
thf(c_H3_tp,type,(c_H3 : ($i > $i))).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > $i))).
thf(c_G2_tp,type,(c_G2 : $i)).
thf(c_H2_tp,type,(c_H2 : ($i > ($i > $i)))).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > ($i > $i)))).
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > ($i > $i)))).
thf(c_H1_tp,type,(c_H1 : $i)).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > $i)))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F9_tp,type,(c_F9 : ($i > $i))).
thf(c_G9_tp,type,(c_G9 : ($i > $i))).
thf(c_H9_tp,type,(c_H9 : $i)).
thf(c_U9_tp,type,(c_U9 : ($i > ($i > $i)))).
thf(c_V9_tp,type,(c_V9 : ($i > $i))).
thf(c_F10_tp,type,(c_F10 : ($i > ($i > $i)))).
thf(c_G10_tp,type,(c_G10 : ($i > ($i > $i)))).
thf(c_H10_tp,type,(c_H10 : ($i > $i))).
thf(c_I10_tp,type,(c_I10 : $i)).
thf(c_J10_tp,type,(c_J10 : $i)).
thf(c_U10_tp,type,(c_U10 : ($i > ($i > ($i > $i))))).
thf(c_V10_tp,type,(c_V10 : ($i > ($i > ($i > $i))))).
thf(c_W10_tp,type,(c_W10 : ($i > $i))).
thf(c_F8_tp,type,(c_F8 : ($i > $i))).
thf(c_G8_tp,type,(c_G8 : $i)).
thf(c_H8_tp,type,(c_H8 : ($i > ($i > $i)))).
thf(c_U8_tp,type,(c_U8 : ($i > ($i > $i)))).
thf(c_V8_tp,type,(c_V8 : ($i > ($i > $i)))).
thf(c_F7_tp,type,(c_F7 : ($i > ($i > $i)))).
thf(c_G7_tp,type,(c_G7 : ($i > $i))).
thf(c_H7_tp,type,(c_H7 : $i)).
thf(c_U7_tp,type,(c_U7 : ($i > ($i > $i)))).
thf(c_V7_tp,type,(c_V7 : ($i > $i))).
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
thf(c_HF3,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_F3 @ X60)) @ int)))).
thf(c_HG3,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_G3 @ X60)) @ int)))).
thf(c_HF4,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_F4 @ X60)) @ int)))).
thf(c_HG4,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_G4 @ X60)) @ int)))).
thf(c_HH4,axiom,((c_In @ c_H4) @ int)).
thf(c_HU4,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U4 @ X60) @ X61)) @ int)))))).
thf(c_HV4,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_V4 @ X60)) @ int)))).
thf(c_HH3,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_H3 @ X60)) @ int)))).
thf(c_HU3,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U3 @ X60) @ X61)) @ int)))))).
thf(c_HV3,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_V3 @ X60)) @ int)))).
thf(c_HF2,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_F2 @ X60)) @ int)))).
thf(c_HG2,axiom,((c_In @ c_G2) @ int)).
thf(c_HH2,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_H2 @ X60) @ X61)) @ int)))))).
thf(c_HU2,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U2 @ X60) @ X61)) @ int)))))).
thf(c_HV2,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_V2 @ X60) @ X61)) @ int)))))).
thf(c_HF1,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_F1 @ X60) @ X61)) @ int)))))).
thf(c_HG1,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_G1 @ X60) @ X61)) @ int)))))).
thf(c_HH1,axiom,((c_In @ c_H1) @ int)).
thf(c_HU1,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U1 @ X60) @ X61)) @ int)))))).
thf(c_HV1,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_V1 @ X60) @ X61)) @ int)))))).
thf(c_HF0,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_F0 @ X60) @ X61)) @ int)))))).
thf(c_HG0,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_G0 @ X60)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U0 @ X60) @ X61)) @ int)))))).
thf(c_HV0,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_V0 @ X60)) @ int)))).
thf(c_HSMALL,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_SMALL @ X60)) @ int)))).
thf(c_HF9,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_F9 @ X60)) @ int)))).
thf(c_HG9,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_G9 @ X60)) @ int)))).
thf(c_HH9,axiom,((c_In @ c_H9) @ int)).
thf(c_HU9,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U9 @ X60) @ X61)) @ int)))))).
thf(c_HV9,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_V9 @ X60)) @ int)))).
thf(c_HF10,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_F10 @ X60) @ X61)) @ int)))))).
thf(c_HG10,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_G10 @ X60) @ X61)) @ int)))))).
thf(c_HH10,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_H10 @ X60)) @ int)))).
thf(c_HI10,axiom,((c_In @ c_I10) @ int)).
thf(c_HJ10,axiom,((c_In @ c_J10) @ int)).
thf(c_HU10,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (! [X62:$i] : (((c_In @ X62) @ int) => ((c_In @ (((c_U10 @ X60) @ X61) @ X62)) @ int)))))))).
thf(c_HV10,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (! [X62:$i] : (((c_In @ X62) @ int) => ((c_In @ (((c_V10 @ X60) @ X61) @ X62)) @ int)))))))).
thf(c_HW10,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_W10 @ X60)) @ int)))).
thf(c_HF8,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_F8 @ X60)) @ int)))).
thf(c_HG8,axiom,((c_In @ c_G8) @ int)).
thf(c_HH8,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_H8 @ X60) @ X61)) @ int)))))).
thf(c_HU8,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U8 @ X60) @ X61)) @ int)))))).
thf(c_HV8,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_V8 @ X60) @ X61)) @ int)))))).
thf(c_HF7,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_F7 @ X60) @ X61)) @ int)))))).
thf(c_HG7,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_G7 @ X60)) @ int)))).
thf(c_HH7,axiom,((c_In @ c_H7) @ int)).
thf(c_HU7,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U7 @ X60) @ X61)) @ int)))))).
thf(c_HV7,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_V7 @ X60)) @ int)))).
thf(c_HF6,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_F6 @ X60)) @ int)))).
thf(c_HG6,axiom,((c_In @ c_G6) @ int)).
thf(c_HH6,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_H6 @ X60) @ X61)) @ int)))))).
thf(c_HU6,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U6 @ X60) @ X61)) @ int)))))).
thf(c_HV6,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_V6 @ X60) @ X61)) @ int)))))).
thf(c_HF5,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_F5 @ X60) @ X61)) @ int)))))).
thf(c_HG5,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_G5 @ X60)) @ int)))).
thf(c_HH5,axiom,((c_In @ c_H5) @ int)).
thf(c_HU5,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => ((c_In @ ((c_U5 @ X60) @ X61)) @ int)))))).
thf(c_HV5,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_V5 @ X60)) @ int)))).
thf(c_HFAST,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_In @ (c_FAST @ X60)) @ int)))).
thf(c_H1,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_F3 @ X60) = ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X60) @ X60))) @ X60))))).
thf(c_H2,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_G3 @ X60) = X60)))).
thf(c_H3,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_F4 @ X60) = ((add_5FSNo @ X60) @ X60))))).
thf(c_H4,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_G4 @ X60) = X60)))).
thf(c_H5,axiom,(c_H4 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H6,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U4 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ (c_F4 @ ((c_U4 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61))))))))).
thf(c_H7,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_V4 @ X60) = ((c_U4 @ (c_G4 @ X60)) @ c_H4))))).
thf(c_H8,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_H3 @ X60) = ((add_5FSNo @ (c_V4 @ X60)) @ (minus_5FSNo @ (ordsucc @ c_Empty))))))).
thf(c_H9,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U3 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61))))))))).
thf(c_H10,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_V3 @ X60) = ((c_U3 @ (c_G3 @ X60)) @ (c_H3 @ X60)))))).
thf(c_H11,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_F2 @ X60) = (c_V3 @ X60))))).
thf(c_H12,axiom,(c_G2 = (ordsucc @ c_Empty))).
thf(c_H13,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_H2 @ X60) @ X61) = X61)))))).
thf(c_H14,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U2 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ (c_F2 @ ((c_U2 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61))))))))).
thf(c_H15,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_V2 @ X60) @ X61) = ((c_U2 @ c_G2) @ ((c_H2 @ X60) @ X61)))))))).
thf(c_H16,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_F1 @ X60) @ X61) = ((add_5FSNo @ ((c_V2 @ X60) @ X61)) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X60) @ X60)))))))))).
thf(c_H17,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_G1 @ X60) @ X61) = X61)))))).
thf(c_H18,axiom,(c_H1 = (ordsucc @ c_Empty))).
thf(c_H19,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U1 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ ((c_F1 @ ((c_U1 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61)) @ X60)))))))).
thf(c_H20,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_V1 @ X60) @ X61) = ((c_U1 @ ((c_G1 @ X60) @ X61)) @ c_H1))))))).
thf(c_H21,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_F0 @ X60) @ X61) = ((add_5FSNo @ ((add_5FSNo @ ((add_5FSNo @ ((c_V1 @ X60) @ X61)) @ X60)) @ X60)) @ X60))))))).
thf(c_H22,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_G0 @ X60) = X60)))).
thf(c_H23,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H24,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U0 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61)) @ X60)))))))).
thf(c_H25,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_V0 @ X60) = ((c_U0 @ (c_G0 @ X60)) @ c_H0))))).
thf(c_H26,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_SMALL @ X60) = (c_V0 @ X60))))).
thf(c_H27,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_F9 @ X60) = ((add_5FSNo @ X60) @ X60))))).
thf(c_H28,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_G9 @ X60) = X60)))).
thf(c_H29,axiom,(c_H9 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H30,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U9 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ (c_F9 @ ((c_U9 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61))))))))).
thf(c_H31,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_V9 @ X60) = ((c_U9 @ (c_G9 @ X60)) @ c_H9))))).
thf(c_H32,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_F10 @ X60) @ X61) = ((mul_5FSNo @ X60) @ X61))))))).
thf(c_H33,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_G10 @ X60) @ X61) = X61)))))).
thf(c_H34,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_H10 @ X60) = X60)))).
thf(c_H35,axiom,(c_I10 = (ordsucc @ c_Empty))).
thf(c_H36,axiom,(c_J10 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))).
thf(c_H37,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (! [X62:$i] : (((c_In @ X62) @ int) => ((((c_U10 @ X60) @ X61) @ X62) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ ((c_F10 @ (((c_U10 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61) @ X62)) @ (((c_V10 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61) @ X62))))))))))).
thf(c_H38,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (! [X62:$i] : (((c_In @ X62) @ int) => ((((c_V10 @ X60) @ X61) @ X62) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X62) @ ((c_G10 @ (((c_U10 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61) @ X62)) @ (((c_V10 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61) @ X62))))))))))).
thf(c_H39,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_W10 @ X60) = (((c_U10 @ (c_H10 @ X60)) @ c_I10) @ c_J10))))).
thf(c_H40,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_F8 @ X60) = ((mul_5FSNo @ ((add_5FSNo @ (c_V9 @ X60)) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ (c_W10 @ X60)))))).
thf(c_H41,axiom,(c_G8 = (ordsucc @ c_Empty))).
thf(c_H42,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_H8 @ X60) @ X61) = X61)))))).
thf(c_H43,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U8 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ (c_F8 @ ((c_U8 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61))))))))).
thf(c_H44,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_V8 @ X60) @ X61) = ((c_U8 @ c_G8) @ ((c_H8 @ X60) @ X61)))))))).
thf(c_H45,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_F7 @ X60) @ X61) = ((add_5FSNo @ ((add_5FSNo @ ((add_5FSNo @ ((c_V8 @ X60) @ X61)) @ X60)) @ X60)) @ X60))))))).
thf(c_H46,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_G7 @ X60) = X60)))).
thf(c_H47,axiom,(c_H7 = (ordsucc @ c_Empty))).
thf(c_H48,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U7 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ ((c_F7 @ ((c_U7 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61)) @ X60)))))))).
thf(c_H49,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_V7 @ X60) = ((c_U7 @ (c_G7 @ X60)) @ c_H7))))).
thf(c_H50,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_F6 @ X60) = (c_V7 @ X60))))).
thf(c_H51,axiom,(c_G6 = (ordsucc @ c_Empty))).
thf(c_H52,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_H6 @ X60) @ X61) = X61)))))).
thf(c_H53,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U6 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ (c_F6 @ ((c_U6 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61))))))))).
thf(c_H54,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_V6 @ X60) @ X61) = ((c_U6 @ c_G6) @ ((c_H6 @ X60) @ X61)))))))).
thf(c_H55,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_F5 @ X60) @ X61) = ((add_5FSNo @ ((c_V6 @ X60) @ X61)) @ ((mul_5FSNo @ ((mul_5FSNo @ ((add_5FSNo @ X60) @ X60)) @ (ordsucc @ (ordsucc @ c_Empty)))) @ (ordsucc @ (ordsucc @ c_Empty)))))))))).
thf(c_H56,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_G5 @ X60) = X60)))).
thf(c_H57,axiom,(c_H5 = (ordsucc @ c_Empty))).
thf(c_H58,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => (! [X61:$i] : (((c_In @ X61) @ int) => (((c_U5 @ X60) @ X61) = (((c_If_5Fi @ ((c_SNoLe @ X60) @ c_Empty)) @ X61) @ ((c_F5 @ ((c_U5 @ ((add_5FSNo @ X60) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X61)) @ X60)))))))).
thf(c_H59,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_V5 @ X60) = ((c_U5 @ (c_G5 @ X60)) @ c_H5))))).
thf(c_H60,axiom,(! [X60:$i] : (((c_In @ X60) @ int) => ((c_FAST @ X60) = (c_V5 @ X60))))).
thf(a28065,conjecture,(! [X60:$i] : (((c_In @ X60) @ int) => (((c_SNoLe @ c_Empty) @ X60) => ((c_SMALL @ X60) = (c_FAST @ X60)))))).
