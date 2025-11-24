% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A20567.mg.html#A20567
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F2_tp,type,(c_F2 : ($i > $i))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : ($i > $i))).
thf(c_H3_tp,type,(c_H3 : $i)).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : $i)).
thf(c_H1_tp,type,(c_H1 : ($i > ($i > $i)))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > $i)))).
thf(c_F4_tp,type,(c_F4 : ($i > ($i > $i)))).
thf(c_G4_tp,type,(c_G4 : $i)).
thf(c_H4_tp,type,(c_H4 : ($i > $i))).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > $i)))).
thf(c_V4_tp,type,(c_V4 : ($i > $i))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F7_tp,type,(c_F7 : ($i > $i))).
thf(c_G7_tp,type,(c_G7 : ($i > $i))).
thf(c_H7_tp,type,(c_H7 : $i)).
thf(c_U7_tp,type,(c_U7 : ($i > ($i > $i)))).
thf(c_V7_tp,type,(c_V7 : ($i > $i))).
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
thf(c_HF2,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_F2 @ X50)) @ int)))).
thf(c_HG2,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_G2 @ X50)) @ int)))).
thf(c_HF3,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_F3 @ X50)) @ int)))).
thf(c_HG3,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_G3 @ X50)) @ int)))).
thf(c_HH3,axiom,((c_In @ c_H3) @ int)).
thf(c_HU3,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U3 @ X50) @ X51)) @ int)))))).
thf(c_HV3,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_V3 @ X50)) @ int)))).
thf(c_HH2,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_H2 @ X50)) @ int)))).
thf(c_HU2,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U2 @ X50) @ X51)) @ int)))))).
thf(c_HV2,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_V2 @ X50)) @ int)))).
thf(c_HF1,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_F1 @ X50)) @ int)))).
thf(c_HG1,axiom,((c_In @ c_G1) @ int)).
thf(c_HH1,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_H1 @ X50) @ X51)) @ int)))))).
thf(c_HU1,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U1 @ X50) @ X51)) @ int)))))).
thf(c_HV1,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_V1 @ X50) @ X51)) @ int)))))).
thf(c_HF4,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_F4 @ X50) @ X51)) @ int)))))).
thf(c_HG4,axiom,((c_In @ c_G4) @ int)).
thf(c_HH4,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_H4 @ X50)) @ int)))).
thf(c_HU4,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U4 @ X50) @ X51)) @ int)))))).
thf(c_HV4,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_V4 @ X50)) @ int)))).
thf(c_HF0,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_F0 @ X50) @ X51)) @ int)))))).
thf(c_HG0,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_G0 @ X50)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U0 @ X50) @ X51)) @ int)))))).
thf(c_HV0,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_V0 @ X50)) @ int)))).
thf(c_HSMALL,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_SMALL @ X50)) @ int)))).
thf(c_HF7,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_F7 @ X50)) @ int)))).
thf(c_HG7,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_G7 @ X50)) @ int)))).
thf(c_HH7,axiom,((c_In @ c_H7) @ int)).
thf(c_HU7,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U7 @ X50) @ X51)) @ int)))))).
thf(c_HV7,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_V7 @ X50)) @ int)))).
thf(c_HF8,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_F8 @ X50) @ X51)) @ int)))))).
thf(c_HG8,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_G8 @ X50) @ X51)) @ int)))))).
thf(c_HH8,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_H8 @ X50)) @ int)))).
thf(c_HI8,axiom,((c_In @ c_I8) @ int)).
thf(c_HJ8,axiom,((c_In @ c_J8) @ int)).
thf(c_HU8,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (! [X52:$i] : (((c_In @ X52) @ int) => ((c_In @ (((c_U8 @ X50) @ X51) @ X52)) @ int)))))))).
thf(c_HV8,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (! [X52:$i] : (((c_In @ X52) @ int) => ((c_In @ (((c_V8 @ X50) @ X51) @ X52)) @ int)))))))).
thf(c_HW8,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_W8 @ X50)) @ int)))).
thf(c_HF6,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_F6 @ X50)) @ int)))).
thf(c_HG6,axiom,((c_In @ c_G6) @ int)).
thf(c_HH6,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_H6 @ X50) @ X51)) @ int)))))).
thf(c_HU6,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U6 @ X50) @ X51)) @ int)))))).
thf(c_HV6,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_V6 @ X50) @ X51)) @ int)))))).
thf(c_HF5,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_F5 @ X50) @ X51)) @ int)))))).
thf(c_HG5,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_G5 @ X50)) @ int)))).
thf(c_HH5,axiom,((c_In @ c_H5) @ int)).
thf(c_HU5,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => ((c_In @ ((c_U5 @ X50) @ X51)) @ int)))))).
thf(c_HV5,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_V5 @ X50)) @ int)))).
thf(c_HFAST,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_In @ (c_FAST @ X50)) @ int)))).
thf(c_H1,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_F2 @ X50) = ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X50) @ X50))) @ X50))))).
thf(c_H2,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_G2 @ X50) = X50)))).
thf(c_H3,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_F3 @ X50) = ((add_5FSNo @ X50) @ X50))))).
thf(c_H4,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_G3 @ X50) = X50)))).
thf(c_H5,axiom,(c_H3 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H6,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U3 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51))))))))).
thf(c_H7,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_V3 @ X50) = ((c_U3 @ (c_G3 @ X50)) @ c_H3))))).
thf(c_H8,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_H2 @ X50) = ((add_5FSNo @ (c_V3 @ X50)) @ (minus_5FSNo @ (ordsucc @ c_Empty))))))).
thf(c_H9,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U2 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ (c_F2 @ ((c_U2 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51))))))))).
thf(c_H10,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_V2 @ X50) = ((c_U2 @ (c_G2 @ X50)) @ (c_H2 @ X50)))))).
thf(c_H11,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_F1 @ X50) = (c_V2 @ X50))))).
thf(c_H12,axiom,(c_G1 = (ordsucc @ c_Empty))).
thf(c_H13,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_H1 @ X50) @ X51) = X51)))))).
thf(c_H14,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U1 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51))))))))).
thf(c_H15,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_V1 @ X50) @ X51) = ((c_U1 @ c_G1) @ ((c_H1 @ X50) @ X51)))))))).
thf(c_H16,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_F4 @ X50) @ X51) = ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X51)) @ X50))))))).
thf(c_H17,axiom,(c_G4 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H18,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_H4 @ X50) = X50)))).
thf(c_H19,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U4 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ ((c_F4 @ ((c_U4 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51)) @ X50)))))))).
thf(c_H20,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_V4 @ X50) = ((c_U4 @ c_G4) @ (c_H4 @ X50)))))).
thf(c_H21,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_F0 @ X50) @ X51) = ((add_5FSNo @ ((c_V1 @ X50) @ X51)) @ ((add_5FSNo @ (c_V4 @ X50)) @ (minus_5FSNo @ X50))))))))).
thf(c_H22,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_G0 @ X50) = X50)))).
thf(c_H23,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H24,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U0 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51)) @ X50)))))))).
thf(c_H25,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_V0 @ X50) = ((c_U0 @ (c_G0 @ X50)) @ c_H0))))).
thf(c_H26,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_SMALL @ X50) = (c_V0 @ X50))))).
thf(c_H27,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_F7 @ X50) = ((add_5FSNo @ X50) @ X50))))).
thf(c_H28,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_G7 @ X50) = X50)))).
thf(c_H29,axiom,(c_H7 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H30,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U7 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ (c_F7 @ ((c_U7 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51))))))))).
thf(c_H31,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_V7 @ X50) = ((c_U7 @ (c_G7 @ X50)) @ c_H7))))).
thf(c_H32,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_F8 @ X50) @ X51) = ((mul_5FSNo @ X50) @ X51))))))).
thf(c_H33,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_G8 @ X50) @ X51) = X51)))))).
thf(c_H34,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_H8 @ X50) = X50)))).
thf(c_H35,axiom,(c_I8 = (ordsucc @ c_Empty))).
thf(c_H36,axiom,(c_J8 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))).
thf(c_H37,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (! [X52:$i] : (((c_In @ X52) @ int) => ((((c_U8 @ X50) @ X51) @ X52) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ ((c_F8 @ (((c_U8 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51) @ X52)) @ (((c_V8 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51) @ X52))))))))))).
thf(c_H38,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (! [X52:$i] : (((c_In @ X52) @ int) => ((((c_V8 @ X50) @ X51) @ X52) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X52) @ ((c_G8 @ (((c_U8 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51) @ X52)) @ (((c_V8 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51) @ X52))))))))))).
thf(c_H39,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_W8 @ X50) = (((c_U8 @ (c_H8 @ X50)) @ c_I8) @ c_J8))))).
thf(c_H40,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_F6 @ X50) = ((mul_5FSNo @ ((add_5FSNo @ (c_V7 @ X50)) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ (c_W8 @ X50)))))).
thf(c_H41,axiom,(c_G6 = (ordsucc @ c_Empty))).
thf(c_H42,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_H6 @ X50) @ X51) = X51)))))).
thf(c_H43,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U6 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ (c_F6 @ ((c_U6 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51))))))))).
thf(c_H44,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_V6 @ X50) @ X51) = ((c_U6 @ c_G6) @ ((c_H6 @ X50) @ X51)))))))).
thf(c_H45,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_F5 @ X50) @ X51) = ((add_5FSNo @ ((add_5FSNo @ ((c_V6 @ X50) @ X51)) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X50) @ X50))) @ X50)))) @ X50))))))).
thf(c_H46,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_G5 @ X50) = X50)))).
thf(c_H47,axiom,(c_H5 = (ordsucc @ c_Empty))).
thf(c_H48,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => (! [X51:$i] : (((c_In @ X51) @ int) => (((c_U5 @ X50) @ X51) = (((c_If_5Fi @ ((c_SNoLe @ X50) @ c_Empty)) @ X51) @ ((c_F5 @ ((c_U5 @ ((add_5FSNo @ X50) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X51)) @ X50)))))))).
thf(c_H49,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_V5 @ X50) = ((c_U5 @ (c_G5 @ X50)) @ c_H5))))).
thf(c_H50,axiom,(! [X50:$i] : (((c_In @ X50) @ int) => ((c_FAST @ X50) = (c_V5 @ X50))))).
thf(a20567,conjecture,(! [X50:$i] : (((c_In @ X50) @ int) => (((c_SNoLe @ c_Empty) @ X50) => ((c_SMALL @ X50) = (c_FAST @ X50)))))).
