% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A254641.mg.html#A254641
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : $i)).
thf(c_H3_tp,type,(c_H3 : ($i > ($i > $i)))).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > $i)))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > ($i > $i)))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > ($i > $i)))).
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > ($i > $i)))).
thf(c_H1_tp,type,(c_H1 : ($i > $i))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > $i)))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F7_tp,type,(c_F7 : ($i > $i))).
thf(c_G7_tp,type,(c_G7 : $i)).
thf(c_H7_tp,type,(c_H7 : ($i > ($i > $i)))).
thf(c_U7_tp,type,(c_U7 : ($i > ($i > $i)))).
thf(c_V7_tp,type,(c_V7 : ($i > ($i > $i)))).
thf(c_F6_tp,type,(c_F6 : ($i > ($i > $i)))).
thf(c_G6_tp,type,(c_G6 : ($i > ($i > $i)))).
thf(c_H6_tp,type,(c_H6 : ($i > $i))).
thf(c_U6_tp,type,(c_U6 : ($i > ($i > $i)))).
thf(c_V6_tp,type,(c_V6 : ($i > ($i > $i)))).
thf(c_F5_tp,type,(c_F5 : ($i > ($i > $i)))).
thf(c_G5_tp,type,(c_G5 : ($i > ($i > $i)))).
thf(c_H5_tp,type,(c_H5 : ($i > $i))).
thf(c_U5_tp,type,(c_U5 : ($i > ($i > $i)))).
thf(c_V5_tp,type,(c_V5 : ($i > ($i > $i)))).
thf(c_F4_tp,type,(c_F4 : ($i > ($i > $i)))).
thf(c_G4_tp,type,(c_G4 : ($i > $i))).
thf(c_H4_tp,type,(c_H4 : $i)).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > $i)))).
thf(c_V4_tp,type,(c_V4 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF3,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_F3 @ X42)) @ int)))).
thf(c_HG3,axiom,((c_In @ c_G3) @ int)).
thf(c_HH3,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_H3 @ X42) @ X43)) @ int)))))).
thf(c_HU3,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U3 @ X42) @ X43)) @ int)))))).
thf(c_HV3,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_V3 @ X42) @ X43)) @ int)))))).
thf(c_HF2,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_F2 @ X42) @ X43)) @ int)))))).
thf(c_HG2,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_G2 @ X42) @ X43)) @ int)))))).
thf(c_HH2,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_H2 @ X42)) @ int)))).
thf(c_HU2,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U2 @ X42) @ X43)) @ int)))))).
thf(c_HV2,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_V2 @ X42) @ X43)) @ int)))))).
thf(c_HF1,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_F1 @ X42) @ X43)) @ int)))))).
thf(c_HG1,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_G1 @ X42) @ X43)) @ int)))))).
thf(c_HH1,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_H1 @ X42)) @ int)))).
thf(c_HU1,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U1 @ X42) @ X43)) @ int)))))).
thf(c_HV1,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_V1 @ X42) @ X43)) @ int)))))).
thf(c_HF0,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_F0 @ X42) @ X43)) @ int)))))).
thf(c_HG0,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_G0 @ X42)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U0 @ X42) @ X43)) @ int)))))).
thf(c_HV0,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_V0 @ X42)) @ int)))).
thf(c_HSMALL,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_SMALL @ X42)) @ int)))).
thf(c_HF7,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_F7 @ X42)) @ int)))).
thf(c_HG7,axiom,((c_In @ c_G7) @ int)).
thf(c_HH7,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_H7 @ X42) @ X43)) @ int)))))).
thf(c_HU7,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U7 @ X42) @ X43)) @ int)))))).
thf(c_HV7,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_V7 @ X42) @ X43)) @ int)))))).
thf(c_HF6,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_F6 @ X42) @ X43)) @ int)))))).
thf(c_HG6,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_G6 @ X42) @ X43)) @ int)))))).
thf(c_HH6,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_H6 @ X42)) @ int)))).
thf(c_HU6,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U6 @ X42) @ X43)) @ int)))))).
thf(c_HV6,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_V6 @ X42) @ X43)) @ int)))))).
thf(c_HF5,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_F5 @ X42) @ X43)) @ int)))))).
thf(c_HG5,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_G5 @ X42) @ X43)) @ int)))))).
thf(c_HH5,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_H5 @ X42)) @ int)))).
thf(c_HU5,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U5 @ X42) @ X43)) @ int)))))).
thf(c_HV5,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_V5 @ X42) @ X43)) @ int)))))).
thf(c_HF4,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_F4 @ X42) @ X43)) @ int)))))).
thf(c_HG4,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_G4 @ X42)) @ int)))).
thf(c_HH4,axiom,((c_In @ c_H4) @ int)).
thf(c_HU4,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => ((c_In @ ((c_U4 @ X42) @ X43)) @ int)))))).
thf(c_HV4,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_V4 @ X42)) @ int)))).
thf(c_HFAST,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_In @ (c_FAST @ X42)) @ int)))).
thf(c_H1,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_F3 @ X42) = ((mul_5FSNo @ X42) @ X42))))).
thf(c_H2,axiom,(c_G3 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H3,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_H3 @ X42) @ X43) = X43)))))).
thf(c_H4,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U3 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43))))))))).
thf(c_H5,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_V3 @ X42) @ X43) = ((c_U3 @ c_G3) @ ((c_H3 @ X42) @ X43)))))))).
thf(c_H6,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_F2 @ X42) @ X43) = ((add_5FSNo @ ((mul_5FSNo @ ((mul_5FSNo @ ((mul_5FSNo @ ((c_V3 @ X42) @ X43)) @ X43)) @ X43)) @ X43)) @ X42))))))).
thf(c_H7,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_G2 @ X42) @ X43) = X43)))))).
thf(c_H8,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_H2 @ X42) = X42)))).
thf(c_H9,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U2 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ ((c_F2 @ ((c_U2 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43)) @ X42)))))))).
thf(c_H10,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_V2 @ X42) @ X43) = ((c_U2 @ ((c_G2 @ X42) @ X43)) @ (c_H2 @ X42)))))))).
thf(c_H11,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_F1 @ X42) @ X43) = ((c_V2 @ X42) @ X43))))))).
thf(c_H12,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_G1 @ X42) @ X43) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X43))))))).
thf(c_H13,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_H1 @ X42) = X42)))).
thf(c_H14,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U1 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ ((c_F1 @ ((c_U1 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43)) @ X42)))))))).
thf(c_H15,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_V1 @ X42) @ X43) = ((c_U1 @ ((c_G1 @ X42) @ X43)) @ (c_H1 @ X42)))))))).
thf(c_H16,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_F0 @ X42) @ X43) = ((c_V1 @ X42) @ X43))))))).
thf(c_H17,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_G0 @ X42) = X42)))).
thf(c_H18,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H19,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U0 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43)) @ X42)))))))).
thf(c_H20,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_V0 @ X42) = ((c_U0 @ (c_G0 @ X42)) @ c_H0))))).
thf(c_H21,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_SMALL @ X42) = (c_V0 @ X42))))).
thf(c_H22,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_F7 @ X42) = ((mul_5FSNo @ ((mul_5FSNo @ X42) @ X42)) @ X42))))).
thf(c_H23,axiom,(c_G7 = (ordsucc @ c_Empty))).
thf(c_H24,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_H7 @ X42) @ X43) = ((mul_5FSNo @ X43) @ X43))))))).
thf(c_H25,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U7 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ (c_F7 @ ((c_U7 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43))))))))).
thf(c_H26,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_V7 @ X42) @ X43) = ((c_U7 @ c_G7) @ ((c_H7 @ X42) @ X43)))))))).
thf(c_H27,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_F6 @ X42) @ X43) = ((add_5FSNo @ ((mul_5FSNo @ ((c_V7 @ X42) @ X43)) @ X43)) @ X42))))))).
thf(c_H28,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_G6 @ X42) @ X43) = X43)))))).
thf(c_H29,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_H6 @ X42) = X42)))).
thf(c_H30,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U6 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ ((c_F6 @ ((c_U6 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43)) @ X42)))))))).
thf(c_H31,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_V6 @ X42) @ X43) = ((c_U6 @ ((c_G6 @ X42) @ X43)) @ (c_H6 @ X42)))))))).
thf(c_H32,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_F5 @ X42) @ X43) = ((c_V6 @ X42) @ X43))))))).
thf(c_H33,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_G5 @ X42) @ X43) = X43)))))).
thf(c_H34,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_H5 @ X42) = X42)))).
thf(c_H35,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U5 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ ((c_F5 @ ((c_U5 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43)) @ X42)))))))).
thf(c_H36,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_V5 @ X42) @ X43) = ((c_U5 @ ((c_G5 @ X42) @ X43)) @ (c_H5 @ X42)))))))).
thf(c_H37,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_F4 @ X42) @ X43) = ((c_V5 @ X42) @ X43))))))).
thf(c_H38,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_G4 @ X42) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X42))))).
thf(c_H39,axiom,(c_H4 = c_Empty)).
thf(c_H40,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => (! [X43:$i] : (((c_In @ X43) @ int) => (((c_U4 @ X42) @ X43) = (((c_If_5Fi @ ((c_SNoLe @ X42) @ c_Empty)) @ X43) @ ((c_F4 @ ((c_U4 @ ((add_5FSNo @ X42) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X43)) @ X42)))))))).
thf(c_H41,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_V4 @ X42) = ((c_U4 @ (c_G4 @ X42)) @ c_H4))))).
thf(c_H42,axiom,(! [X42:$i] : (((c_In @ X42) @ int) => ((c_FAST @ X42) = (c_V4 @ X42))))).
thf(a254641,conjecture,(! [X42:$i] : (((c_In @ X42) @ int) => (((c_SNoLe @ c_Empty) @ X42) => ((c_SMALL @ X42) = (c_FAST @ X42)))))).
