% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A61787.mg.html#A61787
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
thf(c_F4_tp,type,(c_F4 : ($i > ($i > $i)))).
thf(c_G4_tp,type,(c_G4 : ($i > ($i > $i)))).
thf(c_H4_tp,type,(c_H4 : ($i > $i))).
thf(c_I4_tp,type,(c_I4 : $i)).
thf(c_J4_tp,type,(c_J4 : ($i > $i))).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > ($i > $i))))).
thf(c_V4_tp,type,(c_V4 : ($i > ($i > ($i > $i))))).
thf(c_W4_tp,type,(c_W4 : ($i > $i))).
thf(c_F5_tp,type,(c_F5 : ($i > ($i > $i)))).
thf(c_G5_tp,type,(c_G5 : ($i > ($i > $i)))).
thf(c_H5_tp,type,(c_H5 : ($i > $i))).
thf(c_I5_tp,type,(c_I5 : $i)).
thf(c_J5_tp,type,(c_J5 : ($i > $i))).
thf(c_U5_tp,type,(c_U5 : ($i > ($i > ($i > $i))))).
thf(c_V5_tp,type,(c_V5 : ($i > ($i > ($i > $i))))).
thf(c_W5_tp,type,(c_W5 : ($i > $i))).
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
thf(c_HF1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_F1 @ X44) @ X45)) @ int)))))).
thf(c_HG1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_G1 @ X44) @ X45)) @ int)))))).
thf(c_HH1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_H1 @ X44) @ X45)) @ int)))))).
thf(c_HI1,axiom,((c_In @ c_I1) @ int)).
thf(c_HJ1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_J1 @ X44) @ X45)) @ int)))))).
thf(c_HU1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_U1 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HV1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_V1 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HW1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_W1 @ X44) @ X45)) @ int)))))).
thf(c_HF0,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_F0 @ X44) @ X45)) @ int)))))).
thf(c_HG0,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_G0 @ X44) @ X45)) @ int)))))).
thf(c_HH0,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_H0 @ X44)) @ int)))).
thf(c_HI0,axiom,((c_In @ c_I0) @ int)).
thf(c_HJ0,axiom,((c_In @ c_J0) @ int)).
thf(c_HU0,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_U0 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HV0,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_V0 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HW0,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_W0 @ X44)) @ int)))).
thf(c_HSMALL,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_SMALL @ X44)) @ int)))).
thf(c_HF4,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_F4 @ X44) @ X45)) @ int)))))).
thf(c_HG4,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_G4 @ X44) @ X45)) @ int)))))).
thf(c_HH4,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_H4 @ X44)) @ int)))).
thf(c_HI4,axiom,((c_In @ c_I4) @ int)).
thf(c_HJ4,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_J4 @ X44)) @ int)))).
thf(c_HU4,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_U4 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HV4,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_V4 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HW4,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_W4 @ X44)) @ int)))).
thf(c_HF5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_F5 @ X44) @ X45)) @ int)))))).
thf(c_HG5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_G5 @ X44) @ X45)) @ int)))))).
thf(c_HH5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_H5 @ X44)) @ int)))).
thf(c_HI5,axiom,((c_In @ c_I5) @ int)).
thf(c_HJ5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_J5 @ X44)) @ int)))).
thf(c_HU5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_U5 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HV5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((c_In @ (((c_V5 @ X44) @ X45) @ X46)) @ int)))))))).
thf(c_HW5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_W5 @ X44)) @ int)))).
thf(c_HF3,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_F3 @ X44)) @ int)))).
thf(c_HG3,axiom,((c_In @ c_G3) @ int)).
thf(c_HH3,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_H3 @ X44) @ X45)) @ int)))))).
thf(c_HU3,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_U3 @ X44) @ X45)) @ int)))))).
thf(c_HV3,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_V3 @ X44) @ X45)) @ int)))))).
thf(c_HF2,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_F2 @ X44) @ X45)) @ int)))))).
thf(c_HG2,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_G2 @ X44)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => ((c_In @ ((c_U2 @ X44) @ X45)) @ int)))))).
thf(c_HV2,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_V2 @ X44)) @ int)))).
thf(c_HFAST,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_In @ (c_FAST @ X44)) @ int)))).
thf(c_H1,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_F1 @ X44) @ X45) = ((mul_5FSNo @ X44) @ X45))))))).
thf(c_H2,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_G1 @ X44) @ X45) = X45)))))).
thf(c_H3,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_H1 @ X44) @ X45) = X45)))))).
thf(c_H4,axiom,(c_I1 = (ordsucc @ c_Empty))).
thf(c_H5,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_J1 @ X44) @ X45) = X45)))))).
thf(c_H6,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_U1 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X45) @ ((c_F1 @ (((c_U1 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V1 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H7,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_V1 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X46) @ ((c_G1 @ (((c_U1 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V1 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H8,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_W1 @ X44) @ X45) = (((c_U1 @ ((c_H1 @ X44) @ X45)) @ c_I1) @ ((c_J1 @ X44) @ X45)))))))).
thf(c_H9,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_F0 @ X44) @ X45) = ((add_5FSNo @ ((c_W1 @ X44) @ X45)) @ X44))))))).
thf(c_H10,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_G0 @ X44) @ X45) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X45))))))).
thf(c_H11,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_H0 @ X44) = X44)))).
thf(c_H12,axiom,(c_I0 = (ordsucc @ c_Empty))).
thf(c_H13,axiom,(c_J0 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (ordsucc @ (ordsucc @ c_Empty))))).
thf(c_H14,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_U0 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X45) @ ((c_F0 @ (((c_U0 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V0 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H15,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_V0 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X46) @ ((c_G0 @ (((c_U0 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V0 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H16,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_W0 @ X44) = (((c_U0 @ (c_H0 @ X44)) @ c_I0) @ c_J0))))).
thf(c_H17,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_SMALL @ X44) = (c_W0 @ X44))))).
thf(c_H18,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_F4 @ X44) @ X45) = ((mul_5FSNo @ X44) @ X45))))))).
thf(c_H19,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_G4 @ X44) @ X45) = X45)))))).
thf(c_H20,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_H4 @ X44) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X44))))).
thf(c_H21,axiom,(c_I4 = (ordsucc @ c_Empty))).
thf(c_H22,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_J4 @ X44) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ X44) @ X44)))))).
thf(c_H23,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_U4 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X45) @ ((c_F4 @ (((c_U4 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V4 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H24,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_V4 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X46) @ ((c_G4 @ (((c_U4 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V4 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H25,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_W4 @ X44) = (((c_U4 @ (c_H4 @ X44)) @ c_I4) @ (c_J4 @ X44)))))).
thf(c_H26,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_F5 @ X44) @ X45) = ((mul_5FSNo @ X44) @ X45))))))).
thf(c_H27,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_G5 @ X44) @ X45) = X45)))))).
thf(c_H28,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_H5 @ X44) = X44)))).
thf(c_H29,axiom,(c_I5 = (ordsucc @ c_Empty))).
thf(c_H30,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_J5 @ X44) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ X44) @ X44)))))).
thf(c_H31,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_U5 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X45) @ ((c_F5 @ (((c_U5 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V5 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H32,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (! [X46:$i] : (((c_In @ X46) @ int) => ((((c_V5 @ X44) @ X45) @ X46) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X46) @ ((c_G5 @ (((c_U5 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46)) @ (((c_V5 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45) @ X46))))))))))).
thf(c_H33,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_W5 @ X44) = (((c_U5 @ (c_H5 @ X44)) @ c_I5) @ (c_J5 @ X44)))))).
thf(c_H34,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_F3 @ X44) = ((mul_5FSNo @ (c_W4 @ X44)) @ (c_W5 @ X44)))))).
thf(c_H35,axiom,(c_G3 = (ordsucc @ c_Empty))).
thf(c_H36,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_H3 @ X44) @ X45) = X45)))))).
thf(c_H37,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_U3 @ X44) @ X45) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X45) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45))))))))).
thf(c_H38,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_V3 @ X44) @ X45) = ((c_U3 @ c_G3) @ ((c_H3 @ X44) @ X45)))))))).
thf(c_H39,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_F2 @ X44) @ X45) = ((add_5FSNo @ ((c_V3 @ X44) @ X45)) @ X44))))))).
thf(c_H40,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_G2 @ X44) = X44)))).
thf(c_H41,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H42,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => (! [X45:$i] : (((c_In @ X45) @ int) => (((c_U2 @ X44) @ X45) = (((c_If_5Fi @ ((c_SNoLe @ X44) @ c_Empty)) @ X45) @ ((c_F2 @ ((c_U2 @ ((add_5FSNo @ X44) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X45)) @ X44)))))))).
thf(c_H43,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_V2 @ X44) = ((c_U2 @ (c_G2 @ X44)) @ c_H2))))).
thf(c_H44,axiom,(! [X44:$i] : (((c_In @ X44) @ int) => ((c_FAST @ X44) = (c_V2 @ X44))))).
thf(a61787,conjecture,(! [X44:$i] : (((c_In @ X44) @ int) => (((c_SNoLe @ c_Empty) @ X44) => ((c_SMALL @ X44) = (c_FAST @ X44)))))).
