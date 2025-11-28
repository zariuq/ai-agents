% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A74546.mg.html#A74546
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > $i))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : $i)).
thf(c_F2_tp,type,(c_F2 : ($i > $i))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_H1_tp,type,(c_H1 : ($i > $i))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > $i))).
thf(c_G3_tp,type,(c_G3 : $i)).
thf(c_F4_tp,type,(c_F4 : ($i > $i))).
thf(c_G4_tp,type,(c_G4 : ($i > $i))).
thf(c_H4_tp,type,(c_H4 : $i)).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > $i)))).
thf(c_V4_tp,type,(c_V4 : ($i > $i))).
thf(c_H3_tp,type,(c_H3 : ($i > $i))).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > $i))).
thf(c_F5_tp,type,(c_F5 : ($i > ($i > $i)))).
thf(c_G5_tp,type,(c_G5 : ($i > ($i > $i)))).
thf(c_H5_tp,type,(c_H5 : ($i > $i))).
thf(c_I5_tp,type,(c_I5 : $i)).
thf(c_J5_tp,type,(c_J5 : $i)).
thf(c_U5_tp,type,(c_U5 : ($i > ($i > ($i > $i))))).
thf(c_V5_tp,type,(c_V5 : ($i > ($i > ($i > $i))))).
thf(c_W5_tp,type,(c_W5 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_F0 @ X35)) @ int)))).
thf(c_HG0,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_G0 @ X35)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ ((c_U0 @ X35) @ X36)) @ int)))))).
thf(c_HV0,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_V0 @ X35)) @ int)))).
thf(c_HF1,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_F1 @ X35)) @ int)))).
thf(c_HG1,axiom,((c_In @ c_G1) @ int)).
thf(c_HF2,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_F2 @ X35)) @ int)))).
thf(c_HG2,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_G2 @ X35)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ ((c_U2 @ X35) @ X36)) @ int)))))).
thf(c_HV2,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_V2 @ X35)) @ int)))).
thf(c_HH1,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_H1 @ X35)) @ int)))).
thf(c_HU1,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ ((c_U1 @ X35) @ X36)) @ int)))))).
thf(c_HV1,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_V1 @ X35)) @ int)))).
thf(c_HSMALL,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_SMALL @ X35)) @ int)))).
thf(c_HF3,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_F3 @ X35)) @ int)))).
thf(c_HG3,axiom,((c_In @ c_G3) @ int)).
thf(c_HF4,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_F4 @ X35)) @ int)))).
thf(c_HG4,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_G4 @ X35)) @ int)))).
thf(c_HH4,axiom,((c_In @ c_H4) @ int)).
thf(c_HU4,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ ((c_U4 @ X35) @ X36)) @ int)))))).
thf(c_HV4,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_V4 @ X35)) @ int)))).
thf(c_HH3,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_H3 @ X35)) @ int)))).
thf(c_HU3,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ ((c_U3 @ X35) @ X36)) @ int)))))).
thf(c_HV3,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_V3 @ X35)) @ int)))).
thf(c_HF5,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ ((c_F5 @ X35) @ X36)) @ int)))))).
thf(c_HG5,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ ((c_G5 @ X35) @ X36)) @ int)))))).
thf(c_HH5,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_H5 @ X35)) @ int)))).
thf(c_HI5,axiom,((c_In @ c_I5) @ int)).
thf(c_HJ5,axiom,((c_In @ c_J5) @ int)).
thf(c_HU5,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ (((c_U5 @ X35) @ X36) @ X37)) @ int)))))))).
thf(c_HV5,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ (((c_V5 @ X35) @ X36) @ X37)) @ int)))))))).
thf(c_HW5,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_W5 @ X35)) @ int)))).
thf(c_HFAST,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_In @ (c_FAST @ X35)) @ int)))).
thf(c_H1,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_F0 @ X35) = ((add_5FSNo @ ((add_5FSNo @ X35) @ X35)) @ X35))))).
thf(c_H2,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_G0 @ X35) = ((add_5FSNo @ X35) @ X35))))).
thf(c_H3,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H4,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (((c_U0 @ X35) @ X36) = (((c_If_5Fi @ ((c_SNoLe @ X35) @ c_Empty)) @ X36) @ (c_F0 @ ((c_U0 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36))))))))).
thf(c_H5,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_V0 @ X35) = ((c_U0 @ (c_G0 @ X35)) @ c_H0))))).
thf(c_H6,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_F1 @ X35) = ((add_5FSNo @ ((mul_5FSNo @ ((mul_5FSNo @ X35) @ X35)) @ X35)) @ X35))))).
thf(c_H7,axiom,(c_G1 = (ordsucc @ c_Empty))).
thf(c_H8,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_F2 @ X35) = ((add_5FSNo @ X35) @ X35))))).
thf(c_H9,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_G2 @ X35) = X35)))).
thf(c_H10,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H11,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (((c_U2 @ X35) @ X36) = (((c_If_5Fi @ ((c_SNoLe @ X35) @ c_Empty)) @ X36) @ (c_F2 @ ((c_U2 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36))))))))).
thf(c_H12,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_V2 @ X35) = ((c_U2 @ (c_G2 @ X35)) @ c_H2))))).
thf(c_H13,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_H1 @ X35) = (c_V2 @ X35))))).
thf(c_H14,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (((c_U1 @ X35) @ X36) = (((c_If_5Fi @ ((c_SNoLe @ X35) @ c_Empty)) @ X36) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36))))))))).
thf(c_H15,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_V1 @ X35) = ((c_U1 @ c_G1) @ (c_H1 @ X35)))))).
thf(c_H16,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_SMALL @ X35) = ((add_5FSNo @ (c_V0 @ X35)) @ (c_V1 @ X35)))))).
thf(c_H17,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_F3 @ X35) = ((add_5FSNo @ ((mul_5FSNo @ ((mul_5FSNo @ X35) @ X35)) @ X35)) @ X35))))).
thf(c_H18,axiom,(c_G3 = (ordsucc @ c_Empty))).
thf(c_H19,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_F4 @ X35) = ((add_5FSNo @ X35) @ X35))))).
thf(c_H20,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_G4 @ X35) = X35)))).
thf(c_H21,axiom,(c_H4 = (ordsucc @ c_Empty))).
thf(c_H22,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (((c_U4 @ X35) @ X36) = (((c_If_5Fi @ ((c_SNoLe @ X35) @ c_Empty)) @ X36) @ (c_F4 @ ((c_U4 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36))))))))).
thf(c_H23,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_V4 @ X35) = ((c_U4 @ (c_G4 @ X35)) @ c_H4))))).
thf(c_H24,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_H3 @ X35) = (c_V4 @ X35))))).
thf(c_H25,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (((c_U3 @ X35) @ X36) = (((c_If_5Fi @ ((c_SNoLe @ X35) @ c_Empty)) @ X36) @ (c_F3 @ ((c_U3 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36))))))))).
thf(c_H26,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_V3 @ X35) = ((c_U3 @ c_G3) @ (c_H3 @ X35)))))).
thf(c_H27,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (((c_F5 @ X35) @ X36) = ((mul_5FSNo @ X35) @ X36))))))).
thf(c_H28,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (((c_G5 @ X35) @ X36) = X36)))))).
thf(c_H29,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_H5 @ X35) = X35)))).
thf(c_H30,axiom,(c_I5 = (ordsucc @ c_Empty))).
thf(c_H31,axiom,(c_J5 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty))))))).
thf(c_H32,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((((c_U5 @ X35) @ X36) @ X37) = (((c_If_5Fi @ ((c_SNoLe @ X35) @ c_Empty)) @ X36) @ ((c_F5 @ (((c_U5 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36) @ X37)) @ (((c_V5 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36) @ X37))))))))))).
thf(c_H33,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => (! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((((c_V5 @ X35) @ X36) @ X37) = (((c_If_5Fi @ ((c_SNoLe @ X35) @ c_Empty)) @ X37) @ ((c_G5 @ (((c_U5 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36) @ X37)) @ (((c_V5 @ ((add_5FSNo @ X35) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X36) @ X37))))))))))).
thf(c_H34,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_W5 @ X35) = (((c_U5 @ (c_H5 @ X35)) @ c_I5) @ c_J5))))).
thf(c_H35,axiom,(! [X35:$i] : (((c_In @ X35) @ int) => ((c_FAST @ X35) = ((add_5FSNo @ (c_V3 @ X35)) @ (c_W5 @ X35)))))).
thf(a74546,conjecture,(! [X35:$i] : (((c_In @ X35) @ int) => (((c_SNoLe @ c_Empty) @ X35) => ((c_SMALL @ X35) = (c_FAST @ X35)))))).
