% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A36363.mg.html#A36363
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : $i)).
thf(c_H1_tp,type,(c_H1 : ($i > ($i > $i)))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > $i)))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > ($i > $i)))).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_I0_tp,type,(c_I0 : $i)).
thf(c_J0_tp,type,(c_J0 : ($i > $i))).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > ($i > $i))))).
thf(c_V0_tp,type,(c_V0 : ($i > ($i > ($i > $i))))).
thf(c_W0_tp,type,(c_W0 : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > ($i > $i)))).
thf(c_G3_tp,type,(c_G3 : ($i > ($i > $i)))).
thf(c_H3_tp,type,(c_H3 : ($i > $i))).
thf(c_I3_tp,type,(c_I3 : $i)).
thf(c_J3_tp,type,(c_J3 : ($i > $i))).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > ($i > $i))))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > ($i > $i))))).
thf(c_W3_tp,type,(c_W3 : ($i > $i))).
thf(c_F4_tp,type,(c_F4 : ($i > ($i > $i)))).
thf(c_G4_tp,type,(c_G4 : ($i > ($i > $i)))).
thf(c_H4_tp,type,(c_H4 : ($i > $i))).
thf(c_I4_tp,type,(c_I4 : $i)).
thf(c_J4_tp,type,(c_J4 : ($i > $i))).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > ($i > $i))))).
thf(c_V4_tp,type,(c_V4 : ($i > ($i > ($i > $i))))).
thf(c_W4_tp,type,(c_W4 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF1,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_F1 @ X36)) @ int)))).
thf(c_HG1,axiom,((c_In @ c_G1) @ int)).
thf(c_HH1,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_H1 @ X36) @ X37)) @ int)))))).
thf(c_HU1,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_U1 @ X36) @ X37)) @ int)))))).
thf(c_HV1,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_V1 @ X36) @ X37)) @ int)))))).
thf(c_HF0,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_F0 @ X36) @ X37)) @ int)))))).
thf(c_HG0,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_G0 @ X36) @ X37)) @ int)))))).
thf(c_HH0,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_H0 @ X36)) @ int)))).
thf(c_HI0,axiom,((c_In @ c_I0) @ int)).
thf(c_HJ0,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_J0 @ X36)) @ int)))).
thf(c_HU0,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (((c_U0 @ X36) @ X37) @ X38)) @ int)))))))).
thf(c_HV0,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (((c_V0 @ X36) @ X37) @ X38)) @ int)))))))).
thf(c_HW0,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_W0 @ X36)) @ int)))).
thf(c_HF2,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_F2 @ X36) @ X37)) @ int)))))).
thf(c_HG2,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_G2 @ X36)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_U2 @ X36) @ X37)) @ int)))))).
thf(c_HV2,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_V2 @ X36)) @ int)))).
thf(c_HSMALL,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_SMALL @ X36)) @ int)))).
thf(c_HF3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_F3 @ X36) @ X37)) @ int)))))).
thf(c_HG3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_G3 @ X36) @ X37)) @ int)))))).
thf(c_HH3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_H3 @ X36)) @ int)))).
thf(c_HI3,axiom,((c_In @ c_I3) @ int)).
thf(c_HJ3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_J3 @ X36)) @ int)))).
thf(c_HU3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (((c_U3 @ X36) @ X37) @ X38)) @ int)))))))).
thf(c_HV3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (((c_V3 @ X36) @ X37) @ X38)) @ int)))))))).
thf(c_HW3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_W3 @ X36)) @ int)))).
thf(c_HF4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_F4 @ X36) @ X37)) @ int)))))).
thf(c_HG4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => ((c_In @ ((c_G4 @ X36) @ X37)) @ int)))))).
thf(c_HH4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_H4 @ X36)) @ int)))).
thf(c_HI4,axiom,((c_In @ c_I4) @ int)).
thf(c_HJ4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_J4 @ X36)) @ int)))).
thf(c_HU4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (((c_U4 @ X36) @ X37) @ X38)) @ int)))))))).
thf(c_HV4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (((c_V4 @ X36) @ X37) @ X38)) @ int)))))))).
thf(c_HW4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_W4 @ X36)) @ int)))).
thf(c_HFAST,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_In @ (c_FAST @ X36)) @ int)))).
thf(c_H1,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_F1 @ X36) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X36) @ X36)))))).
thf(c_H2,axiom,(c_G1 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H3,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_H1 @ X36) @ X37) = X37)))))).
thf(c_H4,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_U1 @ X36) @ X37) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X37) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37))))))))).
thf(c_H5,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_V1 @ X36) @ X37) = ((c_U1 @ c_G1) @ ((c_H1 @ X36) @ X37)))))))).
thf(c_H6,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_F0 @ X36) @ X37) = ((mul_5FSNo @ ((c_V1 @ X36) @ X37)) @ X36))))))).
thf(c_H7,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_G0 @ X36) @ X37) = X37)))))).
thf(c_H8,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_H0 @ X36) = X36)))).
thf(c_H9,axiom,(c_I0 = (ordsucc @ c_Empty))).
thf(c_H10,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_J0 @ X36) = X36)))).
thf(c_H11,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((((c_U0 @ X36) @ X37) @ X38) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X37) @ ((c_F0 @ (((c_U0 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38)) @ (((c_V0 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38))))))))))).
thf(c_H12,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((((c_V0 @ X36) @ X37) @ X38) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X38) @ ((c_G0 @ (((c_U0 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38)) @ (((c_V0 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38))))))))))).
thf(c_H13,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_W0 @ X36) = (((c_U0 @ (c_H0 @ X36)) @ c_I0) @ (c_J0 @ X36)))))).
thf(c_H14,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_F2 @ X36) @ X37) = ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X37))) @ X36))))))).
thf(c_H15,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_G2 @ X36) = X36)))).
thf(c_H16,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H17,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_U2 @ X36) @ X37) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X37) @ ((c_F2 @ ((c_U2 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37)) @ X36)))))))).
thf(c_H18,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_V2 @ X36) = ((c_U2 @ (c_G2 @ X36)) @ c_H2))))).
thf(c_H19,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_SMALL @ X36) = ((mul_5FSNo @ (c_W0 @ X36)) @ (c_V2 @ X36)))))).
thf(c_H20,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_F3 @ X36) @ X37) = ((mul_5FSNo @ X36) @ X37))))))).
thf(c_H21,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_G3 @ X36) @ X37) = X37)))))).
thf(c_H22,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_H3 @ X36) = X36)))).
thf(c_H23,axiom,(c_I3 = (ordsucc @ c_Empty))).
thf(c_H24,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_J3 @ X36) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X36) @ X36))))))).
thf(c_H25,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((((c_U3 @ X36) @ X37) @ X38) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X37) @ ((c_F3 @ (((c_U3 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38)) @ (((c_V3 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38))))))))))).
thf(c_H26,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((((c_V3 @ X36) @ X37) @ X38) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X38) @ ((c_G3 @ (((c_U3 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38)) @ (((c_V3 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38))))))))))).
thf(c_H27,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_W3 @ X36) = (((c_U3 @ (c_H3 @ X36)) @ c_I3) @ (c_J3 @ X36)))))).
thf(c_H28,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_F4 @ X36) @ X37) = ((mul_5FSNo @ X36) @ X37))))))).
thf(c_H29,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (((c_G4 @ X36) @ X37) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X37))))))).
thf(c_H30,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_H4 @ X36) = X36)))).
thf(c_H31,axiom,(c_I4 = (ordsucc @ c_Empty))).
thf(c_H32,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_J4 @ X36) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X36))))).
thf(c_H33,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((((c_U4 @ X36) @ X37) @ X38) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X37) @ ((c_F4 @ (((c_U4 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38)) @ (((c_V4 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38))))))))))).
thf(c_H34,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => (! [X37:$i] : (((c_In @ X37) @ int) => (! [X38:$i] : (((c_In @ X38) @ int) => ((((c_V4 @ X36) @ X37) @ X38) = (((c_If_5Fi @ ((c_SNoLe @ X36) @ c_Empty)) @ X38) @ ((c_G4 @ (((c_U4 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38)) @ (((c_V4 @ ((add_5FSNo @ X36) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X37) @ X38))))))))))).
thf(c_H35,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_W4 @ X36) = (((c_U4 @ (c_H4 @ X36)) @ c_I4) @ (c_J4 @ X36)))))).
thf(c_H36,axiom,(! [X36:$i] : (((c_In @ X36) @ int) => ((c_FAST @ X36) = ((mul_5FSNo @ ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ c_Empty)) @ X36)) @ (c_W3 @ X36))) @ (c_W4 @ X36)))))).
thf(a36363,conjecture,(! [X36:$i] : (((c_In @ X36) @ int) => (((c_SNoLe @ c_Empty) @ X36) => ((c_SMALL @ X36) = (c_FAST @ X36)))))).
