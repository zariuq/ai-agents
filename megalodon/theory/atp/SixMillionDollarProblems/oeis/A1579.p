% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A1579.mg.html#A1579
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > $i))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : ($i > $i))).
thf(c_H1_tp,type,(c_H1 : $i)).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > $i))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > ($i > $i)))).
thf(c_G3_tp,type,(c_G3 : ($i > ($i > $i)))).
thf(c_H3_tp,type,(c_H3 : ($i > $i))).
thf(c_I3_tp,type,(c_I3 : $i)).
thf(c_J3_tp,type,(c_J3 : $i)).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > ($i > $i))))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > ($i > $i))))).
thf(c_W3_tp,type,(c_W3 : ($i > $i))).
thf(c_F4_tp,type,(c_F4 : ($i > ($i > $i)))).
thf(c_G4_tp,type,(c_G4 : ($i > ($i > $i)))).
thf(c_H4_tp,type,(c_H4 : ($i > $i))).
thf(c_F5_tp,type,(c_F5 : ($i > $i))).
thf(c_G5_tp,type,(c_G5 : ($i > $i))).
thf(c_H5_tp,type,(c_H5 : $i)).
thf(c_U5_tp,type,(c_U5 : ($i > ($i > $i)))).
thf(c_V5_tp,type,(c_V5 : ($i > $i))).
thf(c_I4_tp,type,(c_I4 : ($i > $i))).
thf(c_J4_tp,type,(c_J4 : $i)).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > ($i > $i))))).
thf(c_V4_tp,type,(c_V4 : ($i > ($i > ($i > $i))))).
thf(c_W4_tp,type,(c_W4 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_F0 @ X38)) @ int)))).
thf(c_HG0,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_G0 @ X38)) @ int)))).
thf(c_HF1,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_F1 @ X38)) @ int)))).
thf(c_HG1,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_G1 @ X38)) @ int)))).
thf(c_HH1,axiom,((c_In @ c_H1) @ int)).
thf(c_HU1,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_U1 @ X38) @ X39)) @ int)))))).
thf(c_HV1,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_V1 @ X38)) @ int)))).
thf(c_HH0,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_H0 @ X38)) @ int)))).
thf(c_HU0,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_U0 @ X38) @ X39)) @ int)))))).
thf(c_HV0,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_V0 @ X38)) @ int)))).
thf(c_HF2,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_F2 @ X38)) @ int)))).
thf(c_HG2,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_G2 @ X38)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_U2 @ X38) @ X39)) @ int)))))).
thf(c_HV2,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_V2 @ X38)) @ int)))).
thf(c_HSMALL,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_SMALL @ X38)) @ int)))).
thf(c_HF3,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_F3 @ X38) @ X39)) @ int)))))).
thf(c_HG3,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_G3 @ X38) @ X39)) @ int)))))).
thf(c_HH3,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_H3 @ X38)) @ int)))).
thf(c_HI3,axiom,((c_In @ c_I3) @ int)).
thf(c_HJ3,axiom,((c_In @ c_J3) @ int)).
thf(c_HU3,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((c_In @ (((c_U3 @ X38) @ X39) @ X40)) @ int)))))))).
thf(c_HV3,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((c_In @ (((c_V3 @ X38) @ X39) @ X40)) @ int)))))))).
thf(c_HW3,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_W3 @ X38)) @ int)))).
thf(c_HF4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_F4 @ X38) @ X39)) @ int)))))).
thf(c_HG4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_G4 @ X38) @ X39)) @ int)))))).
thf(c_HH4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_H4 @ X38)) @ int)))).
thf(c_HF5,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_F5 @ X38)) @ int)))).
thf(c_HG5,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_G5 @ X38)) @ int)))).
thf(c_HH5,axiom,((c_In @ c_H5) @ int)).
thf(c_HU5,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => ((c_In @ ((c_U5 @ X38) @ X39)) @ int)))))).
thf(c_HV5,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_V5 @ X38)) @ int)))).
thf(c_HI4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_I4 @ X38)) @ int)))).
thf(c_HJ4,axiom,((c_In @ c_J4) @ int)).
thf(c_HU4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((c_In @ (((c_U4 @ X38) @ X39) @ X40)) @ int)))))))).
thf(c_HV4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((c_In @ (((c_V4 @ X38) @ X39) @ X40)) @ int)))))))).
thf(c_HW4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_W4 @ X38)) @ int)))).
thf(c_HFAST,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_In @ (c_FAST @ X38)) @ int)))).
thf(c_H1,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_F0 @ X38) = ((add_5FSNo @ ((add_5FSNo @ X38) @ X38)) @ X38))))).
thf(c_H2,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_G0 @ X38) = X38)))).
thf(c_H3,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_F1 @ X38) = ((add_5FSNo @ X38) @ X38))))).
thf(c_H4,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_G1 @ X38) = X38)))).
thf(c_H5,axiom,(c_H1 = (ordsucc @ c_Empty))).
thf(c_H6,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_U1 @ X38) @ X39) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X39) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39))))))))).
thf(c_H7,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_V1 @ X38) = ((c_U1 @ (c_G1 @ X38)) @ c_H1))))).
thf(c_H8,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_H0 @ X38) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (c_V1 @ X38)))))).
thf(c_H9,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_U0 @ X38) @ X39) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X39) @ (c_F0 @ ((c_U0 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39))))))))).
thf(c_H10,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_V0 @ X38) = ((c_U0 @ (c_G0 @ X38)) @ (c_H0 @ X38)))))).
thf(c_H11,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_F2 @ X38) = ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X38) @ X38))) @ X38))))).
thf(c_H12,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_G2 @ X38) = X38)))).
thf(c_H13,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H14,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_U2 @ X38) @ X39) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X39) @ (c_F2 @ ((c_U2 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39))))))))).
thf(c_H15,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_V2 @ X38) = ((c_U2 @ (c_G2 @ X38)) @ c_H2))))).
thf(c_H16,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_SMALL @ X38) = ((add_5FSNo @ (c_V0 @ X38)) @ (c_V2 @ X38)))))).
thf(c_H17,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_F3 @ X38) @ X39) = ((mul_5FSNo @ X38) @ X39))))))).
thf(c_H18,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_G3 @ X38) @ X39) = X39)))))).
thf(c_H19,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_H3 @ X38) = X38)))).
thf(c_H20,axiom,(c_I3 = (ordsucc @ c_Empty))).
thf(c_H21,axiom,(c_J3 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))).
thf(c_H22,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((((c_U3 @ X38) @ X39) @ X40) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X39) @ ((c_F3 @ (((c_U3 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40)) @ (((c_V3 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40))))))))))).
thf(c_H23,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((((c_V3 @ X38) @ X39) @ X40) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X40) @ ((c_G3 @ (((c_U3 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40)) @ (((c_V3 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40))))))))))).
thf(c_H24,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_W3 @ X38) = (((c_U3 @ (c_H3 @ X38)) @ c_I3) @ c_J3))))).
thf(c_H25,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_F4 @ X38) @ X39) = ((mul_5FSNo @ X38) @ X39))))))).
thf(c_H26,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_G4 @ X38) @ X39) = X39)))))).
thf(c_H27,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_H4 @ X38) = X38)))).
thf(c_H28,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_F5 @ X38) = ((add_5FSNo @ X38) @ X38))))).
thf(c_H29,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_G5 @ X38) = X38)))).
thf(c_H30,axiom,(c_H5 = (ordsucc @ c_Empty))).
thf(c_H31,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (((c_U5 @ X38) @ X39) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X39) @ (c_F5 @ ((c_U5 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39))))))))).
thf(c_H32,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_V5 @ X38) = ((c_U5 @ (c_G5 @ X38)) @ c_H5))))).
thf(c_H33,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_I4 @ X38) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (c_V5 @ X38)))))).
thf(c_H34,axiom,(c_J4 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ (ordsucc @ (ordsucc @ c_Empty))))).
thf(c_H35,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((((c_U4 @ X38) @ X39) @ X40) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X39) @ ((c_F4 @ (((c_U4 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40)) @ (((c_V4 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40))))))))))).
thf(c_H36,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => (! [X39:$i] : (((c_In @ X39) @ int) => (! [X40:$i] : (((c_In @ X40) @ int) => ((((c_V4 @ X38) @ X39) @ X40) = (((c_If_5Fi @ ((c_SNoLe @ X38) @ c_Empty)) @ X40) @ ((c_G4 @ (((c_U4 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40)) @ (((c_V4 @ ((add_5FSNo @ X38) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X39) @ X40))))))))))).
thf(c_H37,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_W4 @ X38) = (((c_U4 @ (c_H4 @ X38)) @ (c_I4 @ X38)) @ c_J4))))).
thf(c_H38,axiom,(! [X38:$i] : (((c_In @ X38) @ int) => ((c_FAST @ X38) = ((add_5FSNo @ (c_W3 @ X38)) @ (c_W4 @ X38)))))).
thf(a1579,conjecture,(! [X38:$i] : (((c_In @ X38) @ int) => (((c_SNoLe @ c_Empty) @ X38) => ((c_SMALL @ X38) = (c_FAST @ X38)))))).
