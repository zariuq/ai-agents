% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A10799.mg.html#A10799
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > ($i > $i)))).
thf(c_H1_tp,type,(c_H1 : $i)).
thf(c_I1_tp,type,(c_I1 : ($i > $i))).
thf(c_J1_tp,type,(c_J1 : ($i > ($i > $i)))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > ($i > $i))))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > ($i > $i))))).
thf(c_W1_tp,type,(c_W1 : ($i > ($i > $i)))).
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F3_tp,type,(c_F3 : ($i > ($i > $i)))).
thf(c_G3_tp,type,(c_G3 : $i)).
thf(c_H3_tp,type,(c_H3 : ($i > ($i > $i)))).
thf(c_U3_tp,type,(c_U3 : ($i > ($i > $i)))).
thf(c_V3_tp,type,(c_V3 : ($i > ($i > $i)))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : $i)).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_F4_tp,type,(c_F4 : ($i > ($i > $i)))).
thf(c_G4_tp,type,(c_G4 : ($i > $i))).
thf(c_H4_tp,type,(c_H4 : $i)).
thf(c_U4_tp,type,(c_U4 : ($i > ($i > $i)))).
thf(c_V4_tp,type,(c_V4 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_F1 @ X30) @ X31)) @ int)))))).
thf(c_HG1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_G1 @ X30) @ X31)) @ int)))))).
thf(c_HH1,axiom,((c_In @ c_H1) @ int)).
thf(c_HI1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_I1 @ X30)) @ int)))).
thf(c_HJ1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_J1 @ X30) @ X31)) @ int)))))).
thf(c_HU1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ (((c_U1 @ X30) @ X31) @ X32)) @ int)))))))).
thf(c_HV1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((c_In @ (((c_V1 @ X30) @ X31) @ X32)) @ int)))))))).
thf(c_HW1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_W1 @ X30) @ X31)) @ int)))))).
thf(c_HF0,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_F0 @ X30) @ X31)) @ int)))))).
thf(c_HG0,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_G0 @ X30)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_U0 @ X30) @ X31)) @ int)))))).
thf(c_HV0,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_V0 @ X30)) @ int)))).
thf(c_HSMALL,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_SMALL @ X30)) @ int)))).
thf(c_HF3,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_F3 @ X30) @ X31)) @ int)))))).
thf(c_HG3,axiom,((c_In @ c_G3) @ int)).
thf(c_HH3,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_H3 @ X30) @ X31)) @ int)))))).
thf(c_HU3,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_U3 @ X30) @ X31)) @ int)))))).
thf(c_HV3,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_V3 @ X30) @ X31)) @ int)))))).
thf(c_HF2,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_F2 @ X30) @ X31)) @ int)))))).
thf(c_HG2,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_G2 @ X30)) @ int)))).
thf(c_HH2,axiom,((c_In @ c_H2) @ int)).
thf(c_HU2,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_U2 @ X30) @ X31)) @ int)))))).
thf(c_HV2,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_V2 @ X30)) @ int)))).
thf(c_HF4,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_F4 @ X30) @ X31)) @ int)))))).
thf(c_HG4,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_G4 @ X30)) @ int)))).
thf(c_HH4,axiom,((c_In @ c_H4) @ int)).
thf(c_HU4,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => ((c_In @ ((c_U4 @ X30) @ X31)) @ int)))))).
thf(c_HV4,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_V4 @ X30)) @ int)))).
thf(c_HFAST,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_In @ (c_FAST @ X30)) @ int)))).
thf(c_H1,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_F1 @ X30) @ X31) = ((add_5FSNo @ ((mul_5FSNo @ X30) @ X31)) @ X30))))))).
thf(c_H2,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_G1 @ X30) @ X31) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X31))))))).
thf(c_H3,axiom,(c_H1 = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))).
thf(c_H4,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_I1 @ X30) = X30)))).
thf(c_H5,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_J1 @ X30) @ X31) = X31)))))).
thf(c_H6,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((((c_U1 @ X30) @ X31) @ X32) = (((c_If_5Fi @ ((c_SNoLe @ X30) @ c_Empty)) @ X31) @ ((c_F1 @ (((c_U1 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31) @ X32)) @ (((c_V1 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31) @ X32))))))))))).
thf(c_H7,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (! [X32:$i] : (((c_In @ X32) @ int) => ((((c_V1 @ X30) @ X31) @ X32) = (((c_If_5Fi @ ((c_SNoLe @ X30) @ c_Empty)) @ X32) @ ((c_G1 @ (((c_U1 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31) @ X32)) @ (((c_V1 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31) @ X32))))))))))).
thf(c_H8,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_W1 @ X30) @ X31) = (((c_U1 @ c_H1) @ (c_I1 @ X30)) @ ((c_J1 @ X30) @ X31)))))))).
thf(c_H9,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_F0 @ X30) @ X31) = ((c_W1 @ X30) @ X31))))))).
thf(c_H10,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_G0 @ X30) = X30)))).
thf(c_H11,axiom,(c_H0 = (ordsucc @ c_Empty))).
thf(c_H12,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_U0 @ X30) @ X31) = (((c_If_5Fi @ ((c_SNoLe @ X30) @ c_Empty)) @ X31) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31)) @ X30)))))))).
thf(c_H13,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_V0 @ X30) = ((c_U0 @ (c_G0 @ X30)) @ c_H0))))).
thf(c_H14,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_SMALL @ X30) = (c_V0 @ X30))))).
thf(c_H15,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_F3 @ X30) @ X31) = ((mul_5FSNo @ ((add_5FSNo @ X30) @ (minus_5FSNo @ X31))) @ X30))))))).
thf(c_H16,axiom,(c_G3 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H17,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_H3 @ X30) @ X31) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X31)))))))).
thf(c_H18,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_U3 @ X30) @ X31) = (((c_If_5Fi @ ((c_SNoLe @ X30) @ c_Empty)) @ X31) @ ((c_F3 @ ((c_U3 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31)) @ X30)))))))).
thf(c_H19,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_V3 @ X30) @ X31) = ((c_U3 @ c_G3) @ ((c_H3 @ X30) @ X31)))))))).
thf(c_H20,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_F2 @ X30) @ X31) = ((mul_5FSNo @ ((c_V3 @ X30) @ X31)) @ X30))))))).
thf(c_H21,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_G2 @ X30) = X30)))).
thf(c_H22,axiom,(c_H2 = (ordsucc @ c_Empty))).
thf(c_H23,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_U2 @ X30) @ X31) = (((c_If_5Fi @ ((c_SNoLe @ X30) @ c_Empty)) @ X31) @ ((c_F2 @ ((c_U2 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31)) @ X30)))))))).
thf(c_H24,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_V2 @ X30) = ((c_U2 @ (c_G2 @ X30)) @ c_H2))))).
thf(c_H25,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_F4 @ X30) @ X31) = ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ c_Empty)) @ X31)) @ X30))))))).
thf(c_H26,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_G4 @ X30) = X30)))).
thf(c_H27,axiom,(c_H4 = (ordsucc @ c_Empty))).
thf(c_H28,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => (! [X31:$i] : (((c_In @ X31) @ int) => (((c_U4 @ X30) @ X31) = (((c_If_5Fi @ ((c_SNoLe @ X30) @ c_Empty)) @ X31) @ ((c_F4 @ ((c_U4 @ ((add_5FSNo @ X30) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X31)) @ X30)))))))).
thf(c_H29,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_V4 @ X30) = ((c_U4 @ (c_G4 @ X30)) @ c_H4))))).
thf(c_H30,axiom,(! [X30:$i] : (((c_In @ X30) @ int) => ((c_FAST @ X30) = ((mul_5FSNo @ (c_V2 @ X30)) @ (c_V4 @ X30)))))).
thf(a10799,conjecture,(! [X30:$i] : (((c_In @ X30) @ int) => (((c_SNoLe @ c_Empty) @ X30) => ((c_SMALL @ X30) = (c_FAST @ X30)))))).
