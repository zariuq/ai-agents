% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A2275.mg.html#A2275
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > $i))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > ($i > $i)))).
thf(c_G1_tp,type,(c_G1 : ($i > ($i > $i)))).
thf(c_H1_tp,type,(c_H1 : ($i > $i))).
thf(c_I1_tp,type,(c_I1 : ($i > $i))).
thf(c_J1_tp,type,(c_J1 : $i)).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > ($i > $i))))).
thf(c_V1_tp,type,(c_V1 : ($i > ($i > ($i > $i))))).
thf(c_W1_tp,type,(c_W1 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_F0 @ X15)) @ int)))).
thf(c_HG0,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_G0 @ X15)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => ((c_In @ ((c_U0 @ X15) @ X16)) @ int)))))).
thf(c_HV0,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_V0 @ X15)) @ int)))).
thf(c_HSMALL,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_SMALL @ X15)) @ int)))).
thf(c_HF1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => ((c_In @ ((c_F1 @ X15) @ X16)) @ int)))))).
thf(c_HG1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => ((c_In @ ((c_G1 @ X15) @ X16)) @ int)))))).
thf(c_HH1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_H1 @ X15)) @ int)))).
thf(c_HI1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_I1 @ X15)) @ int)))).
thf(c_HJ1,axiom,((c_In @ c_J1) @ int)).
thf(c_HU1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => (! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (((c_U1 @ X15) @ X16) @ X17)) @ int)))))))).
thf(c_HV1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => (! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (((c_V1 @ X15) @ X16) @ X17)) @ int)))))))).
thf(c_HW1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_W1 @ X15)) @ int)))).
thf(c_HFAST,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_In @ (c_FAST @ X15)) @ int)))).
thf(c_H1,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_F0 @ X15) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X15) @ X15))) @ X15))))))).
thf(c_H2,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_G0 @ X15) = X15)))).
thf(c_H3,axiom,(c_H0 = c_Empty)).
thf(c_H4,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => (((c_U0 @ X15) @ X16) = (((c_If_5Fi @ ((c_SNoLe @ X15) @ c_Empty)) @ X16) @ (c_F0 @ ((c_U0 @ ((add_5FSNo @ X15) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X16))))))))).
thf(c_H5,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_V0 @ X15) = ((c_U0 @ (c_G0 @ X15)) @ c_H0))))).
thf(c_H6,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_SMALL @ X15) = (c_V0 @ X15))))).
thf(c_H7,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => (((c_F1 @ X15) @ X16) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((mul_5FSNo @ X15) @ X16)))))))).
thf(c_H8,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => (((c_G1 @ X15) @ X16) = X16)))))).
thf(c_H9,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_H1 @ X15) = ((add_5FSNo @ X15) @ (minus_5FSNo @ (ordsucc @ c_Empty))))))).
thf(c_H10,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_I1 @ X15) = (((c_If_5Fi @ ((c_SNoLe @ X15) @ c_Empty)) @ c_Empty) @ (ordsucc @ c_Empty)))))).
thf(c_H11,axiom,(c_J1 = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty))))))).
thf(c_H12,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => (! [X17:$i] : (((c_In @ X17) @ int) => ((((c_U1 @ X15) @ X16) @ X17) = (((c_If_5Fi @ ((c_SNoLe @ X15) @ c_Empty)) @ X16) @ ((c_F1 @ (((c_U1 @ ((add_5FSNo @ X15) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X16) @ X17)) @ (((c_V1 @ ((add_5FSNo @ X15) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X16) @ X17))))))))))).
thf(c_H13,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => (! [X16:$i] : (((c_In @ X16) @ int) => (! [X17:$i] : (((c_In @ X17) @ int) => ((((c_V1 @ X15) @ X16) @ X17) = (((c_If_5Fi @ ((c_SNoLe @ X15) @ c_Empty)) @ X17) @ ((c_G1 @ (((c_U1 @ ((add_5FSNo @ X15) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X16) @ X17)) @ (((c_V1 @ ((add_5FSNo @ X15) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X16) @ X17))))))))))).
thf(c_H14,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_W1 @ X15) = (((c_U1 @ (c_H1 @ X15)) @ (c_I1 @ X15)) @ c_J1))))).
thf(c_H15,axiom,(! [X15:$i] : (((c_In @ X15) @ int) => ((c_FAST @ X15) = (c_W1 @ X15))))).
thf(a2275,conjecture,(! [X15:$i] : (((c_In @ X15) @ int) => (((c_SNoLe @ c_Empty) @ X15) => ((c_SMALL @ X15) = (c_FAST @ X15)))))).
