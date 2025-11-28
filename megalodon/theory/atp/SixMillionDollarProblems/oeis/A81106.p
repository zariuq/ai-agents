% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A81106.mg.html#A81106
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : $i)).
thf(c_H0_tp,type,(c_H0 : ($i > $i))).
thf(c_I0_tp,type,(c_I0 : $i)).
thf(c_J0_tp,type,(c_J0 : ($i > $i))).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > ($i > $i))))).
thf(c_V0_tp,type,(c_V0 : ($i > ($i > ($i > $i))))).
thf(c_W0_tp,type,(c_W0 : ($i > $i))).
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
thf(c_HF0,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => ((c_In @ ((c_F0 @ X18) @ X19)) @ int)))))).
thf(c_HG0,axiom,((c_In @ c_G0) @ int)).
thf(c_HH0,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_H0 @ X18)) @ int)))).
thf(c_HI0,axiom,((c_In @ c_I0) @ int)).
thf(c_HJ0,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_J0 @ X18)) @ int)))).
thf(c_HU0,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (((c_U0 @ X18) @ X19) @ X20)) @ int)))))))).
thf(c_HV0,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (((c_V0 @ X18) @ X19) @ X20)) @ int)))))))).
thf(c_HW0,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_W0 @ X18)) @ int)))).
thf(c_HSMALL,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_SMALL @ X18)) @ int)))).
thf(c_HF1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => ((c_In @ ((c_F1 @ X18) @ X19)) @ int)))))).
thf(c_HG1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => ((c_In @ ((c_G1 @ X18) @ X19)) @ int)))))).
thf(c_HH1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_H1 @ X18)) @ int)))).
thf(c_HI1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_I1 @ X18)) @ int)))).
thf(c_HJ1,axiom,((c_In @ c_J1) @ int)).
thf(c_HU1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (((c_U1 @ X18) @ X19) @ X20)) @ int)))))))).
thf(c_HV1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((c_In @ (((c_V1 @ X18) @ X19) @ X20)) @ int)))))))).
thf(c_HW1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_W1 @ X18)) @ int)))).
thf(c_HFAST,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ (c_FAST @ X18)) @ int)))).
thf(c_H1,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (((c_F0 @ X18) @ X19) = ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ ((add_5FSNo @ X18) @ X18)) @ X18))) @ X19))))))).
thf(c_H2,axiom,(c_G0 = c_Empty)).
thf(c_H3,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_H0 @ X18) = X18)))).
thf(c_H4,axiom,(c_I0 = (ordsucc @ c_Empty))).
thf(c_H5,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_J0 @ X18) = X18)))).
thf(c_H6,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((((c_U0 @ X18) @ X19) @ X20) = (((c_If_5Fi @ ((c_SNoLe @ X18) @ c_Empty)) @ X19) @ ((c_F0 @ (((c_U0 @ ((add_5FSNo @ X18) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X19) @ X20)) @ (((c_V0 @ ((add_5FSNo @ X18) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X19) @ X20))))))))))).
thf(c_H7,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((((c_V0 @ X18) @ X19) @ X20) = (((c_If_5Fi @ ((c_SNoLe @ X18) @ c_Empty)) @ X20) @ c_G0))))))))).
thf(c_H8,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_W0 @ X18) = (((c_U0 @ (c_H0 @ X18)) @ c_I0) @ (c_J0 @ X18)))))).
thf(c_H9,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_SMALL @ X18) = (c_W0 @ X18))))).
thf(c_H10,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (((c_F1 @ X18) @ X19) = ((mul_5FSNo @ X18) @ X19))))))).
thf(c_H11,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (((c_G1 @ X18) @ X19) = X19)))))).
thf(c_H12,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_H1 @ X18) = ((add_5FSNo @ X18) @ (minus_5FSNo @ (ordsucc @ c_Empty))))))).
thf(c_H13,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_I1 @ X18) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X18))))))).
thf(c_H14,axiom,(c_J1 = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ (ordsucc @ (ordsucc @ c_Empty)))))).
thf(c_H15,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((((c_U1 @ X18) @ X19) @ X20) = (((c_If_5Fi @ ((c_SNoLe @ X18) @ c_Empty)) @ X19) @ ((c_F1 @ (((c_U1 @ ((add_5FSNo @ X18) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X19) @ X20)) @ (((c_V1 @ ((add_5FSNo @ X18) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X19) @ X20))))))))))).
thf(c_H16,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => (! [X19:$i] : (((c_In @ X19) @ int) => (! [X20:$i] : (((c_In @ X20) @ int) => ((((c_V1 @ X18) @ X19) @ X20) = (((c_If_5Fi @ ((c_SNoLe @ X18) @ c_Empty)) @ X20) @ ((c_G1 @ (((c_U1 @ ((add_5FSNo @ X18) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X19) @ X20)) @ (((c_V1 @ ((add_5FSNo @ X18) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X19) @ X20))))))))))).
thf(c_H17,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_W1 @ X18) = (((c_U1 @ (c_H1 @ X18)) @ (c_I1 @ X18)) @ c_J1))))).
thf(c_H18,axiom,(! [X18:$i] : (((c_In @ X18) @ int) => ((c_FAST @ X18) = (((c_If_5Fi @ ((c_SNoLe @ X18) @ c_Empty)) @ (ordsucc @ c_Empty)) @ (c_W1 @ X18)))))).
thf(a81106,conjecture,(! [X18:$i] : (((c_In @ X18) @ int) => (((c_SNoLe @ c_Empty) @ X18) => ((c_SMALL @ X18) = (c_FAST @ X18)))))).
