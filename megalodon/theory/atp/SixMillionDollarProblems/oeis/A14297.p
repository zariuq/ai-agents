% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A14297.mg.html#A14297
% Bounty in April 2025: about 3 pfg bars ($240)
include('oeisheader.ax').
thf(c_F0_tp,type,(c_F0 : ($i > ($i > $i)))).
thf(c_G0_tp,type,(c_G0 : ($i > $i))).
thf(c_H0_tp,type,(c_H0 : $i)).
thf(c_U0_tp,type,(c_U0 : ($i > ($i > $i)))).
thf(c_V0_tp,type,(c_V0 : ($i > $i))).
thf(c_SMALL_tp,type,(c_SMALL : ($i > $i))).
thf(c_F1_tp,type,(c_F1 : ($i > $i))).
thf(c_G1_tp,type,(c_G1 : ($i > $i))).
thf(c_H1_tp,type,(c_H1 : ($i > $i))).
thf(c_U1_tp,type,(c_U1 : ($i > ($i > $i)))).
thf(c_V1_tp,type,(c_V1 : ($i > $i))).
thf(c_F2_tp,type,(c_F2 : ($i > ($i > $i)))).
thf(c_G2_tp,type,(c_G2 : ($i > $i))).
thf(c_H2_tp,type,(c_H2 : ($i > $i))).
thf(c_U2_tp,type,(c_U2 : ($i > ($i > $i)))).
thf(c_V2_tp,type,(c_V2 : ($i > $i))).
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ ((c_F0 @ X17) @ X18)) @ int)))))).
thf(c_HG0,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_G0 @ X17)) @ int)))).
thf(c_HH0,axiom,((c_In @ c_H0) @ int)).
thf(c_HU0,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ ((c_U0 @ X17) @ X18)) @ int)))))).
thf(c_HV0,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_V0 @ X17)) @ int)))).
thf(c_HSMALL,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_SMALL @ X17)) @ int)))).
thf(c_HF1,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_F1 @ X17)) @ int)))).
thf(c_HG1,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_G1 @ X17)) @ int)))).
thf(c_HH1,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_H1 @ X17)) @ int)))).
thf(c_HU1,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ ((c_U1 @ X17) @ X18)) @ int)))))).
thf(c_HV1,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_V1 @ X17)) @ int)))).
thf(c_HF2,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ ((c_F2 @ X17) @ X18)) @ int)))))).
thf(c_HG2,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_G2 @ X17)) @ int)))).
thf(c_HH2,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_H2 @ X17)) @ int)))).
thf(c_HU2,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => ((c_In @ ((c_U2 @ X17) @ X18)) @ int)))))).
thf(c_HV2,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_V2 @ X17)) @ int)))).
thf(c_HFAST,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_In @ (c_FAST @ X17)) @ int)))).
thf(c_H1,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => (((c_F0 @ X17) @ X18) = ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((mul_5FSNo @ ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X18)) @ X17)))))))).
thf(c_H2,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_G0 @ X17) = X17)))).
thf(c_H3,axiom,(c_H0 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H4,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => (((c_U0 @ X17) @ X18) = (((c_If_5Fi @ ((c_SNoLe @ X17) @ c_Empty)) @ X18) @ ((c_F0 @ ((c_U0 @ ((add_5FSNo @ X17) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X18)) @ X17)))))))).
thf(c_H5,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_V0 @ X17) = ((c_U0 @ (c_G0 @ X17)) @ c_H0))))).
thf(c_H6,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_SMALL @ X17) = (c_V0 @ X17))))).
thf(c_H7,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_F1 @ X17) = ((add_5FSNo @ X17) @ X17))))).
thf(c_H8,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_G1 @ X17) = X17)))).
thf(c_H9,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_H1 @ X17) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ X17))))).
thf(c_H10,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => (((c_U1 @ X17) @ X18) = (((c_If_5Fi @ ((c_SNoLe @ X17) @ c_Empty)) @ X18) @ (c_F1 @ ((c_U1 @ ((add_5FSNo @ X17) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X18))))))))).
thf(c_H11,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_V1 @ X17) = ((c_U1 @ (c_G1 @ X17)) @ (c_H1 @ X17)))))).
thf(c_H12,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => (((c_F2 @ X17) @ X18) = ((mul_5FSNo @ X17) @ X18))))))).
thf(c_H13,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_G2 @ X17) = X17)))).
thf(c_H14,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_H2 @ X17) = ((add_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ X17))))).
thf(c_H15,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => (! [X18:$i] : (((c_In @ X18) @ int) => (((c_U2 @ X17) @ X18) = (((c_If_5Fi @ ((c_SNoLe @ X17) @ c_Empty)) @ X18) @ ((c_F2 @ ((c_U2 @ ((add_5FSNo @ X17) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X18)) @ X17)))))))).
thf(c_H16,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_V2 @ X17) = ((c_U2 @ (c_G2 @ X17)) @ (c_H2 @ X17)))))).
thf(c_H17,axiom,(! [X17:$i] : (((c_In @ X17) @ int) => ((c_FAST @ X17) = ((mul_5FSNo @ (c_V1 @ X17)) @ (c_V2 @ X17)))))).
thf(a14297,conjecture,(! [X17:$i] : (((c_In @ X17) @ int) => (((c_SNoLe @ c_Empty) @ X17) => ((c_SMALL @ X17) = (c_FAST @ X17)))))).
