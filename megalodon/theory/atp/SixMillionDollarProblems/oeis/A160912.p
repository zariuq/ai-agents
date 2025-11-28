% https://mgwiki.github.io/mgw_test/conj/oeis/oeis-A160912.mg.html#A160912
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
thf(c_FAST_tp,type,(c_FAST : ($i > $i))).
thf(c_HF0,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => (! [X11:$i] : (((c_In @ X11) @ int) => ((c_In @ ((c_F0 @ X10) @ X11)) @ int)))))).
thf(c_HG0,axiom,((c_In @ c_G0) @ int)).
thf(c_HH0,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_In @ (c_H0 @ X10)) @ int)))).
thf(c_HI0,axiom,((c_In @ c_I0) @ int)).
thf(c_HJ0,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_In @ (c_J0 @ X10)) @ int)))).
thf(c_HU0,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => (! [X11:$i] : (((c_In @ X11) @ int) => (! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (((c_U0 @ X10) @ X11) @ X12)) @ int)))))))).
thf(c_HV0,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => (! [X11:$i] : (((c_In @ X11) @ int) => (! [X12:$i] : (((c_In @ X12) @ int) => ((c_In @ (((c_V0 @ X10) @ X11) @ X12)) @ int)))))))).
thf(c_HW0,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_In @ (c_W0 @ X10)) @ int)))).
thf(c_HSMALL,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_In @ (c_SMALL @ X10)) @ int)))).
thf(c_HFAST,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_In @ (c_FAST @ X10)) @ int)))).
thf(c_H1,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => (! [X11:$i] : (((c_In @ X11) @ int) => (((c_F0 @ X10) @ X11) = ((add_5FSNo @ ((add_5FSNo @ X10) @ X11)) @ X11))))))).
thf(c_H2,axiom,(c_G0 = (ordsucc @ (ordsucc @ c_Empty)))).
thf(c_H3,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_H0 @ X10) = ((add_5FSNo @ X10) @ X10))))).
thf(c_H4,axiom,(c_I0 = (ordsucc @ c_Empty))).
thf(c_H5,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_J0 @ X10) = X10)))).
thf(c_H6,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => (! [X11:$i] : (((c_In @ X11) @ int) => (! [X12:$i] : (((c_In @ X12) @ int) => ((((c_U0 @ X10) @ X11) @ X12) = (((c_If_5Fi @ ((c_SNoLe @ X10) @ c_Empty)) @ X11) @ ((c_F0 @ (((c_U0 @ ((add_5FSNo @ X10) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X11) @ X12)) @ (((c_V0 @ ((add_5FSNo @ X10) @ (minus_5FSNo @ (ordsucc @ c_Empty)))) @ X11) @ X12))))))))))).
thf(c_H7,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => (! [X11:$i] : (((c_In @ X11) @ int) => (! [X12:$i] : (((c_In @ X12) @ int) => ((((c_V0 @ X10) @ X11) @ X12) = (((c_If_5Fi @ ((c_SNoLe @ X10) @ c_Empty)) @ X12) @ c_G0))))))))).
thf(c_H8,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_W0 @ X10) = (((c_U0 @ (c_H0 @ X10)) @ c_I0) @ (c_J0 @ X10)))))).
thf(c_H9,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_SMALL @ X10) = (c_W0 @ X10))))).
thf(c_H10,axiom,(! [X10:$i] : (((c_In @ X10) @ int) => ((c_FAST @ X10) = ((add_5FSNo @ (ordsucc @ c_Empty)) @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ ((add_5FSNo @ ((mul_5FSNo @ (ordsucc @ (ordsucc @ c_Empty))) @ ((add_5FSNo @ X10) @ X10))) @ (minus_5FSNo @ (((c_If_5Fi @ ((c_SNoLe @ X10) @ c_Empty)) @ c_Empty) @ (ordsucc @ (ordsucc @ c_Empty)))))) @ X10))))))).
thf(a160912,conjecture,(! [X10:$i] : (((c_In @ X10) @ int) => (((c_SNoLe @ c_Empty) @ X10) => ((c_SMALL @ X10) = (c_FAST @ X10)))))).
