% https://mgwiki.github.io/mgw_test/conj/aim/AIMBountiesNov2024.mg.html#T1dist__aa1
% Bounty in April 2025: about 296.4 pfg bars ($23712)
include('aimheader.ax').
thf(conj_aim2024_T1dist__aa1,conjecture,((! [X10:$i] : (((c_In @ X10) @ c_X) => (! [X11:$i] : (((c_In @ X11) @ c_X) => (! [X12:$i] : (((c_In @ X12) @ c_X) => (((m @ ((c_T @ X10) @ X11)) @ ((c_T @ X12) @ X11)) = ((c_T @ ((m @ X10) @ X12)) @ X11)))))))) => (! [X10:$i] : (((c_In @ X10) @ c_X) => (! [X11:$i] : (((c_In @ X11) @ c_X) => (! [X12:$i] : (((c_In @ X12) @ c_X) => (! [X13:$i] : (((c_In @ X13) @ c_X) => (! [X14:$i] : (((c_In @ X14) @ c_X) => ((((a @ (((a @ X10) @ X11) @ X12)) @ X13) @ X14) = e))))))))))))).
