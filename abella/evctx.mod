module evctx.

ty top.
ty (arrow A B) :- ty A, ty B.

of (app M N) B :- of M (arrow A B), of N A.
of (abs R) (arrow A B) :- pi x\ (of x A => of (R x) B).


value (abs R).

evctx (x\ x).
evctx (x\ (app (C x) M)) :- evctx C.
% evctx (x\ (app V (C x))) :- evctx C, value V.

% evctx rule
step (C M) (C N) :- evctx C, step M N.
%beta
step (app (abs R) M) (R M).




