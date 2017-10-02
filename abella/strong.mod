module strong.

ty top.
ty (arrow A B) :- ty A, ty B.

of (app M N) B :- of M (arrow A B), of N A.
of (abs R) (arrow A B) :- ty A, pi x\ (of x A => of (R x) B).

% We add this since Girard's proof assumes we can always find
% at least one element in the reducability relation
% of c A :- ty A.


notabs (app M N).
step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- step N N'.
step (app (abs R) M) (R M).
step (abs  R) (abs R') :- pi x\ step (R x) (R' x).

stepSN (app (abs R) M) (R M) :- normal M.

stepSN (app M N) (app M' N) :- notabs M, stepSN M M'.



normal (abs R) :- pi x \ neutral x => normal (R x).
normal M :- neutral M.
normal M :- stepSN M N, normal N.
neutral (app M N) :- neutral M, normal N.