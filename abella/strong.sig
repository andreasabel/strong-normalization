sig strong.

kind    tm, ty      type.

type    c           tm.
type    app         tm -> tm -> tm.
type    abs         (tm -> tm) -> tm.

type    top         ty.
type    arrow       ty -> ty -> ty.


type   normal, neutral,notabs tm -> o.
type    ty          ty -> o.
type    of          tm -> ty -> o.
type    step, stepSN        tm -> tm -> o.
