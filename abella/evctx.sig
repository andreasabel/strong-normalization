sig evctx.

kind    tm, ty      type.

type    app         tm -> tm -> tm.
type    abs         (tm -> tm) -> tm.

type    top         ty.
type    arrow       ty -> ty -> ty.


type   value	     tm -> o.

type    of          tm -> ty -> o.

type    step      tm -> tm -> o.
type  evctx 	   (tm -> tm) -> o.
