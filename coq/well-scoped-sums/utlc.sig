ty : Type
tm: Type

Base : ty 
Fun : ty -> ty -> ty
Plus : ty -> ty -> ty

app : tm -> tm -> tm
lam : ty -> (tm -> tm) -> tm
inl : tm -> tm 
inr : tm -> tm 
orelim : tm -> (tm -> tm) -> (tm -> tm) -> tm
