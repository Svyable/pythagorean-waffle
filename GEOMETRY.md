# Geometric bridge: finite cone and reflected altitude

Status: intermediate axiomatic geometry, not yet a derivation from
Tarski or Hilbert incidence/congruence axioms.

Let T=(0,b), Y=(a,0), Z=(-a,0), 0<a<b. Let
u=2ab/(b²-a²), v=2a²/(b²-a²), and X=Y-u(b,a).
The verified affine equations give X=Z-v(a,b); hence T, Z, X are
collinear and TX=(1+v)(a,b) as a directed vector from X to T.
The cone leg XY=u(b,a) is perpendicular to TY by a quarter-turn.

Let H=T+(Y-T)/(1+v). Then H is on TY and
H-Z=(u/(1+v))(b,a). This is the reflected triangle's altitude.
The two right triangles therefore give the same opposite/hypotenuse ratio:
s=length(ZH)/c=length(XY)/length(XT)=u/(1+v).

Compute the area of TYZ using the horizontal base YZ (length 2a)
and altitude b: area=ab. Compute again using base TY (length c)
and altitude ZH (length sc): area=sc²/2. Hence sc²=2ab.
Combining with the existing finite cone certificate gives a²+b²=c².
The equal-leg case has a perpendicular reflected apex and uses the
same area relation; reversed ordering follows from swap symmetry.

## Exact assumptions

AreaPlane contains abstract length (axial calibration, coordinate swap,
reflection, positivity, scalar homogeneity), an abstract area function,
cyclic invariance and a base-times-perpendicular-altitude formula.
OnLine and Perp are affine predicates; Perp uses a quarter-turn,
not a Euclidean inner product or distance definition.

This removes the archived global complex-similarity length axiom and
the two sine equations as direct hypotheses. It does NOT establish
their independence from elementary synthetic axioms: the global
base-height area principle and quarter-turn/length semantics are
substantive Euclidean assumptions that require justification. In fact,
they already suffice for Pythagoras, as the checked theorem shows.
A standard axiom audit does not audit the strength of structure fields.

## Next acceptance gate

Derive the geometric interface (or a local equivalent) from an explicit
synthetic geometry library using an independently justified area
theory, or replace the area bridge with a synthetic Law of Sines
derived via altitude and triangle similarity. Audit those dependencies.
Do not label this a completed synthetic-foundations proof until then.
