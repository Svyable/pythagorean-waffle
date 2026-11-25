# Local characterization of Euclidean length

Under the BasicLength interface (axis calibration, positivity, scalar homogeneity, reflection and axis-swap symmetry), three conditions are equivalent:

1. Quadratic: L(x,y)^2 = x^2+y^2 for every vector.
2. LocalAA: the common-angle right-triangle ratio rule.
3. NormalizedTest: for each x>0, p=(1,0), q=(1,x), t=1/(1+x^2), require L(0,x)L(1,0)=L(p-tq)L(q).

The forward AA implication uses the finite waffle proof; the converse deliberately assumes the quadratic law. The normalized test suffices because p-tq=[x/(1+x^2)](x,-1). Symmetry and homogeneity reduce the test to x=[x/(1+x^2)]L(1,x)^2. Cancellation establishes the quadratic law on positive slopes; scaling and symmetry extend it to all vectors.

No continuity, triangle inequality, area function, infinite series or analytic trigonometry is assumed. The equivalence identifies the logical strength of the local rule within this coordinate setting, not its derivation from Tarski or Hilbert geometry. Priority and minimality among alternative foundations remain open.

Next: justify the normalized projection test synthetically, compare known Euclidean norm characterizations, and investigate dense-slope testing under continuity.
