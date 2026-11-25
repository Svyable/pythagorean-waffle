# Area-free local similarity route

The finite cone now has a second independent geometric bridge, conditional
on elementary length rules and the local AA right-triangle similarity rule
in Waffle/Similarity.lean. No area function is needed. The earlier
AreaPlane route remains available for comparison.

At Y=(a,0), the two right triangles YMT and YHZ share the acute
angle between the horizontal ray YZ and ray YT. Here M=(0,0) and H
is the perpendicular foot of Z on TY. Their hypotenuses are on
different rays. Local AA similarity equates the opposite/hypotenuse
ratios b/c and length(ZH)/(2a).

Thus length(ZH)*c = 2ab. The cone homothety gives
length(ZH)=u*c/(1+v). With s=length(ZH)/c this gives both
s(1+v)=u and sc²=2ab. Apply the existing finite algebraic certificate.
Equal legs are handled directly with H=T; reversed order uses symmetry.

The local AA rule is an explicit field of LengthPlane, not a proved
consequence of Tarski or Hilbert axioms. It is not a global complex
length multiplication rule and no squared-distance formula occurs in
the derivation. Angle semantics still require a synthetic justification.
The taxicab counterexample demonstrates that the same affine
perpendicularity does not imply this AA length relation without an
additional geometric axiom.

## Next acceptance gates

- Connect the local common-angle rule to a synthetic theorem of
  corresponding side ratios (AA similarity), with explicit dependency
  evidence that no Pythagorean result was used.
- Compare the two geometric bridges and seek a minimal shared interface.
- Complete the independent infinite-cone realization and literature
  comparison before claiming originality.
