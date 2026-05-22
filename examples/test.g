
LoadPackage( "CAP", false );
LoadPackage( "LinearAlgebraForCAP", false );

#LoadPackage("KaroubiEnvelope");
Read("../gap/KaroubiEnvelope_new.gd");
Read("../gap/KaroubiEnvelope_new.gi");

Q := HomalgFieldOfRationals();

Qmat := MatrixCategory( Q );

kar := KaroubiEnvelope( Qmat );

V := 2 / Qmat;

endo := VectorSpaceMorphism( V, HomalgMatrix( [ [ 0, 1 ], [ 1, 0 ] ], 2, 2, Q ), V );

# not valid because endo is not an idempotent
Vendo :=  endo / kar ;
IsWellDefinedForObjects(Vendo);
# false

e := VectorSpaceMorphism(V, HomalgMatrix( [[1, 1], [0, 0]], 2, 2, Q), V);
f := VectorSpaceMorphism(V, HomalgMatrix( [[0, 0], [1, 1]], 2, 2, Q), V);

iA := IdentityMorphism(V) / kar;
eA := e / kar;
fA := f / kar;
phi := MorphismConstructor(eA, PreCompose(f, e), fA);
