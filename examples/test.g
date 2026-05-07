
LoadPackage( "CAP", false );
LoadPackage( "LinearAlgebraForCAP", false );

#LoadPackage("KaroubiEnvelope");
Read("../gap/KaroubiEnvelope.gd");
Read("../gap/KaroubiEnvelope.gi");

Q := HomalgFieldOfRationals();

underlying_category := MatrixCategory( Q );

kar := KaroubiEnvelope( underlying_category );


V := VectorSpaceObject( 2, Q );

endo := VectorSpaceMorphism( V, HomalgMatrix( [ [ 0, 1 ], [ 1, 0 ] ], 2, 2, Q ), V );

# not valid because endo is not an idempotent
Vendo := KaroubiObject( endo );
IsWellDefinedForObjects(Vendo);
# false

e := VectorSpaceMorphism(V, HomalgMatrix( [[1, 1], [0, 0]], 2, 2, Q), V);
f := VectorSpaceMorphism(V, HomalgMatrix( [[0, 0], [1, 1]], 2, 2, Q), V);

iA := KaroubiObject(IdentityMorphism(V));
eA := KaroubiObject(e);
fA := KaroubiObject(f);
phi := KaroubiMorphism(eA, PreCompose(f, e), fA);

a := ListPrimitivelyInstalledOperationsOfCategory( CapCategory( V ) );;
b := ListInstalledOperationsOfCategory( CapCategory( phi ) );;
Display(Difference( a, b ));
