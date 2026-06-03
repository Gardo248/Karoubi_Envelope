LoadPackage( "CAP", false );
LoadPackage( "LinearAlgebraForCAP", false );

#LoadPackage( "KaroubiEnvelope" );
Read( "../gap/KaroubiEnvelope_new.gd" );
Read( "../gap/KaroubiEnvelope_new.gi" );

Q := HomalgFieldOfRationals();

Qmat := MatrixCategory( Q );

kar := KaroubiEnvelope( Qmat );

V := 2 / Qmat;

endo := VectorSpaceMorphism( V, HomalgMatrix( [ [ 0, 1 ], [ 1, 0 ] ], 2, 2, Q ), V );


Vendo :=  endo / kar ;
IsWellDefinedForObjects( Vendo );
# false

e := VectorSpaceMorphism(V, HomalgMatrix( [ [ 1, 1 ], [ 0, 0 ] ], 2, 2, Q ), V );
f := VectorSpaceMorphism( V, HomalgMatrix( [ [ 0, 0 ], [ 1, 1 ] ], 2, 2, Q ), V );

iA := IdentityMorphism( V ) / kar;

i := ObjectDatum( iA );
IsEqualForObjects( iA, i / kar );
#true

eA := e / kar;
fA := f / kar;
phi := MorphismConstructor( fA, PreCompose( f, e ), eA );
phidatum := MorphismDatum( phi );
IsEqualForMorphisms( phidatum, Precompose( f, e ) );
IsEqualForMorphisms( phidatum, Precompose( f, e ) );
psi := MorphismConstructor( iA, f, fA );

IsWellDefinedForMorphisms( phi );
#true
IsWellDefinedForMorphisms( PreCompose( psi, phi ) );
#true



CanCompute( kar, "TensorProductOnObjects" );
