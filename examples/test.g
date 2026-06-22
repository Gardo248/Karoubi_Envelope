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
iA = i / kar;
#true

eA := e / kar;
fA := f / kar;
eA = fA;
#false

phi := MorphismConstructor( fA, PreCompose( f, e ), eA );
phidatum := MorphismDatum( phi );

IsEqualForMorphisms( phi, MorphismConstructor( fA, phidatum, eA ) );
#true

psi := MorphismConstructor( iA, f, fA );

IsWellDefined( phi );
#true
IsWellDefined( PreCompose( psi, phi ) );
#true
psi = PreCompose( psi, IdentityMorphism( fA ) );
#same as IsCongruentForMorphisms( psi, PreCompose( psi, IdentityMorphism( fA ) ) );
#true

CanCompute( kar, "TensorProductOnObjects" );
#true

one := TensorUnit( kar );

fA = TensorProduct( fA, one );
#true

IsCongruentForMorphisms( psi, TensorProduct( IdentityMorphism( one ), psi ) );
#true

phipsi := TensorProduct( psi, phi );
#a morphism in KaroubiEnvelope(Category of matices over Q)

MorphismDatum( TensorProduct( psi, phi ) );
#[ [ 0, 0, 0, 0 ],
#  [ 0, 0, 0, 0 ],
#  [ 0, 0, 0, 0 ],
#  [ 1, 1, 1, 1 ]
#]
# A morphism in Category of matrices over Q

Source( TensorProduct( psi, phi ) );
#an object in KaroubiEnvelope(Category of matrices over Q)

IsEqualForMorphisms( TensorProduct( i, f ), IdempotentDatum( Source( phipsi ) ) );
#true

#TODO: add examples with unitors and associators

CanCompute( kar, "ZeroMorphism");
#true

IsAbCategory( kar );
#true

zero_ef := ZeroMorphism( eA, fA );

zero := ZeroObject( kar );

zero_zero := ZeroMorphism( zero, zero );

TensorProduct( zero_ef, zero_zero + zero_zero ) = zero_zero;
#true

PreCompose( IdentityMorphism( iA ), psi ) - psi = ZeroMorphism(iA, fA);
#true



