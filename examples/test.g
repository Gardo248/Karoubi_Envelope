LoadPackage( "CartesianCategories", false );
LoadPackage( "CAP", false );
LoadPackage( "LinearAlgebraForCAP", false );
LoadPackage( "FinSetsForCAP", false );

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

Tens_one := TensorUnit( kar );

fA = TensorProduct( fA, Tens_one );
#true

IsCongruentForMorphisms( psi, TensorProduct( IdentityMorphism( Tens_one ), psi ) );
#true

psiphi := TensorProduct( psi, phi );
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

IsEqualForMorphisms( TensorProduct( i, f ), IdempotentDatum( Source( psiphi ) ) );
#true

#TODO: add examples with unitors and associators

CanCompute( kar, "ZeroMorphism");
#true

IsAbCategory( kar );
#true

zero_ef := ZeroMorphism( eA, fA );

zero_kar := ZeroObject( kar );

zero_zero := ZeroMorphism( zero_kar, zero_kar );

TensorProduct( zero_ef, zero_zero + zero_zero ) = zero_zero;
#true

PreCompose( IdentityMorphism( iA ), psi ) - psi = ZeroMorphism(iA, fA);
#true

eta := MorphismConstructor( eA, e, eA );

gamma := MorphismConstructor( iA, f, eA );

efA := DirectSum( [ eA, fA ] );

fiA := DirectSum( [ fA, iA ] );

eeA := DirectSum( [ eA, eA ] );

phi_plus_psi := DirectSumFunctorialWithGivenDirectSums( fiA, [ phi, psi ], efA );

IsWellDefined( phi_plus_psi );
#true

eta_plus_phi := DirectSumFunctorialWithGivenDirectSums( efA, [ eta, phi ], eeA );

phi_plus_gamma := DirectSumFunctorialWithGivenDirectSums( fiA, [ phi, gamma ], eeA );

PreCompose( phi_plus_psi, eta_plus_phi ) = phi_plus_gamma;
#true

eta = PreCompose( PreCompose( InjectionOfCofactorOfDirectSumWithGivenDirectSum( [ eA, fA ], 1, efA ), eta_plus_phi ), ProjectionInFactorOfDirectSumWithGivenDirectSum( [ eA, eA ], 1, eeA ) );
#true

ZeroMorphism( eA, eA ) = PreCompose( PreCompose( InjectionOfCofactorOfDirectSumWithGivenDirectSum( [ eA, fA ], 1, efA ), eta_plus_phi ), ProjectionInFactorOfDirectSumWithGivenDirectSum( [ eA, eA ], 2, eeA ) );
#true


###########################################################

Sets := SkeletalCategoryOfFiniteSets( );

KarSets := KaroubiEnvelope( Sets );

T := 3 / Sets;

S := 7 / Sets;

eT := MorphismConstructor( T, [0, 1, 0], T );

eS := MorphismConstructor( S, [0, 1, 0, 1, 4, 5, 4], S );

eSK := eS / KarSets;

eTK := eT / KarSets;

zero_set := InitialObject( KarSets );

one_set := TerminalObject( KarSets );




