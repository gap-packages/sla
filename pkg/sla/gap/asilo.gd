DeclareOperation( "ExtendedCartanMatrix", [IsRootSystem] );

DeclareOperation( "CartanType", [IsMatrix] );

DeclareOperation( "WeylTransversal", [IsRootSystem,IsList] );

DeclareAttribute( "WeylPermutations", IsWeylGroup );

DeclareAttribute( "AdmissibleLattice", IsAlgebraModule );

DeclareOperation( "SizeOfWeylGroup", [IsList] );

DeclareOperation( "SizeOfWeylGroup", [IsString, IsInt] );

DeclareOperation( "SizeOfWeylGroup", [IsRootSystem] );