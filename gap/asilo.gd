DeclareOperation( "ExtendedCartanMatrix", [IsRootSystem] );

DeclareOperation( "CartanType", [IsMatrix] );

DeclareOperation( "WeylTransversal", [IsRootSystem,IsList] );

DeclareAttribute( "WeylPermutations", IsWeylGroup );

DeclareAttribute( "AdmissibleLattice", IsAlgebraModule );

DeclareOperation( "SizeOfWeylGroup", [IsList] );

DeclareOperation( "SizeOfWeylGroup", [IsString, IsInt] );

DeclareOperation( "SizeOfWeylGroup", [IsRootSystem] );

DeclareAttribute( "WeylGroupAsPermGroup", IsRootSystem );

DeclareOperation( "ApplyWeylPermToWeight", [IsRootSystem, IsPerm, IsList] );

DeclareOperation( "WeylWordAsPerm", [IsRootSystem, IsList] );

DeclareOperation( "PermAsWeylWord", [IsRootSystem, IsPerm] );

DeclareOperation( "ApplyWeylPermToCartanElement", [IsLieAlgebra, IsPerm,
IsObject ] );
