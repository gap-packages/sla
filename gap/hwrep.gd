DeclareProperty( "IsIrreducibleHWModule", IsAlgebraModule );

DeclareAttribute( "HighestWeight", IsAlgebraModule );

DeclareAttribute( "HighestWeightVector", IsAlgebraModule );

DeclareOperation( "IsomorphismOfIrreducibleHWModules", [ IsAlgebraModule,
     IsAlgebraModule ] );

DeclareOperation( "DisplayHighestWeight", [IsAlgebraModule] );

DeclareOperation( "DisplayDynkinDiagram", [IsMatrix] );

DeclareOperation( "DisplayWeightedDynkinDiagram", [IsNilpotentOrbit] );

DeclareProperty( "IsRegular", IsNilpotentOrbit );

DeclareOperation( "RegularNilpotentOrbit", [IsLieAlgebra] );

DeclareProperty( "IsDistinguished", IsNilpotentOrbit );

DeclareOperation( "DistinguishedNilpotentOrbits", [IsLieAlgebra] );