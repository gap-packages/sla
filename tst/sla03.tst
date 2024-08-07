# SLA, chapter 3
#
# DO NOT EDIT THIS FILE - EDIT EXAMPLES IN THE SOURCE INSTEAD!
#
# This file has been generated by AutoDoc. It contains examples extracted from
# the package documentation. Each example is preceded by a comment which gives
# the name of a GAPDoc XML file and a line range from which the example were
# taken. Note that the XML file in turn may have been generated by AutoDoc
# from some other input.
#
gap> START_TEST("sla03.tst");

# doc/manual.xml:366-371
gap> L:= SimpleLieAlgebra("F",4,Rationals);
<Lie algebra of dimension 52 over Rationals>
gap> DisplayDynkinDiagram(L);              
F4:  2---4=>=3---1

# doc/manual.xml:387-399
gap> L:= SimpleLieAlgebra("F",4,Rationals);;
gap> R:= RootSystem(L);;
gap> W:= WeylGroupAsPermGroup(R);;
gap> w:= Product( GeneratorsOfGroup(W) );
(1,32,33,36,35,27,25,8,9,12,11,3)(2,30,34,44,37,39,26,6,10,20,13,15)(4,16,23,24,22,18,28,
40,47,48,46,42)(5,31,41,43,45,38,29,7,17,19,21,14)
gap> H:= CartanSubalgebra(L);;
gap> h:= Sum( Basis(H) );
v.49+v.50+v.51+v.52
gap> ApplyWeylPermToCartanElement( L, w, h );
(-1)*v.52

# doc/manual.xml:421-435
gap> L:= SimpleLieAlgebra("G",2,Rationals);;
gap> V:= HighestWeightModule( L, [2,0] );
<27-dimensional left-module over <Lie algebra of dimension 14 over Rationals>>
gap> B:=AdmissibleLattice(V);;
gap> x:= L.1;
v.1
gap> mx:= MatrixOfAction( B, x );;
gap> IsZero(mx^4); IsZero(mx^5);
false
true
gap> exp:=Sum( List( [0..4], i -> mx^i/Factorial(i) ) );;
gap> ForAll( Flat(exp), IsInt );
true

# doc/manual.xml:449-461
gap> L:= SimpleLieAlgebra("G",2,Rationals);;
gap> V:= HighestWeightModule( L, [1,0] );;
gap> W:= TensorProductOfAlgebraModules( V, V );
<49-dimensional left-module over <Lie algebra of dimension 14 over Rationals>>
gap> DirectSumDecomposition( W );
[ <left-module over <Lie algebra of dimension 14 over Rationals>>, 
  <left-module over <Lie algebra of dimension 14 over Rationals>>, 
  <left-module over <Lie algebra of dimension 14 over Rationals>>, 
  <left-module over <Lie algebra of dimension 14 over Rationals>> ]
gap> List( last, Dimension );
[ 27, 7, 14, 1 ]

# doc/manual.xml:475-482
gap> L:= SimpleLieAlgebra("F",4,Rationals);
<Lie algebra of dimension 52 over Rationals>
gap> V:= HighestWeightModule( L, [0,1,0,0] );
<52-dimensional left-module over <Lie algebra of dimension 52 over Rationals>>
gap> IsIrreducibleHWModule(V);
true

# doc/manual.xml:499-511
gap> L:= SimpleLieAlgebra("G",2,Rationals);;
gap> V:= HighestWeightModule( L, [1,0] );;
gap> W:= TensorProductOfAlgebraModules( V, V );;
gap> dW:= DirectSumDecomposition( W );;
gap> cg:= CanonicalGenerators( RootSystem(L) );;
gap> v0:= HighestWeightVector( dW[3] );
1*(1*v0<x>y1*v0)-1*(y1*v0<x>1*v0)
gap> List( cg[3], h -> h^v0 );
[ <0-tensor>, 1*(1*v0<x>y1*v0)-1*(y1*v0<x>1*v0) ]
gap> List( cg[1], h -> h^v0 );
[ <0-tensor>, <0-tensor> ]

# doc/manual.xml:527-534
gap> L:= SimpleLieAlgebra("G",2,Rationals);;
gap> V:= HighestWeightModule( L, [1,0] );;
gap> W:= TensorProductOfAlgebraModules( V, V );;
gap> dW:= DirectSumDecomposition( W );;
gap> List( dW, HighestWeight );
[ [ 2, 0 ], [ 1, 0 ], [ 0, 1 ], [ 0, 0 ] ]

# doc/manual.xml:548-579
gap> r:= LieAlgebraAndSubalgebras( "E8" );;
gap> L:= r.liealg;;
gap> K:= r.subalgs[823];
<Lie algebra of dimension 58 over CF(84)>
gap> DisplayDynkinDiagram(K);
A1:  1
B5:  2---3---4---5=>=6
gap> V:= AdjointModule( L );
<248-dimensional left-module over <Lie algebra of dimension 248 over CF(84)>>
gap> W:= ModuleByRestriction( V, K );
<248-dimensional left-module over <Lie algebra of dimension 58 over CF(84)>>
gap> dW:= DirectSumDecomposition( W ); 
[ <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>>, 
  <left-module over <Lie algebra of dimension 58 over CF(84)>> ]
gap> List( dW, Dimension );
[ 33, 3, 3, 3, 64, 64, 11, 11, 55, 1 ]
gap> DisplayHighestWeight( dW[5] );
A1:  1
B5:  0---0---0---0=>=1
gap> DisplayHighestWeight( dW[1] );
A1:  2
B5:  1---0---0---0=>=0

# doc/manual.xml:594-615
gap> r:= LieAlgebraAndSubalgebras( "E8" );;
gap> L:= r.liealg;;
gap> K:= r.subalgs[823];;
gap> DisplayDynkinDiagram(K);
A1:  1
B5:  2---3---4---5=>=6
gap> V:= AdjointModule( L );;
gap> W:= ModuleByRestriction( V, K );;
gap> dW:= DirectSumDecomposition( W );;
gap> DisplayHighestWeight( dW[5] );
A1:  1
B5:  0---0---0---0=>=1
gap> DisplayHighestWeight( dW[6] );
A1:  1
B5:  0---0---0---0=>=1
gap> f:= IsomorphismOfIrreducibleHWModules( dW[5], dW[6] );;
gap> Image( f, HighestWeightVector( dW[5] ) );
v.205
gap> HighestWeightVector( dW[6] );
v.205

# doc/manual.xml:636-656
gap> L:= SimpleLieAlgebra("E",6,Rationals);;
gap> V:= HighestWeightModule( L, [0,0,1,0,0,0] );; Dimension(V);
351
gap> Vst:= DualAlgebraModule( V );
<351-dimensional left-module over <Lie algebra of dimension 78 over Rationals>>
gap> DisplayHighestWeight( Vst );
             0
             |
E6:  0---0---0---1---0
gap> DisplayHighestWeight( V );  
             0
             |
E6:  0---1---0---0---0
gap> v0:= HighestWeightVector( Vst );
(1)*F@y15*y23*y36^(2)*v0
gap> f:= ExtRepOfObj( v0 );         
(1)*F@y15*y23*y36^(2)*v0
gap> Image(f, Basis(V)[10] );
0

# doc/manual.xml:714-719
gap> L:= SimpleLieAlgebra("G",2,Rationals);;
gap> CharacteristicsOfStrata( L, [0,1] );
[ [ v.13+(2)*v.14, (2)*v.13+(3)*v.14, (2)*v.13+(4)*v.14, (6)*v.13+(10)*v.14 ],
  [ 6, 8, 10, 12 ] ]

# doc/manual.xml:728-790
gap> f:= FiniteOrderInnerAutomorphisms("E",6,3)[2];;
gap> M:= Source(f);;
gap> gr:= Grading(f);;
gap> L:= Subalgebra(M,gr[1]);
<Lie algebra over CF(3), with 28 generators>
gap> K:= LieDerivedSubalgebra( L );
<Lie algebra of dimension 27 over CF(3)>
gap> V:= LeftAlgebraModuleByGenerators( K, function(x,v) return x*v; end, gr[2]); 
<left-module over <Lie algebra of dimension 27 over CF(3)>>
gap> DisplayDynkinDiagram( K ); 
A4:  1---4---3---2
A1:  5
gap> dV:= DirectSumDecomposition(V);
[ <left-module over <Lie algebra of dimension 27 over CF(3)>>, 
  <left-module over <Lie algebra of dimension 27 over CF(3)>> ]
gap> DisplayHighestWeight( dV[1] );        
A4:  0---0---0---1
A1:  0
gap> DisplayHighestWeight( dV[2] );
A4:  0---0---1---0
A1:  1
gap> t0:= Basis(LieCentre(L))[1];
v.73+(4/5)*v.75+(3/5)*v.76+(2/5)*v.77+(1/5)*v.78
gap> HighestWeightVector( dV[1] ); t0^last;
v.7
(6/5)*v.7
gap> HighestWeightVector( dV[2] ); t0^last;
v.13
(-3/5)*v.13
gap> hw:= [ [0,1,0,0,0,6/5], [0,0,1,0,1,-3/5] ]; 
[ [ 0, 1, 0, 0, 0, 6/5 ], [ 0, 0, 1, 0, 1, -3/5 ] ]
gap> bas:= Concatenation( CanonicalGenerators( RootSystem(K) )[3],
> Basis(LieCentre(L)) );;
gap> B:= List( bas, x -> [] );;
gap> ad:= List( bas, x -> AdjointMatrix( Basis(M), x ) );;
gap> for i in [1..Length(B)] do for j in [i..Length(B)] do
> B[i][j]:= TraceMat( ad[i]*ad[j]); B[j][i]:= B[i][j];
> od; od;
gap> B;
[ [ 48, 0, 0, -24, 0, 0 ], [ 0, 48, -24, 0, 0, 0 ], [ 0, -24, 48, -24, 0, 0 ], 
[ -24, 0, -24, 48, 0, 0 ], [ 0, 0, 0, 0, 48, 0 ], [ 0, 0, 0, 0, 0, 144/5 ] ]
gap> CharacteristicsOfStrata( L, B, hw );
[ [ v.74+v.75+v.76, v.73+v.75, (-2)*v.73, 
      (2)*v.74+(2)*v.75+(3)*v.76+(2)*v.77+v.78, (-1)*v.73+(-1)*v.76+(-1)*v.77,
      v.73+v.74+(2)*v.75+v.76, (2)*v.73+(2)*v.74+(4)*v.75+(4)*v.76+(2)*v.77+(
        2)*v.78, (-2)*v.73+v.74, v.74+(4)*v.75+(2)*v.76+v.77+v.78, 
      (-1)*v.73+v.74+v.75+v.76, (2)*v.73+(3)*v.74+(5)*v.75+(5)*v.76+(3)*v.77+(
        2)*v.78, v.73+(4)*v.75+v.76, v.75+(-1)*v.76+(-1)*v.77, 
      v.73+v.74+(3)*v.75+(2)*v.76+v.78, (4)*v.73+(6)*v.74+(7)*v.75+(9)*v.76+(
        6)*v.77+(3)*v.78, (-3)*v.73+(-2)*v.75+(-2)*v.76+(-2)*v.77+(-1)*v.78, 
      (4)*v.75+(2)*v.76, (2)*v.73+(6)*v.74+(8)*v.75+(8)*v.76+(4)*v.77+(2)*v.78
        , (2)*v.74+(4)*v.75+(2)*v.76+v.77+v.78, 
      (2)*v.74+(4)*v.75+(2)*v.76+(-2)*v.77, 
      v.73+v.74+(5)*v.75+(3)*v.76+v.77+v.78, 
      v.73+(2)*v.74+(4)*v.75+(3)*v.76+v.77+v.78, 
      (4)*v.73+(6)*v.74+(10)*v.75+(10)*v.76+(4)*v.77+(4)*v.78, 
      (3)*v.73+(6)*v.74+(10)*v.75+(10)*v.76+(5)*v.77+(5)*v.78, 
      (-1)*v.73+v.74+(3)*v.75+(-3)*v.77+(-1)*v.78, 
      (6)*v.74+(10)*v.75+(8)*v.76+(2)*v.77+(2)*v.78 ], 
  [ 8, 5, 16, 11, 12, 10, 13, 18, 18, 15, 15, 17, 13, 15, 16, 20, 20, 20, 19, 
      21, 19, 17, 20, 22, 22, 24 ] ]

#
gap> STOP_TEST("sla03.tst", 1);
