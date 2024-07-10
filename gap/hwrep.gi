InstallMethod( HighestWeightVector,
     "for an irreducible highest weight module",
     true, [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection ], 0,
    function( V )

    local L, K, R, e, m, c, sp;

    if HasBasis(V) and IsWeightRepElement( Basis(V)[1]![1] ) then
       return Basis(V)[1];
    fi;

    K:= LeftActingAlgebra( V );

    R:= RootSystem(K);
    if R = fail then return fail; fi;
    e:= CanonicalGenerators( R )[1];

    m:= List( e, u -> TransposedMatDestructive( MatrixOfAction( Basis(V), u )));
    m:= List( [1..Dimension(V)], i -> Concatenation( List( m, u -> u[i] ) ) );
    c:= NullspaceMatDestructive(m);
    sp:= Subspace( V, List( c, u -> u*Basis(V) ), "basis" );
    if Dimension( sp ) > 1 then return fail; fi;

    return Basis(sp)[1];

end );

InstallMethod( IsIrreducibleHWModule,
     "for an algebra module",
     true, [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection ], 0,
    function( V )

    return HighestWeightVector(V) <> fail;

end );

InstallMethod( HighestWeight,
     "for an irreducible highest weight module",
     true, [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection ], 0,
    function( V )

    local L, h, v0, b;

    L:= LeftActingAlgebra(V);
    h:= CanonicalGenerators( RootSystem(L) )[3];
    v0:= HighestWeightVector( V );
    if v0 = fail then return fail; fi;
    b:= Basis( Subspace( V, [v0] ), [v0] );
    return List( h, u -> Coefficients( b, u^v0 )[1] );

end );





InstallMethod( DirectSumDecomposition,
"for a module over a semisimple Lie algebra", 
true, [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection], 0,

function( V )

   local L, R, e, sp, x, m, c, sp0, K, h, U, es, u, M, b, hw;

   K:= LeftActingAlgebra( V );

   R:= RootSystem(K);
   if R = fail then return fail; fi;
   e:= CanonicalGenerators( R )[1];

   m:= List( e, u -> TransposedMatDestructive( MatrixOfAction( Basis(V), u )));
   m:= List( [1..Dimension(V)], i -> Concatenation( List( m, u -> u[i] ) ) );
   c:= NullspaceMatDestructive(m);
   sp:= Subspace( V, List( c, u -> u*Basis(V) ), "basis" );

   # in sp find a basis of weight vectors
   h:= CanonicalGenerators( R )[3];
   sp:= [ sp ];
   for x in h do
       sp0:= [ ];
       for U in sp do
           m:= List( Basis(U), a -> Coefficients( Basis(U), x^a ) );
           es:= Eigenspaces(LeftActingDomain(K),m);
           Append( sp0, List( es, M -> Subspace( V, List( Basis(M), v ->
                                          v*Basis(U) ) ) ) );
       od;
       sp:= sp0;
   od;

   sp0:= [ ];
   for U in sp do
       u:= Basis(U)[1];
       b:= Basis( Subspace( V, [u] ), [u] );
       hw:= List( h, s -> Coefficients( b, s^u )[1] );       
       for u in Basis(U) do
           M:= SubAlgebraModule( V, [u] );
	   SetIsIrreducibleHWModule( M, true );
           SetHighestWeightVector( M, u );
	   SetHighestWeight( M, hw );	   
           Add( sp0, M );
       od;
   od;
   return sp0;
    

end );

SLAfcts.canbasofhwrep:= function( V )


    local   L,  R,  hw,  cg,  paths,  strings,  p,  p1, word, k, b,
            st,  i,  j,  a,  y,  v,  bas, s1, i1, n1,  w,  sim, pos, posR, yy, 
            weylwordNF, e, sp, x, m, c, sp0, h, H, t0, s0, sw, wts;

   weylwordNF:= function( R, path )
   local   w,  rho,  wt, w1;        
    # the WeylWord in lex shortest form...
      w:= WeylWord( path );
      rho:= List( [1..Length( CartanMatrix(R))], x -> 1 );
      wt:= ApplyWeylElement( WeylGroup(R), rho, w );
      w1:= ConjugateDominantWeightWithWord( WeylGroup(R), wt )[2];
      return w1; 
   end;

   L:= LeftActingAlgebra( V );
   R:= RootSystem( L );
   h:= CanonicalGenerators( R )[3];
   hw:= HighestWeight( V );

   cg:= CrystalGraph( R, hw );
   paths:= cg.points;
   # For every path we compute its adapted string.
   strings:= [ ];
   for p in paths do
      p1:= p;
      st:= [];
      word:= weylwordNF( R, p1 );
      while word <> [] do
         j:= 0;
         k:= word[1];
         while  WeylWord( p1 ) <> [] and word[1] = k do
            p1:= Ealpha( p1, k );
            word:= weylwordNF( R, p1 );     
            j:= j+1;
         od;
         if j > 0 then
             Add( st, k );
             Add( st, j );
         fi;
      od;
      Add( strings, st );        
   od;

   y:= ChevalleyBasis( L )[2];
   sim:= SimpleSystem( R );
   posR:= PositiveRoots( R );
   yy:= [];
   for a in sim do
      pos:= Position( posR, a );
      Add( yy, y[pos] );
   od;
   y:= yy;
   sw:= SimpleRootsAsWeights(R);
   bas:= [ HighestWeightVector(V) ];
   wts:= [ HighestWeight(V) ];

   for i in [2..Length(strings)] do
     s1:= ShallowCopy( strings[i] );
     i1:= s1[1];
     n1:= s1[2];
     if n1 > 1 then
        s1[2]:= n1-1;
     else
        Unbind( s1[1] ); Unbind( s1[2] );
        s1:= Filtered( s1, x -> IsBound(x) );
     fi;
     pos:= Position( strings, s1 );
     w:= bas[pos];
     w:= yy[i1]^w;
     w:= w/n1;
     Add( bas, w );
     Add( wts, wts[pos]-sw[i1] );
  od;

  return [bas,wts];
end;



InstallMethod( Basis,
    "for an irreducible highest weight module",
    true, [ IsFreeLeftModule and IsLeftAlgebraModuleElementCollection and
    IsIrreducibleHWModule], 0,
    function( V )

    local   vecs;

    vecs:= SLAfcts.canbasofhwrep( V )[1];
    return BasisOfAlgebraModule( V, vecs );

end );


InstallMethod( IsomorphismOfIrreducibleHWModules,
    "for two irreducible highest weight modules",
    true, [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection,
    IsAlgebraModule and IsLeftAlgebraModuleElementCollection ], 0,
    function( V1, V2 )

    local b1, b2;

    if not (IsIrreducibleHWModule(V1) and IsIrreducibleHWModule(V2)) then
       return fail;
    fi;
    
    if HighestWeight(V1) <> HighestWeight(V2) then
       return fail;
    fi;

    b1:= SLAfcts.canbasofhwrep( V1 )[1];
    b2:= SLAfcts.canbasofhwrep( V2 )[1];
    return LeftModuleHomomorphismByImages( V1, V2, b1, b2 );
    

end );



SLAfcts.printdyndiag:= function( C, labs )

   local t, en, type, i, b, s, rank, offset, bound,lv;

   t:= CartanType(C);
   for lv in [1..Length(t.enumeration)] do
      if not lv = 1 then Print("\n"); fi;
      en:= t.enumeration[lv];
      if Length(labs) > 0 then en:= labs{en}; fi;
      rank:= Length(en);

      type:= t.types[lv][1];

      if type ="D" then
         offset:= Length(en)+ 3*(rank-3)+3;
	 if rank > 9 then offset:= offset+2; fi;
         s:= ""; for i in [1..offset] do Append( s, " "); od;
         Append(s," ");
         Append( s, String(en[rank-1]) );
         Append(s,"\n");
         Print(s);
         s:= ""; for i in [1..offset] do Append( s, " "); od;
         Append( s, "/\n" );
         Print(s);
      fi;

      if type ="E" then	 
         offset:= 12;
         s:= ""; for i in [1..offset] do Append( s, " "); od;
         Append( s, " " ); 
         Append( s, String(en[2]) );
         Append(s,"\n");
         Print(s);
         s:= " "; for i in [1..offset] do Append( s, " "); od;
         Append( s, "|\n" );
         Print(s);
      fi;  

      Print( t.types[lv][1], t.types[lv][2], ":  " );
      if type in ["A","B","C","F","G","E"] then
         bound:= rank;
      elif type = "D" then
         bound:= rank-2;
      fi; 
         for i in [1..bound] do
          if type <> "E" or i <> 2 then
             Print(en[i]);
          fi;

          if i < Length(en) then
      
             if type = "A" or (type in ["B","C"] and i < Length(en)-1) 
                     or (type = "D" and i < Length(en)-2) or (type="E" and i <> 2) 
                     or (type = "F" and i in [1,3] ) then
                Print( "---");
             elif type in ["B","C"] and i = Length(en)-1 then
                if type = "B" then
                   Print("=>=");
                else
                   Print("=<=");
                fi;
             elif type = "G" then
                Print("#<#");
             elif type ="F" and i=2 then
                Print("=>=");
             fi;
          fi;
      od;

      if type ="D" then
         s:= "\n"; for i in [1..offset] do Append( s, " "); od;
         Append( s, "\\\n" );
         Print(s);
         #offset:= Length(en) + 3*(rank-3)+3;
         s:= ""; for i in [1..offset] do Append( s, " "); od;
         Append(s," ");
         Append( s, String(en[rank]) );
         Append(s,"\n");
         Print(s);
      fi;

   od;

end;


InstallMethod( DisplayHighestWeight,
    "for an irred Lie algebra module",
    true, [ IsAlgebraModule and  IsLeftAlgebraModuleElementCollection], 0,
    function( V )

    local C, hw;

    if not IsIrreducibleHWModule(V) then
       Print("<V> is not an irreducible highest weight module");
    else
       C:= CartanMatrix( RootSystem(LeftActingAlgebra(V) ) );
       hw:= HighestWeight(V);
       SLAfcts.printdyndiag(C,hw);
    fi;
end);


InstallMethod( DisplayDynkinDiagram,
    "for a Cartan matrix",
    true, [ IsMatrix ], 0,
    function( C )

    SLAfcts.printdyndiag(C,[]);
end);

InstallOtherMethod( DisplayDynkinDiagram,
    "for a root system",
    true, [ IsRootSystem ], 0,
    function( R )

    SLAfcts.printdyndiag(CartanMatrix(R),[]);
end);

InstallOtherMethod( DisplayDynkinDiagram,
    "for a semisimple Lie algebra",
    true, [ IsLieAlgebra ], 0,
    function( L )

    SLAfcts.printdyndiag(CartanMatrix(RootSystem(L)),[]);
end);


WeightSpacesOfIrreduciblewHWModule:= function( V )

   local a, vv, wts, wts0, sp, w, ii;

   if HasBasis(V) and IsWeightRepElement( Basis(V)[1]![1] ) then
      vv:= BasisVectors( Basis(V) );
      wts:= Set( List( vv, x -> x![1]![1][1][3] ) );
      sp:= [ ];
      for w in wts do
          Add( sp, Subspace(V,Filtered( vv, x -> x![1]![1][1][3]=w),"basis"));
      od;
      return [ wts, sp ];
   fi;

   a:= SLAfcts.canbasofhwrep( V );
   vv:= a[1];
   wts:= a[2];
    
   wts0:= Set( wts );
   sp:= [ ];
   for w in wts0 do
       ii:= Filtered( [1..Length(wts)], i -> wts[i]=w );
       Add( sp, Subspace(V,vv{ii},"basis"));
   od;
   return [ wts0, sp ];

end;


InstallMethod( DualAlgebraModule,
        "for a left module over a Lie algebra", true,
        [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection ], 0,
        function( M )
    
    local L, Mstr, act, Bst, sp, bas, ff, aa, R, y, k, rhs, sol, Vst;
    
    L:= LeftActingAlgebra( M );
    if not IsLieAlgebra( L ) then TryNextMethod(); fi;
    Mstr:= DualSpace( M );

    act:= function( x, v ) # x in L, v in Mstr

          local bM, c, ev, k, a, pos;

          bM:= FamilyObj(v)!.basisV;
	  c:= List( [1..Dimension(M)], x -> Zero(LeftActingDomain(L)) );
	  ev:= ExtRepOfObj(v);
	  for k in [1,3..Length(ev)-1] do
	      pos:= Position( bM, ev[k+1] );
	      c[pos]:= ev[k];
	  od;
	  a:= [];
	  for k in [1..Dimension(M)] do
	      a[k]:= -c*Coefficients( bM, x^bM[k] );
	  od;
	  return a*Basis(Mstr);

    end;

    Bst:= Basis( Mstr );
    Vst:= LeftAlgebraModule( L, act, Mstr );

    if IsIrreducibleHWModule(M) then

       sp:= WeightSpacesOfIrreduciblewHWModule(M)[2];
       bas:= Concatenation( List( sp, Basis ) );
       ff:= BasisVectors( Basis(Mstr) );
       aa:= List( ff, f -> List( bas, v -> Image( f, v ) ) );
       R:= RootSystem( L );
       y:= CanonicalGenerators( R )[2];
       k:= PositionProperty( bas, v -> ForAll( y, x -> IsZero(x^v) ) );
       rhs:= List( ff, f -> Zero(LeftActingDomain(L)) );
       rhs[k]:= One( LeftActingDomain(L) );
       sol:= SolutionMat( aa, rhs );
       SetHighestWeightVector( Vst, sol*Basis(Vst) );
    fi;

    return Vst;

end );


