InfoSLA:=NewInfoClass("InfoSLA");
SetInfoLevel(InfoSLA,2);

SLAfcts:= rec();

InstallMethod( ExtendedCartanMatrix,
"for a root system", true, [ IsRootSystem ], 0,

function( R )

    local posR, hts, p, sim, B, C, i, j, v, a;

    posR:= PositiveRootsNF(R);
    hts:= List( posR, Sum);
    p:= Position( hts, Maximum(hts) );
    sim:= [-posR[p]];
    Append( sim, SimpleSystemNF(R) );

    B:= BilinearFormMatNF( R );
    C:= NullMat( Length(sim), Length(sim) );
    for i in [1..Length(sim)] do
        for j in [1..Length(sim)] do
            C[i][j]:= 2*( sim[i]*(B*sim[j]) )/( sim[j]*(B*sim[j]) );
        od;
    od;

    v:= NullspaceMat(C)[1];
    a:= Lcm( List( v, DenominatorRat ) );
    v:= a*v;

    return rec( ECM:= C, labels:= v );


end );



InstallMethod( CartanType,
"for a Cartan matrix", true, [IsMatrix], 0, 
function( C )


   # Here C is a Cartan matrix. We compute ts type,
   # as well as a standard enumeration of the vertices.
   
   local count_negs, comps, dones, i, j, k, l, m, cp, done, nonegs, o, types, ends,
         standard_orders;

   count_negs:= function( list )
        local c,i;
        c:= 0;
        for i in list do
            if i < 0 then c:= c+1; fi;
        od;
        return c;
   end;

   # First we split into irreducible components.
   comps:= [ ];
   dones:= [ ];
   while Length( dones ) <> Length( C ) do

       for i in [1..Length(C)] do
           if not i in dones then
              k:= i; break;
           fi;
       od;
       
       cp:= [ k ];
       j:= 1;
       done:= false;
       while not done do
           k:= cp[j];
           for i in [1..Length(C[k])] do
               if C[k][i] < 0 and not (i in cp) then
                  Add( cp, i ); 
               fi;
           od;
           if Length(cp) > j then
              j:= j+1;
           else  # i.e, we ran through the component...
              done:= true;  
           fi;
       od;
       Add( comps, cp );
       Append( dones, cp );
   od;

   # for each component we find its type.
   types:= [ ];
   standard_orders:= [ ];
   for cp in comps do
       if Length(cp) = 1 then
          Add( types, ["A",1] );
          Add( standard_orders, [cp[1]] );
       else
          nonegs:= List( cp, x -> count_negs( C[x] ) );

          if ForAll( nonegs, x -> x <=2 ) then  
             # An, Bn, Cn, F4, G2
             # find an "endpoint

             for i in [1..Length(nonegs)] do
                 if nonegs[i] = 1 then
                    k:= cp[i]; break;
                 fi;
             od;
             o:= [ k ];
             while Length(o) < Length(cp) do
                 for i in [1..Length(C[k])] do
                     if C[k][i] < 0 and not (i in o) then
                        k:= i; Add( o, k );
                        break;
                     fi;
                 od;
             od;
  
             k:= o[1]; j:= o[2]; 
             l:= o[Length(o)-1]; m:= o[Length(o)];       
             if C[k][j] <> C[j][k] then
                # Bn, Cn, G2
           
                if C[k][j]*C[j][k] = 3 then
                   Add( types, ["G",2] );
                   if C[k][j] = -1 then
                      Add( standard_orders, o );
                   else
                      Add( standard_orders, Reversed( o ) );
                   fi;
                else
                   if C[k][j] = -1 then
                      # i.e., second root long; Bn
                      Add( types, [ "B", Length(cp) ] );
                      Add( standard_orders, Reversed( o ) );
                   else
                      if Length(cp) = 2 then # not C after all...
                         Add( types, [ "B", 2 ] );
                         Add( standard_orders, o );
                      else
                         Add( types, [ "C", Length(cp) ] );
                         Add( standard_orders, Reversed( o ) );
                      fi;
                   fi;
                fi;
             elif C[l][m] <> C[m][l] then
                if C[m][l] = -1 then
                   # i.e., next to last root long; Bn
                   Add( types, [ "B", Length(cp) ] );
                   Add( standard_orders, o );
                else
                   if Length(cp) = 2 then # not C after all...
                      Add( types, [ "B", 2 ] );
                      Add( standard_orders, Reversed(o) );
                   else                   
                      Add( types, [ "C", Length(cp) ] );
                      Add( standard_orders, o );
                   fi;
                fi;
             elif Length(cp) = 4 then
                if C[j][l] <> C[l][j] then 
                   Add( types, [ "F", 4 ] );
                   if C[j][l] = -2 then
                      Add( standard_orders, o );
                   else
                      Add( standard_orders, Reversed( o ) );
                   fi;
                else
                   Add( types, [ "A", 4 ] );
                   Add( standard_orders, o );
                fi;
             else
                Add( types, [ "A", Length(cp) ] );
                Add( standard_orders, o );
             fi;

          else # Dn, E6,7,8

             # find the node...
             j:= cp[ PositionProperty( nonegs, x -> x = 3 ) ];
             ends:= [ ];
             for i in [1..Length(C[j])] do
                 if C[j][i] = -1 then
                    if count_negs( C[i] ) = 1 then
                       Add( ends, i );
                    fi;
                 fi;
             od;
             if Length( ends ) >= 2 then
                Add( types, [ "D", Length(cp) ] );
                if Length(cp) = 4 then
                   k:= ends[1];
                else
                   for i in [1..Length(nonegs)] do
                       if nonegs[i] = 1 and not (cp[i] in ends) then
                          k:= cp[i]; break;
                       fi;
                   od;
                fi;
                o:= [ k ];
                while Length(o) < Length(cp)-1 do
                    for i in [1..Length(C[k])] do
                        if C[k][i] < 0 and not (i in o) then
                           k:= i; Add( o, k );
                           break;
                        fi;
                    od;  
                od;
                for i in ends do
                    if not i in o then Add( o, i ); fi; 
                od;
                Add( standard_orders, o );
             else
                Add( types, [ "E", Length(cp) ] );       
                for i in cp do
                    if count_negs(C[i]) = 1 and not (i in ends) then
                       k:= PositionProperty( C[i], x -> x < 0 );
                       for j in [1..Length(C[k])] do
                           if C[k][j] < 0 and j <> i then
                              k:= j;
                              break;
                           fi;
                       od;
                       if count_negs(C[k]) = 3 then k:= i; break; fi;
                    fi;
                od;
                o:= [ k, ends[1] ];
                while Length(o) < Length(cp) do
                    for i in [1..Length(C[k])] do
                        if C[k][i] < 0 and not (i in o) and not (i in ends) then
                           k:= i; Add( o, k );
                           break;
                        fi;
                    od;  
                od;
                Add( standard_orders, o );
             fi;
          fi;
       fi;
   od;
   return rec( types:= types, enumeration:= standard_orders );

end );

SLAfcts.perms:= function( R )

     local N, p, i, a, b;
 
     N:= Length( PositiveRoots(R) );
     p:= ShallowCopy( WeylPermutations( WeylGroup(R) ) );
     for i in [1..Length(p)] do
         a:= ShallowCopy(p[i]);
         a[i]:= N+i;
         b:= List( a, x -> N+x );
         b[i]:= i;
         Append( a, b );
         p[i]:= a;
     od;

     return List( p, PermList );


end;

InstallMethod( WeylTransversal,
"for a root system, and a list of indices", true, [ IsRootSystem, IsList ], 0,
function( R, inds )


    # R: root system
    # inds: indices of *positive* roots that span a subsystem
    # Output: the set of shortest right coset reps of the corr
    # Weyl subgroup. 


     local B, rank, sub, in_sub_weylch, sim, cur_R, rho, reps, new_R, new_Pm,
           w, i, j, mu, w0, reduced, bas, gd, posR, sums, cur_Pm, pm, s, 
           p, k, N, crho, imgs, Pm, pmi; 

     if Length(inds) = 0 then

        # return all elements
        w:= WeylGroupAsPermGroup(R);
        return List( Elements(w), u -> PermAsWeylWord(R,u) );
     fi;    

    
     if IsList(inds[1]) then

        bas:= Basis( VectorSpace( Rationals, inds ), inds );
        gd:= function(r) 
             local c; 
             c:= Coefficients(bas,r);
             if c = fail then return false; fi; 
             return ForAll(c,IsInt) and 
                    (ForAll(c,x->x<=0) or ForAll(c,x->x>=0) ); 
        end;
        posR:= Filtered( PositiveRootsNF(R), gd );
        sums:=[ ];
        for i in [1..Length(posR)] do
            for j in [i+1..Length(posR)] do
                Add( sums, posR[i]+posR[j] );
            od;
        od;

        sim:= Filtered( posR, x -> not x in sums );
        inds:= List( sim, x -> Position(PositiveRootsNF(R),x) );

     fi;

     B:= BilinearFormMatNF(R);
     rank:= Length(B);

     N:= Length( PositiveRoots(R) );

     cur_R:= [ [] ];
     reps:= [ [] ];

     p:= SLAfcts.perms(R);

     cur_Pm:= [ () ];

     while Length(cur_R) > 0 do
 
         new_R:= [ ];
         new_Pm:= [ ];
         Pm:= [ ];

         for s in [1..Length(cur_R)] do

             for i in [1..rank] do

                 k:= i^cur_Pm[s];
                 if k <= N then

                    pm:= p[i]*cur_Pm[s];

                    if PositionSet( Pm, pm ) = fail then
                       pmi:= pm^-1;
                       imgs:= List( inds, x -> x^pmi );

                       if ForAll( imgs, x -> x <= N ) then
                          Add( new_R, Concatenation( cur_R[s], [i] ) );
                          Add( new_Pm, pm );
                          AddSet( Pm, pm );
                       fi;

                    fi;

                 fi;                 
             od;
         od;

         cur_R:= new_R;
         cur_Pm:= new_Pm;
         Append( reps, new_R );
     od;

     return reps;

end );


InstallMethod( WeylPermutations,
"for a Weyl group", true, [ IsWeylGroup ], 0,

function( W )

    local R, rank, posR, perms, i, j, p;

    R:= RootSystem(W);
    rank:= Length( CartanMatrix(R) );

    posR:= PositiveRootsAsWeights( R );
    perms:= [ ];
    for i in [1..rank] do
        p:= [ ];
        for j in [1..Length(posR)] do
            if j <> i then
               p[j]:= Position( posR, ApplyWeylElement( W, posR[j], [i] ) );
            else
               p[j]:= i;
            fi;
        od;
        Add( perms, p );
    od;

    return perms;


end );



InstallMethod( LengthOfWeylWord,
"for a Weyl group and word", true, [ IsWeylGroup, IsList ], 0,

function( W, w )

    local p, v, N, len, i, j, k, sign;

    p:= WeylPermutations( W );
    v:= Reversed( w );
    N:= Length( p[1] ); # ie the number of pos roots.
    len:= 0;
    for i in [1..N] do

        # see whether w(i-th pos root) is negative

        k:= i; sign:= 1;
        for j in v do
            if j = k then
               sign:= -sign;
            else
               k:= p[j][k];
            fi;
        od;

        if sign = -1 then len:= len+1; fi;
    od;

    return len;

end );


SLAfcts.sizeofweylgrp:= function( tp )

    local size, i, s, r;

    size:= 1;
    for i in [1..Length(tp)] do
        s:= tp[i][1]; r:= tp[i][2];
        if s = "A" then
           size:= size*Factorial( r+1 );
        elif s = "B" or s = "C" then           
           size:= size*( 2^r*Factorial(r) );
        elif s = "D" then
           size:= size*( 2^(r-1)*Factorial(r) );
        elif s = "E" then
           if r = 6 then
              size:= size*51840;
           elif r = 7 then
              size:= size*2903040;
           else
              size:= size*696729600;
           fi;
        elif s ="F" then
           size:= size*1152;
        elif s = "G" then
           size:= size*12;
        else
           Error("wrong input");
        fi;
    od;

    return size;

end;

InstallMethod( SizeOfWeylGroup,
"for a root system", 
true, [ IsRootSystem ], 0,

function(R) 
return SLAfcts.sizeofweylgrp( CartanType( CartanMatrix(R) ).types );
end );

InstallMethod( SizeOfWeylGroup,
"for a list", 
true, [ IsList ], 0,

function(tp) 
return SLAfcts.sizeofweylgrp( tp );
end );

InstallMethod( SizeOfWeylGroup,
"for a simple type", 
true, [ IsString, IsInt ], 0,

function(s,n) 
return SLAfcts.sizeofweylgrp( [[s,n]] );
end );


InstallMethod( AdmissibleLattice,
"for an irreducible module over a semisimple Lie algebra", 
true, [ IsAlgebraModule ], 0,

function( V )

  local   L,  R,  hw,  cg,  paths,  strings,  p,  p1, word, k, b,
          st,  i,  j,  a,  y,  v,  bas, s1, i1, n1,  w,  sim, pos, posR, yy, 
          weylwordNF, hwv, e, sp, x, m, c, sp0, h;



weylwordNF:= function( R, path )
        
    local   w,  rho,  wt;
        
    # the WeylWord in lex shortest form...
    w:= WeylWord( path );
    rho:= List( [1..Length( CartanMatrix(R))], x -> 1 );
    wt:= ApplyWeylElement( WeylGroup(R), rho, w );
    return ConjugateDominantWeightWithWord( WeylGroup(R), wt )[2];

end;

   L:= LeftActingAlgebra( V );
   R:= RootSystem( L );

   if IsWeightRepElement( ExtRepOfObj(Basis(V)[1]) ) then
      hw:= Basis(V)[1]![1]![1][1][3];
      hwv:= Basis(V)[1];
   else
      e:= CanonicalGenerators( R )[1];
      sp:= V;
      for x in e do
          m:= MatrixOfAction( Basis(V), x );
          m:= TransposedMatDestructive(m);
          c:= NullspaceMat(m);
          sp0:= Subspace( V, List( c, u -> u*Basis(V) ), "basis" );
          sp:= Intersection( sp, sp0 );
      od;
      if Dimension(sp) > 1 then Error("The module <V> must be irreducible"); fi;
      h:= CanonicalGenerators( R )[3];
      hw:= List( h, x -> Coefficients( Basis(sp), x^Basis(sp)[1] )[1] );
      hwv:= Basis(sp)[1];
   fi;

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

      y:= ChevalleyBasis(L)[2];
      sim:= SimpleSystem( R );
      posR:= PositiveRoots( R );
      yy:= [];
      for a in sim do
          pos:= Position( posR, a );
          Add( yy, y[pos] );
      od;
      y:= yy;

      bas:= [ hwv ];
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
      od;

   return Basis( V, bas );
  
end ); 


############################ functions for Weyl groups as perm groups ######

InstallMethod( WeylGroupAsPermGroup,
"for a root system", true, [ IsRootSystem ], 0,

function( R )

    local W;

    W:= Group( SLAfcts.perms(R) );
    W!.rootSystem:= R;
    return W; 

end );

InstallMethod( ApplyWeylPermToWeight, 
"for a root system a permutation and a list", true, 
[ IsRootSystem, IsPerm, IsList ], 0,

function( R, p, lam )

    local W, sim, cf, pr, N, im, i, j;

    if p = () then return lam; fi;

    W:= WeylGroupAsPermGroup( R );
    if not IsBound( W!.wtSpace ) then
       sim:= SimpleRootsAsWeights(R);
       W!.wtSpace:= Basis( VectorSpace( Rationals, sim ), sim );
    fi;
    cf:= Coefficients( W!.wtSpace, lam );
    
    pr:= PositiveRootsAsWeights( R );
    N:= Length(pr);
    im:= 0*lam;
    for i in [1..Length(cf)] do
        j:= i^p;
        if j <= N then
           im:= im + cf[i]*pr[j];
        else
           im:= im - cf[i]*pr[j-N];
        fi;
    od;

    return im;

end );

InstallMethod( WeylWordAsPerm,
"for root system and a list", true, [ IsRootSystem, IsList ], 0,

function( R, u )

    local W, p, v;

    if Length(u) = 0 then return (); fi;
    W:= WeylGroupAsPermGroup(R);
    p:= GeneratorsOfGroup(W);
    v:= Reversed(u);
    return Product( v, i -> p[i] );

end );

InstallMethod( PermAsWeylWord,
"for a root system and a permutation", true, [ IsRootSystem, IsPerm ], 0,

function( R, p )

    local rho, im;

    rho:= List( CartanMatrix(R), i -> 1 );
    im:= ApplyWeylPermToWeight( R, p, rho );
    return ConjugateDominantWeightWithWord( WeylGroup(R), im )[2];

end );


InstallMethod( ApplyWeylPermToCartanElement,
"for Lie algebra, permutation and Cartan elt", true, 
[ IsLieAlgebra, IsPerm, IsObject ], 0,

function( L, w, h )

       local W, ch, hh, cf, ha, N, im, i, j;

       W := WeylGroupAsPermGroup( RootSystem(L) );
       if not IsBound( W!.hSpace ) then
          ch:= ChevalleyBasis(L);
          hh:= ch[3];
          W!.hSpace:= Basis( VectorSpace( LeftActingDomain(L), hh ), hh );
	  W!.halphas:= List( [1..Length(ch[1])], i -> ch[1][i]*ch[2][i] ); 
       fi;

       cf:= Coefficients( W!.hSpace, h );
       if cf = fail then return fail; fi;
       
       ha:= W!.halphas;
       N:= Length( ha );
       im:= 0*h;
       for i in [ 1 .. Length( cf ) ] do
           j := i^w;
           if j <= N then
              im := im + cf[i] * ha[j];
           else
              im := im - cf[i] * ha[(j - N)];
          fi;
       od;
       return im;
end );
       