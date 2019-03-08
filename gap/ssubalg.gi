SLAfcts.highest_root:= function( type )

     # here type is a list, e.g., [ "B", 5 ] -- we return the
     # coefficients of the highest root of the root system

     local t, rank, c;

     t:= type[1]; rank:= type[2];

     if t = "A" then
        c:= List( [1..rank], x -> 1 );
     elif t = "B" then
        c:= [1];
        Append( c, List( [2..rank], x -> 2 ) );
     elif t = "C" then
        c:= List( [1..rank-1], x -> 2 );
        Add( c, 1 );
     elif t = "D" then
        c:= [1];
        Append( c, List( [2..rank-2], x -> 2 ) );
        Append( c, [1,1] );
     elif t = "E" and rank = 6 then
        c:= [ 1, 2, 2, 3, 2, 1 ];
     elif t ="E" and rank = 7 then
        c:= [ 2, 2, 3, 4, 3, 2, 1 ];
     elif t = "E" and rank = 8 then
        c:= [ 2, 3, 4, 6, 5, 4, 3, 2 ];
     elif t ="F" then
        c:= [ 2, 3, 4, 2 ];
     elif t = "G" then
        c:= [ 3, 2 ];
     fi;

     return c;

end;


SLAfcts.derived_systems:= function( B, p )

     # here p is a pi-system, B matrix of the bilinear form.

     local rts, tps, der, i, j, k, l, rts0, tps0, c, rr, rank, C, t, rt, 
           tp, e, r;
     
     rts:= p.roots;
     tps:= p.types;

     der:= [ ];

     for i in [1..Length(tps)] do

         rts0:= List( rts, x -> ShallowCopy(x) );
         tps0:= List( tps, x -> ShallowCopy(x) );
         RemoveElmList( rts0, i );
         RemoveElmList( tps0, i );

         c:= -SLAfcts.highest_root( tps[i] );
         c:= c*rts[i];
         for j in [1..Length(rts[i])] do
             rr:= ShallowCopy( rts[i] );
             rr[j]:= c;
             rank:= Length(rr);
             C:= NullMat( rank, rank );
             for k in [1..rank] do
                 for l in [1..rank] do
                     C[k][l]:= 2*rr[k]*(B*rr[l])/( rr[l]*(B*rr[l]) );
                 od;
             od;

             t:= CartanType( C );

             if not ( Length(t.types) = 1 and t.types[1] = tps[i] ) then

                rt:= List( rts0, ShallowCopy );
                tp:= List( tps0, ShallowCopy );
                for k in [1..Length(t.types)] do
                    e:= t.enumeration[k];
                    r:= [ ];
                    for l in [1..Length(e)] do
                        Add( r, rr[ e[l] ] );
                    od;
                    Add( rt, r );
                    Add( tp, t.types[k] );
                od;
                Add( der, rec( roots:= rt, types:= tp ) );
             fi;
         od;
     od;

     return der;

end;


SLAfcts.pi_systems_0:= function( R )
     
     # We assume R is a simple root system.

     local C, t, e, rts, i, p, res, newpis, news, x, B;

     C:= CartanMatrix(R);
     t:= CartanType( C );

     B:= BilinearFormMatNF(R);

     e:= t.enumeration[1];
     rts:= [ ];
     for i in [1..Length(e)] do
         Add( rts, SimpleSystemNF(R)[ e[i] ] );
     od;
     p:= rec( roots:= [rts], types:= t.types );

     res:= [ p ];
     newpis:= [ p ];
     while newpis <> [ ] do

         news:= [ ];
         for x in newpis do
             Append( news, SLAfcts.derived_systems( B, x ) );
         od;

         newpis:= news;
         Append( res, newpis );
     od;

     return res;

end;


# now some functions for dealing with sub-Weyl groups
# They are given as records: W.roots gives the roots
# as weights rel to the big root system, W.wgts, gives
# the simple roots as weights rel to the small root system.

SLAfcts.conj_dom_wt:= function( wt, relwt, W )

    # Here wt is a weight (rel to the big root system).
    # relwt is the weight rel to the small root system (i.e., 
    # the vector of values < mu, \beta_i^\vee >, i = 1,..,m.
    # W a sub-Weyl group datum..
    # We compute the dominant weight (rel to small root sys) 
    # conj to wt, we output the dom wt, its rel wt, and the word,
    # in terms of the generators of W that maps the weight
    # to the dominant one.

    local lam, rlam, pos, w;
     
    lam:= ShallowCopy( wt );
    rlam:= ShallowCopy( relwt );
    pos:= PositionProperty( rlam, x -> x < 0 );
    w:= [ ];
    while pos <> fail do

       Add( w, pos );
       lam:= lam - rlam[pos]*W.roots[pos];
       rlam:= rlam - rlam[pos]*W.wgts[pos];
       pos:= PositionProperty( rlam, x -> x < 0 );
    od;

    return [ lam, rlam, Reversed(w) ];


end;

SLAfcts.stabilizer:= function( wt, B, W )

    # Here W is a sub-Weyl group, and wt a weight rel to
    # the big root system R. B is the matrix of the bilin form
    # wrt weight basis (in the big root system).
    # we find generators of the stabiliser of wt in W,
    # output as a sub-Weyl group

    local relwt, d, inds, i, j, g, w, rt, relt, CM;

    relwt:= List( W.roots, x -> 2*wt*(B*x)/( x*(B*x) ) );

    d:= SLAfcts.conj_dom_wt( wt, relwt, W );

    inds:= [ ];
    for i in [1..Length(d[2])] do
        if d[2][i] = 0 then Add( inds, i ); fi;
    od;

    g:= [ ];

    w:= d[3];

    for i in inds do
        rt:= ShallowCopy(W.roots[i]);
        relt:= ShallowCopy(W.wgts[i]);

        # apply w...

        for j in w do
            rt:= rt - relt[j]*W.roots[j];
            relt:= relt - relt[j]*W.wgts[j];
        od;
        Add( g, rt );

    od;

    CM:= List( g, x -> List( g, y -> 2*x*(B*y)/( y*(B*y) ) ) );

    return rec( roots:= g, wgts:= CM );


end;


SLAfcts.bilin_weights:= function( R )

   # The bilin form mat wrt basis of fund weights...

   local sp, rank, B, b, bas, i, j, c;

   sp:= Basis( VectorSpace( Rationals, SimpleRootsAsWeights(R) ),
            SimpleRootsAsWeights(R) );

   rank:= Length( CartanMatrix(R) );
   B:= NullMat( rank, rank );
   b:= BilinearFormMatNF( R );
   bas:= IdentityMat( rank );
   for i in [1..rank] do
       for j in [i..rank] do
           c:= Coefficients( sp, bas[i] )*( b*Coefficients(sp,bas[j]) );
           B[i][j]:= c; B[j][i]:= c;
       od;
   od;

   return B;

end;



SLAfcts.are_conjugate_0:= function( R, B, mus, lams )


   # R is the big root system, B the bilin form mat wrt weights,
   # mus and lams are lists of weights, we determine whether
   # there exists w in W wich w(mus[i]) = lams[i], all i.

   local sim, W, i, j, k, a, b, w, mu, rmu;

   sim:= SimpleRootsAsWeights( R );
   W:= rec( roots:= sim, wgts:= sim );

   for i in [1..Length(mus)] do

       rmu:= List( W.roots, x -> 2*mus[i]*( B*x )/( x*(B*x) ) );
       a:= SLAfcts.conj_dom_wt( mus[i], rmu, W );

       rmu:= List( W.roots, x -> 2*lams[i]*( B*x )/( x*(B*x) ) );
       b:= SLAfcts.conj_dom_wt( lams[i], rmu, W );

       if a[1] <> b[1] then return false; fi;

       w:= Reversed( b[3] );
       Append( w, a[3] );
       w:= Reversed(w);

       for k in [i..Length(mus)] do

           mu:= ShallowCopy(mus[k]);
           rmu:= List( W.roots, x -> 2*mu*( B*x )/( x*(B*x) ) );

           for j in w do

               mu:= mu -rmu[j]*W.roots[j];
               rmu:= rmu - rmu[j]*W.wgts[j];

           od;

           mus[k]:= mu;

       od;

       W:= SLAfcts.stabilizer( lams[i], B, W );

   od;

   return true;


end;


SLAfcts.are_conjugate:= function( R, B, mus, lams )


   # same as previous function, but now we also permute
   # the mus, lams. We do assume that they arrive in an
   # order that defines the same Cartan matrix...

   local C, perms, i, newperms, p, q, good, j, k, l, nus;

   # however,... first we try the identity permutation...

   if SLAfcts.are_conjugate_0( R, B, mus, lams ) then
      return true;
   fi;
   
   # The Cartan matrix: 
   C:= List( mus, x -> List( mus, y -> 2*x*(B*y)/( y*(B*y) ) ) );

   # Now we determine all permutations of the mus that leave C invariant:

   perms:= List( [1..Length(mus)], x -> [x] );
   # i.e., the first element can be mapped to one of the other elts.
   # now we see whether this can be extended...

   for i in [2..Length(mus)] do

       newperms:= [ ];
       for p in perms do
           for j in [1..Length(mus)] do
               # see whether p can be extended by adding j...
               if not j in p then
                  q:= ShallowCopy(p);
                  Add( q, j );
                  good:= true;
                  for k in [1..i] do
                      if not good then break; fi;
                      for l in [1..i] do
                          if not good then break; fi;
                          if C[k][l] <> C[ q[k] ][ q[l] ] then
                             good:= false;
                          fi;
                      od;
                  od;
                  if good then Add( newperms, q ); fi;
               fi;
           od;
       od;
       perms:= newperms;
   od;

   perms:= Filtered( perms, x -> x <> [1..Length(mus)] ); # already tried it
   
   # now we see whether there is a permutation mapping 
   # a permuted mus to lams...

   for p in perms do

       nus:= [ ];
       for i in [1..Length(p)] do
           nus[p[i]]:= mus[i];
       od;

       if SLAfcts.are_conjugate_0( R, B, nus, lams ) then
          return true;
       fi;
   od;

   return false;

end;


SLAfcts.pi_systems:= function( R )

   # simple root system...

   local pis, B, sim, roots, types, p, tps, rts, mus, pos, found, i; 

   pis:= SLAfcts.pi_systems_0(R);
   B:= SLAfcts.bilin_weights( R );
   sim:= SimpleRootsAsWeights(R);

   roots:= [ ];
   types:= [ ];

   for p in pis do
       tps:= p.types;
       rts:= p.roots;

       SortParallel( tps, rts );

       mus:= Concatenation( List( rts, x -> List( x, y -> y*sim ) ) );

       pos:= Position( types, tps );
       if pos = fail then
          Add( types, tps );
          Add( roots, mus );
       else
          
          found:= false;
          for i in [pos..Length(types)] do
              if types[i] = tps then      
                 
                 if SLAfcts.are_conjugate( R, B, mus, roots[i] ) then
                    found:= true; break;
                 fi;
 
              fi;
          od;
          if not found then 
             Add( types, tps );
             Add( roots, mus );
          fi;

       fi; 

   od;

   return rec( types:= types, roots:= roots );


end;


SLAfcts.sub_systems:= function( R )

   # simple root system..., we give reps of all orbits of
   # sub root systems under the Weyl group

   local pis, B, roots, types, tps, rts, mus, pos, found, i, j, k, comb,
         r0, c, C, r1, tp, e, u, t1, rank; 

   pis:= SLAfcts.pi_systems(R);
   B:= SLAfcts.bilin_weights( R );

   roots:= [ ];
   types:= [ ];

   rank:= Length(B);
   comb:= Combinations( [1..rank] );
   comb:= Filtered( comb, x -> (x <> [] and Length(x) <> rank ) );


   for i in [1..Length(pis.types)] do
       tps:= pis.types[i];
       rts:= pis.roots[i];

       Add( roots, rts );
       Add( types, tps );


       for c in comb do

           r0:= rts{c};
           # find its type in normal enumeration...

           C:= List( r0, x -> List( r0, y -> 2*x*(B*y)/(y*(B*y)) ) );
           tp:= CartanType( C );

           e:= tp.enumeration;
           r1:= [ ];
           for j in [1..Length(e)] do
               u:= [ ];
               for k in e[j] do
                   Add( u, r0[k] );
               od;
               Add( r1, u );
           od;

           t1:= tp.types;
           SortParallel( t1, r1 );

           mus:= Concatenation( r1 );

           pos:= Position( types, t1 );
           if pos = fail then
              Add( types, t1 );
              Add( roots, mus );
           else
          
              found:= false;
              for j in [pos..Length(types)] do
                  if types[j] = t1 then      
                 
                     if SLAfcts.are_conjugate( R, B, mus, roots[j] ) then
                        found:= true; break;
                     fi;
  
                  fi;
              od;
              if not found then 
                 Add( types, t1 );
                 Add( roots, mus );
              fi;

           fi; 
       od;
   od;

   return rec( types:= types, roots:= roots );


end;

InstallMethod( RegularSemisimpleSubalgebras,
"for a Lie algebra", true, [ IsLieAlgebra ], 0,

function( L )

   local R, s, posRw, ch, xL, yL, algs, i, j, r, x, y, pos, K, tL, tK, 
         h, fund, rt, sp, CartInt, posR, posRv, oldR, oldRv, negR, negRv,
         oldneg, newneg, newR, newRv, allrts, C, RK, k, u;

    CartInt := function( R, a, b )
       local s,t,rt;
       s:=0; t:=0;
       rt:=a-b;
       while (rt in R) or (rt=0*R[1]) do
         rt:=rt-b;
         s:=s+1;
       od;
       rt:=a+b;
       while (rt in R) or (rt=0*R[1]) do
         rt:=rt+b;
         t:=t+1;
       od;
       return s-t;
    end;

   
   R:= RootSystem(L);
   s:= SLAfcts.sub_systems( R );

   posRw:= PositiveRootsAsWeights( R );
   ch:= ChevalleyBasis(L);
   xL:= ch[1]; yL:= ch[2];

   tL:= SemiSimpleType(L);

   algs:= [ ];
   for i in [1..Length(s.roots)] do

       tK:= Concatenation( s.types[i][1][1], String( s.types[i][1][2] ) );
       if tK <> tL then

          r:= s.roots[i];
          x:= [ ]; y:= [ ];
          for j in [1..Length(r)] do
              pos:= Position( posRw, r[j] );
              if pos <> fail then
                 Add( x, xL[pos] );
                 Add( y, yL[pos] );
              else
                 pos:= Position( posRw, -r[j] );
                 Add( x, yL[pos] );
                 Add( y, xL[pos] );
              fi;
          od;

          K:= Subalgebra( L, Concatenation( x, y ) );

          # make the root system of K...
          h:= List( [1..Length(x)], k -> x[k]*y[k] );
          SetCartanSubalgebra( K, Subalgebra(K,h) );

          fund:= [ ];
          for j in [1..Length(x)] do
              rt:= [ ];
              sp:= Basis( Subspace(L,[x[j]]), [x[j]] );
              for k in [1..Length(h)] do
                  Add( rt, Coefficients( sp, h[k]*x[j] )[1] );
              od;
              Add( fund, rt );
          od;

          posR:= ShallowCopy( fund );
          posRv:= ShallowCopy( x );
          oldR:= ShallowCopy(fund);
          oldRv:= ShallowCopy( x );

          negR:= List( fund, q -> -q );
          negRv:= ShallowCopy(y);
          oldneg:= ShallowCopy( negRv );

          while oldR <> [ ] do
              newR:= [ ];
              newRv:= [ ];
              newneg:= [ ];
              for j in [1..Length(fund)] do
                  for k in [1..Length(oldR)] do
                      u:= x[j]*oldRv[k];
                      if not IsZero( u ) then
                         rt:= fund[j]+oldR[k];
                         if not rt in newR then
                            Add( newR, rt );
                            Add( newRv, u );
                            Add( newneg, y[j]*oldneg[k] );
                         fi;
                      fi;
                  od;
              od;
              Append( posR, newR );
              Append( posRv, newRv );
              Append( negR, -newR );
              Append( negRv, newneg );
              oldR:= newR; oldRv:= newRv;
              oldneg:= newneg;
          od;
             
          allrts:= Concatenation( posR, negR );            

          C:= List( fund, a -> List( fund, b -> CartInt( allrts, a, b ) ) );

          RK:= Objectify( NewType( NewFamily( "RootSystemFam", IsObject ),
                     IsAttributeStoringRep and IsRootSystemFromLieAlgebra ), 
                     rec() );
          SetCanonicalGenerators( RK, [ x, y, h ] );
          SetUnderlyingLieAlgebra( RK, K );
          SetPositiveRootVectors( RK, posRv );
          SetNegativeRootVectors( RK, negRv );
          SetCartanMatrix( RK, C );
    
          SetPositiveRoots( RK, posR );
          SetNegativeRoots( RK, negR ); 
          SetSimpleSystem( RK, fund );
          SetRootSystem( K, RK );

          Add( algs, K );
       fi;
   od;

   return algs;

end );


#    Functions for computing the closed subsystems of root systems
#    up to conjugacy by the Weyl group.
#
#
# the addition table of the roots will always be Q
# if a sum is not a root, then the entry is 0, otherwise the index of the root.

# Also note that if a is a root with index i then -a has index i+n0 mod 2n0,
# where n0 is the number of positive roots.


SLAfcts.clos:= function( rts, S )
        
        local i,j, a, T, added, start, start0, u;

        T:= ShallowCopy(S);
        added:= true;
        start:= 1;
        while added do
           added:= false; start0:= Length(T);
           for i in [1..Length(T)] do
               u:= Maximum( start, i+1 );
               for j in [u..Length(T)] do
                   a:= T[i]+T[j];
                   if (a in rts) and (not a in T) then
                      Add( T, a );
                      added:= true;
                   fi;
               od;
           od;
           start:= start0+1;   
        od;
        return T;

end;

SLAfcts.dynkintable:= function( type, rank )

        local defseq, R, s, Pw, rts, sys, r, sim;

        defseq:= function( rk, rts, r )

          local sim, pos, ip, s, sq;

          sim:= rts{[1..rk]};
          pos:= PositionProperty( r, x -> x <> 0 );
          if r[pos] > 0 then
             ip:= true;
             s:= ShallowCopy(r);
          else
             ip:= false;
             s:= -ShallowCopy(r);
          fi;

          sq:= [ ];
          while not IsZero(s) do
              pos:= PositionProperty( sim, x -> s-x in rts );
              if pos = fail then
                 pos:= Position( sim, s );
              fi;
              Add( sq, pos );
              s:= s-sim[pos];
          od;

          return [ ip, Reversed(sq) ];

        end;

        R:= RootSystem( type, rank );
        s:= SLAfcts.sub_systems(R);
        Pw:= PositiveRootsAsWeights(R);
        Pw:= Concatenation( Pw, -Pw );
        rts:= Concatenation( PositiveRootsNF(R), -PositiveRootsNF(R) );
	    sys:= [ ];
	    for r in s.roots do
	       sim:= List( r, x -> rts[ Position( Pw, x ) ] );
	       sim:= Concatenation( sim, -sim );
	       Add( sys, SLAfcts.clos( rts, sim ) );
        od;
        sys:= List( sys, x -> List( x, y -> defseq( rank, rts, y ) ) );
	    return rec( type:= type, sys:= sys );

end;

SLAfcts.semsim:= function(s,H,n0,rts,Q,B,ipmat)


        local setss, rows, sm, max, r, a, b, c, k, l, iscl, sums, bas, C, tp,
              sets, set, n, T, zyz, m, s0, pos, U, mat, j, p0, conj, i, ind, u;


        T:= [ ];

        setss:= [ ];
        rows:= [ ];

        sm:= Sum(rts{s});
        max:= [ ];  # max set that can be added...(just the pos rts)

        for r in [1..n0] do
            if (not r in s) and (not r+n0 in s) and (rts[r]*B*sm = 0) then
               iscl:= true;
               for a in s do
                   b:= Q[a][r]; c:= Q[a][r+n0];
                   if (b<>0 and not b in s) or (c<>0 and not c in s) then
                      iscl:= false; break;
                   fi;
               od;
               if iscl then Add( max, r ); fi;
            fi;
        od;

        if Length(max) >0 then

           sums:= [];
           for k in max do for l in max do Add( sums, Q[k][l] ); od; od;
           bas:= Filtered( max, x -> not x in sums );
           C:= List( bas, x -> List( bas, y -> 2*ipmat[x][y]/ipmat[y][y]));
           tp:= CartanType(C);
           sets:= [ ];

           for k in [1..Length(tp.types)] do
               set:= [ [] ];
               n:= tp.types[k][2];
               if not IsBound( T[n] ) then T[n]:= [ ]; fi;
               l:= PositionProperty( T[n], x -> x.type[1] =
                                                      tp.types[k][1] );
               if l = fail then
                  Add( T[n], SLAfcts.dynkintable( tp.types[k][1], n ) );
                  l:= Length( T[n] );
               fi;
               zyz:= T[n][l].sys;
               for m in [1..Length(zyz)] do
                   s0:= [ ];
                   for r in zyz[m] do
                       if r[1] then
                          u:= bas[tp.enumeration[k][r[2][1]]];
                          for j in [2..Length(r[2])] do
                              u:= Q[u][bas[tp.enumeration[k][r[2][j]]]];
                          od;
                          Add( s0, u );
                       fi;
                   od;
                   Add( set, s0 );
               od;
               Add( sets, set );
           od;
           # now make unions...

           ind:= List( sets, x -> 1 );
           k:= 1;
           while k <> 0 do

               s0:= Concatenation( List( [1..Length(ind)], j ->
                                                      sets[j][ind[j]] ) );
               s0:= Concatenation( s0, List( s0, x -> 
                                              ((x+n0) mod (2*n0)) ) );
               pos:= Position( s0, 0 );
               if pos <> fail then s0[pos]:= 2*n0; fi;
               U:= Concatenation( s0, s );
               Sort(U);
               mat:= List( U, x -> [ ] );
               for j in [1..Length(U)] do
                   for l in [j..Length(U)] do
                       mat[j][l]:= ipmat[U[j]][U[l]];
                       mat[l][j]:= mat[j][l];
                   od;
               od;

               p0:= List( mat, Sum ); Sort(p0);
               conj:= false;
               for l in [1..Length(setss)] do
                   if Length(setss[l]) = Length(U) and
                      p0 = rows[l] and
                      RepresentativeAction(H,setss[l],U,OnSets) <> fail then
                         conj:= true; break;
                   fi;
               od;
               if not conj then
                  Add( setss, U );
                  Add( rows, p0 );
               fi;
                
               k:= 0;
               for i in [1..Length(ind)] do
                   if ind[i] < Length(sets[i]) then k:= i; break; fi;
               od;

               if k > 0 then
                  for i in [1..k-1] do ind[i]:= 1; od;
                  ind[k]:= ind[k]+1;
               fi;
           od;
        else
           setss:= [s];
        fi;
 
        return setss;

end;

SLAfcts.normaliser_ofclset:= function( S, n0, Q )
                                # all a such that a+b in S for all b in S
                                # if a+b is a root; assume S closed...
                                # we return the part that is not in S

        local res, x, b, good, c;

        res:= [ ];
        for x in [1..n0] do
            good:= true;
            if not x in S then #and not ((x+n0) mod (2*n0)) in S then
               for b in S do
                   c:= Q[b][x];
                   if c <> 0 and not c in S then
                      good:= false;
                      break;
                   fi;
               od;
               if good then AddSet( res, x ); fi;
            fi;
        od;
        return res;
end;


SLAfcts.normalvec:= function( R, v )

        # v is a vector with rational coordinates of length rank(R).
        # we compute the W-conjugate lying in the dominant Weyl chamber.

        local w, rank, j;

        w:= ShallowCopy(v);
        rank:= Length( CartanMatrix(R) );
        j:= First( [1..rank], x -> w[x] < 0 );

        while j <> fail do
            w:= w - w[j]*SimpleRootsAsWeights(R)[j];
            j:= First( [1..rank], x -> w[x] < 0 );
        od;

        return w;

end;

SLAfcts.normalvec_plus:= function( R, perms, v )

        # v is a vector with rational coordinates of length rank(R).
        # we compute the W-conjugate lying in the dominant Weyl chamber.

        local w, rank, j, g;

        w:= ShallowCopy(v);
        rank:= Length( CartanMatrix(R) );
        j:= First( [1..rank], x -> w[x] < 0 );

        g:= perms[1]^0;

        while j <> fail do
            w:= w - w[j]*SimpleRootsAsWeights(R)[j];
            g:= g*perms[j];
            j:= First( [1..rank], x -> w[x] < 0 );
        od;

        return rec( vec:= w, g:= g );

end;


InstallMethod( ClosedSubsets,
"for a root system", true, [ IsRootSystem ], 0,


function(R)

        local p, G, pr, n0, rts, prw, Q, k, l, p0, B, rank, ipmat, Bvals, SS,
              closeds, newSS, rows, dets, i, S, T, d0, gg, G0, nn, G1, conj,
              H, N, D, o, j, pos, vecs, v0, mat, vals, val, ind, cnt, cj, orbs,
              n0exp, t0, stab, gens, sys, sim, Pw, r, s;

        p:= SLAfcts.perms(R);
        G:= Group(p);

        pr:= PositiveRootsNF(R);
        n0:= Length( pr );
        rts:= Concatenation( pr, -pr );

        prw:= PositiveRootsAsWeights(R);
        prw:= Concatenation( prw, -prw );

        Q:= List( rts, x -> [] );
        for k in [1..2*n0] do
            for l in [1..2*n0] do
                p0:= Position( rts, rts[k]+rts[l] );
                if p0 = fail then p0:= 0; fi;
                Q[k][l]:= p0;
            od;
        od;


        B:= BilinearFormMatNF(R);
        rank:= Length(B);
        ipmat:= List( rts, x -> [ ] );
        for k in [1..Length(rts)] do
            for l in [k..Length(rts)] do
                ipmat[k][l]:= rts[k]*B*rts[l];
                ipmat[l][k]:= ipmat[k][l];
            od;
        od;

        Bvals:= Set( Flat( ipmat ) );
        nn:= Maximum(Bvals)-Minimum(Bvals)+2;
        n0exp:= List( [1..Length(Bvals)], i -> nn^(i-1) );

        # a closed subsystem is represented by a list of the indices of its
        # elements

        SS:=[    List( [1..n0], x -> x )     ];
        closeds:= []; 
       
        while Length(SS) > 0  do

            newSS:= [ ];
            rows:= [ ];
            dets:= [ ];

            for i in [1..Length(SS)] do
                S:= ShallowCopy( SS[i] );
                d0:= SLAfcts.normalvec_plus( R, p, Sum( prw{S} ) );
                gg:= p{ Filtered( [1..Length(CartanMatrix(R))],
                                i -> d0.vec[i]=0 ) };
                stab:= false;
                if Length(gg) = 0 then
                   G0:= Group( () );
                   stab:= true;
                else
                   gens:= List( gg, x -> (d0.g)*x*d0.g^-1 );
                   if ForAll( gens, p -> ForAll( S, i -> i^p in S ) ) then
                      stab:= true;
                   fi;
                   G0:= Group( gens );
                fi;

                if not stab then

                   nn:= Filtered( [1..2*n0], x -> ForAll( S, y -> ipmat[x][y]
                           >= -1 ) );
                   d0:= SLAfcts.normalvec_plus( R, p, Sum( prw{nn} ) );
                   gg:= p{ Filtered( [1..Length(CartanMatrix(R))],
                                                     i -> d0.vec[i]=0 ) };
                   if Length(gg) = 0 then
                      G1:= Group( () );
                      stab:= true;
                   else
                      G1:= Group( List( gg, x -> (d0.g)*x*d0.g^-1 ) );
                   fi;
                   G0:= Intersection( G0, G1 );
                   gens:= GeneratorsOfGroup(G0);
                   if ForAll( gens, p -> ForAll( S, i -> i^p in S ) ) then
                      stab:= true;
                   fi;
                fi;
              
                if not stab then
                   H:= Stabilizer( G0, S, OnSets );
                else
                   H:= G0;
                fi;

                Append( closeds, SLAfcts.semsim(S,H,n0,rts,Q,B,ipmat));

                # now we compute the derived system of S, that is the closed
                # set consisting of all sums of elements of S

                N:= [ ];
                for k in [1..Length(S)] do
                    for l in [k+1..Length(S)] do
                        AddSet( N, Q[S[k]][S[l]] );
                    od;
                od;
                N:= Filtered( N, x -> x <> 0 );
                D:= Filtered( S, x -> not x in N );

                orbs:= Orbits( H, D ); 
                for o in orbs do
                    j:= o[1];
                    T:= ShallowCopy( S );
                    pos:= Position( S, j );
                    RemoveSet( T, j );

                    N:= SLAfcts.normaliser_ofclset( T, n0, Q );

                    vecs:= [ ];
                    d0:= Sum( prw{T} );
                    for k in N do
                        Add( vecs, SLAfcts.normalvec( R, d0+prw[k] ) );
                        if k = j then
                           v0:= vecs[Length(vecs)];
                        fi;
                    od;
                    if ForAll( vecs, x -> v0 <= x ) then

                       mat:= ipmat{T}{T};
                       for k in mat do Sort(k); od;
                       Sort(mat);

                       vals:= [ ];
                       for l in [1..Length(mat)] do
                           k:= 1; 
                           val:= []; ind:= 1; cnt:=0;
                           while k <= Length(mat) do
                               while k<=Length(mat) and mat[l][k]=Bvals[ind] do
                                   k:= k+1;
                                   cnt:= cnt+1;
                               od;
                               Add( val, cnt );
                               ind:= ind+1;
                               cnt:=0;
                           od;
                           Add( vals, val );
                       od;

                       d0:= List( vals, x -> Sum( [1..Length(x)],
                                          i -> x[i]*n0exp[Length(x)-i+1] ) );
                       nn:= Filtered( [1..2*n0], x -> ForAll(T,y->ipmat[x][y]
                           >= -1 ) );
                       nn:= SLAfcts.normalvec( R, Sum( prw{nn} ) );

                       conj:= false;
                       k:= PositionSorted( dets, d0 );

                       while k<= Length(newSS) and dets[k] = d0 do

                             if rows[k] = nn then
                               cj:= RepresentativeAction( G,newSS[k],T,OnSets );
                             else
                                cj:= fail;
                             fi;

                             if cj <> fail then
                                conj:= true; break;
                             fi;
                             k:= k+1;
                       od;

                       if not conj then
                          InsertElmList( newSS, k, T );
                          InsertElmList( dets, k, d0 );
                          InsertElmList( rows, k, nn );
                       fi;

                    fi;
                od;

            od;

            SS:= newSS;
            if Length(SS)>0 and Length(SS[1])=1 then
               for S in SS do
                   H:= Stabilizer( G, S, OnSets );
                   Append( closeds, SLAfcts.semsim(S,H,n0,rts,Q,B,ipmat));
               od;
               SS:= [ ];
            fi;
        od;

        sys:= List( closeds, x -> rts{x} );
        s:= SLAfcts.sub_systems(R);
        Pw:= PositiveRootsAsWeights(R);
        Pw:= Concatenation( Pw, -Pw );
	    for r in s.roots do
	       sim:= List( r, x -> rts[ Position( Pw, x ) ] );
	       sim:= Concatenation( sim, -sim );
	       Add( sys, SLAfcts.clos( rts, sim ) );
        od;

        return sys;

end );        


InstallMethod( IsSpecialClosedSet,
"for a closed subset of a root system", true, [ IsList ], 0,

function(c)

   return ForAll( c, x -> not -x in c );

end );


InstallMethod( DecompositionOfClosedSet,
"for a closed subset of a root system", true, [ IsList ], 0,

function(c)

   local S, N;

   S:= Filtered( c, x -> -x in c );
   N:= Filtered( c, x -> not x in S );
   return [S,N];

end );


InstallMethod( SubalgebraOfClosedSet,
"for a Lie algebra and a closed subset of its root system", true,
[ IsLieAlgebra, IsList ], 0,

function( L, c )

     local b, pr, rts, ch, rvcs, bas, r, pos;

     b:= [ ];
     pr:= PositiveRootsNF(RootSystem(L));
     rts:= Concatenation( pr, -pr );
     ch:= ChevalleyBasis(L);
     rvcs:= Concatenation( ch[1], ch[2] );
     bas:= ShallowCopy( ch[3] );
     for r in c do
         pos:= Position( rts, r );
	 if pos = fail then
	    Error( "One of the elements of <c> is not a root" );
	 fi;
	 Add( bas, rvcs[pos] );
     od;
     return Subalgebra( L, bas, "basis" );

end );
