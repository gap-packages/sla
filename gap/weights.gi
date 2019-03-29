InstallMethod( ProjectionMatrix,
"for two semisimple Lie algebras", true, [ IsLieAlgebra, IsLieAlgebra ], 0,

function( L, K )

    local H, HK, N, K0, hK, hL, b;

    H:= CartanSubalgebra(L);
    HK:= Intersection( H, K );

    N:= LieNormalizer( K, HK );
    if N <> HK then
       Error("The Cartan subalgebras do not match.");
    fi;

    if HasCartanSubalgebra(K) and CartanSubalgebra(K) <> HK then
       K0:= Subalgebra( L, BasisVectors( Basis(K) ), "basis" );
       SetCartanSubalgebra(K0,HK);
    else
       K0:= K;
    fi;

    hK:= CanonicalGenerators( RootSystem(K0) )[3];
    hL:= CanonicalGenerators( RootSystem(L) )[3];

    b:= Basis( Subspace( L, hL ), hL );
    
    return List( hK, x -> Coefficients( b, x ) );
    

end );


InstallOtherMethod( ProjectionMatrix,
"for two semisimple Lie algebras", true, [ IsLieAlgebra, IsLieAlgebra, IsList ], 0,

function( L, K, cc )

    local H, HK, N, K0, hK, hL, b;

    H:= CartanSubalgebra(L);
    HK:= Intersection( H, K );

    N:= LieNormalizer( K, HK );
    if N <> HK then
       Error("The Cartan subalgebras do not match.");
    fi;

    if not ForAll( cc, x -> x in H ) then
       Error("The toral elements do noy lie in the Cartan.");
    fi;

    if not HasCartanSubalgebra(K) then
       K0:= K;
       SetCartanSubalgebra(K0,HK);
    elif  CartanSubalgebra(K) <> HK then
       K0:= Subalgebra( L, BasisVectors( Basis(K) ), "basis" );
       SetCartanSubalgebra(K0,HK);
    else
       K0:= K;
    fi;

    hK:= Concatenation( CanonicalGenerators( RootSystem(K0) )[3], cc );
    hL:= CanonicalGenerators( RootSystem(L) )[3];

    b:= Basis( Subspace( L, hL ), hL );
    
    return List( hK, x -> Coefficients( b, x ) );
    

end );




InstallMethod( Branching,
"for two semisimple Lie algebras and a weight", true, 
[ IsLieAlgebra, IsLieAlgebra, IsList ], 0,

function( L, K, wt )


    local P, ch, R, W, w0, m0, i, o, mu, pos, S, sim, b, ord, ww, mm, mult,
          w, isg;
          

    P:= ProjectionMatrix(L,K);
    ch:= DominantCharacter( L, wt );
    R:= RootSystem(L);
    W:= WeylGroup(R);
    w0:= [ ]; m0:= [ ];
    for i in [1..Length(ch[1])] do
        o:= WeylOrbitIterator( W, ch[1][i] );
        while not IsDoneIterator(o) do
             mu:= P*NextIterator( o );
             if ForAll( mu, u -> u >= 0 ) then
                pos:= Position( w0, mu );
                if pos = fail then
                   Add( w0, mu );
                   Add( m0, ch[2][i] );
                else
                   m0[pos]:= m0[pos]+ch[2][i];
                fi;
             fi;
        od;
    od;

    S:= RootSystem(K);
    sim:= SimpleRootsAsWeights(S);
    b:= Basis( VectorSpace( Rationals, sim ), sim );
    
    ord:= function( mu, nu )

        # true if mu < nu

        local cf;

        if mu = nu then return fail; fi;
        cf:= Coefficients( b, nu-mu );
        if ForAll( cf, IsInt ) then
           if ForAll( cf, x -> x >= 0 ) then
              return true;
           elif ForAll( cf, x -> x <= 0 ) then
              return false;
           fi;
        fi;

        return fail;

    end;

    ww:=[ ]; mm:= [ ];

    while Length(w0) > 0 do

        # look for a maximum in w0...

        w:= w0[1];
        mult:= m0[1];
        for i in [1..Length(w0)] do
            isg:= ord( w, w0[i] );
            if isg <> fail and isg then
                 w:= w0[i]; mult:= m0[i];
            fi;
        od;

        Add( ww, w ); Add( mm, mult );
        ch:= DominantCharacter( K, w );
        for i in [1..Length(ch[1])] do
            pos:= Position( w0, ch[1][i] );
            m0[pos]:= m0[pos] - mult*ch[2][i];
        od;
        for i in [1..Length(w0)] do
            if m0[i] = 0 then
               Unbind( m0[i] );
               Unbind( w0[i] );
            fi;
        od;
        m0:= Filtered( m0, x -> IsBound(x) );
        w0:= Filtered( w0, x -> IsBound(x) );
    od;

    return [ww,mm];

end );


InstallOtherMethod( Branching,
"for two semisimple Lie algebras and a weight", true, 
[ IsLieAlgebra, IsLieAlgebra, IsList, IsList ], 0,

function( L, K, cc, wt )


    local P, ch, R, W, w0, m0, i, o, mu, pos, S, sim, b, ord, ww, mm, mult,
          w, isg, semsimrk;

   

    P:= ProjectionMatrix( L, K, cc );
    semsimrk:= Dimension( CartanSubalgebra(K) );

    ch:= DominantCharacter( L, wt );
    R:= RootSystem(L);
    W:= WeylGroup(R);
    w0:= [ ]; m0:= [ ];
    for i in [1..Length(ch[1])] do
        o:= WeylOrbitIterator( W, ch[1][i] );
        while not IsDoneIterator(o) do
             mu:= P*NextIterator( o );
             if ForAll( [1..semsimrk], k -> mu[k] >= 0 ) then
                pos:= Position( w0, mu );
                if pos = fail then
                   Add( w0, mu );
                   Add( m0, ch[2][i] );
                else
                   m0[pos]:= m0[pos]+ch[2][i];
                fi;
             fi;
        od;
    od;

    S:= RootSystem(K);
    sim:= SimpleRootsAsWeights(S);
    b:= Basis( VectorSpace( Rationals, sim ), sim );
    
    ord:= function( mu, nu )

        # true if mu < nu

        local cf, mu0, nu0;

        mu0:= mu{[1..semsimrk]};
        nu0:= nu{[1..semsimrk]};	
        if mu0 = nu0 then return fail; fi;
        cf:= Coefficients( b, nu0-mu0 );
        if ForAll( cf, IsInt ) then
           if ForAll( cf, x -> x >= 0 ) then
              return true;
           elif ForAll( cf, x -> x <= 0 ) then
              return false;
           fi;
        fi;

        return fail;

    end;

    ww:=[ ]; mm:= [ ];

    while Length(w0) > 0 do

        # look for a maximum in w0...

        w:= w0[1];
        mult:= m0[1];
        for i in [1..Length(w0)] do
            isg:= ord( w, w0[i] );
            if isg <> fail and isg then
                 w:= w0[i]; mult:= m0[i];
            fi;
        od;

        Add( ww, w ); Add( mm, mult );
        ch:= DominantCharacter( K, w{[1..semsimrk]} );
        for i in [1..Length(ch[1])] do
	    mu:= Concatenation( ch[1][i], w{[semsimrk+1..Length(w)]} );
            pos:= Position( w0, mu );
            m0[pos]:= m0[pos] - mult*ch[2][i];
        od;
        for i in [1..Length(w0)] do
            if m0[i] = 0 then
               Unbind( m0[i] );
               Unbind( w0[i] );
            fi;
        od;
        m0:= Filtered( m0, x -> IsBound(x) );
        w0:= Filtered( w0, x -> IsBound(x) );
    od;

    return [ww,mm];

end );




InstallMethod( DirectSumDecomposition,
"for a module over a semisimple Lie algebra", 
true, [ IsAlgebraModule ], 0,

# IN FACT: we assume that it is a left algebra module!

function( V )

   local L, R, e, sp, x, m, c, sp0, K, h, U, es;

   L:= LeftActingAlgebra( V );

   # We assume that L is reductive, and that the action is "algebraic".

   if LieDerivedSubalgebra( L ) <> L then
      K:= LieDerivedSubalgebra(L);
   else
      K:= L;
   fi; 

   R:= RootSystem(K);
   if R = fail then return fail; fi;
   e:= CanonicalGenerators( R )[1];

   sp:= V;
   for x in e do
       m:= MatrixOfAction( Basis(V), x );
       m:= TransposedMatDestructive(m);
       c:= NullspaceMat(m);
       sp0:= Subspace( V, List( c, u -> u*Basis(V) ), "basis" );
       sp:= Intersection( sp, sp0 );
   od;

   # in sp find a basis of weight vectors
   h:= CanonicalGenerators( R )[3];
   sp:= [ sp ];
   for x in h do
       sp0:= [ ];
       for U in sp do
           m:= List( Basis(U), a -> Coefficients( Basis(U), x^a ) );
           es:= Eigenspaces(LeftActingDomain(L),m);
           Append( sp0, List( es, M -> Subspace( V, List( Basis(M), v ->
                                          v*Basis(U) ) ) ) );
       od;
       sp:= sp0;
   od;

   sp0:= [ ];
   for U in sp do
       Append( sp0, List( Basis(U), u -> SubAlgebraModule( V, [u] ) ) );
   od;
   return sp0;
    

end );



InstallMethod( CharacteristicsOfStrata,
"for a semisimple Lie algebra and a highest weight", 
true, [ IsLieAlgebra, IsList ], 0,

function( L, hw ) # L: semisimple Lie algebra, hw: highest weight

    local ch, W, wts, w, o, hh, KM, hwts, perms, rk, i, R, B, rho, exprs, 
          p, a, sa, mults, H, BH, ip, posR, csa, inconvexhull, hdimstrata,
          weylorbs, j, A, sim, id;

# first we have three functions...

weylorbs:= function( W, wts, A )

     # wts is a set of weights, in usual notation, permuted 
     # by the Weyl group, we find subsets of length up to the rank
     # containing reps of each orbit of the Weyl group, but 
     # probably rather redundant.

     local sets, zeros, rk, s1, z1, i, j, k, s, z, s0, z0, inds, len, cont, 
           r, l, OO, dt, dets, mat, rows, row, cols, col;

     sets:= [ ];
     zeros:= [ ];
     rk:= Length( wts[1] );

     s1:= [ ];
     z1:= [ ];
     for i in [1..Length(wts)] do
         if ForAll( wts[i], m -> m >= 0 ) then 
            Add( s1, [i] ); 
            Add( z1, Filtered( [1..rk], m -> wts[i][m] = 0 ) );
         fi;
     od;
     Add( sets, s1 );
     Add( zeros, z1 );

     for len in [2..rk] do
         s1:= [ ]; z1:= [ ]; dets:= [ ]; rows:= [ ]; #cols:= [ ];
         for i in [1..Length(sets[len-1])] do
             s:= sets[len-1][i];
             z:= zeros[len-1][i];
             for j in [1..Length(wts)] do
                 if not j in s then
                    if ForAll( z, m -> wts[j][m] >= 0 ) then
                       s0:= ShallowCopy(s); Add( s0, j );
                       z0:= [ ];
                       for k in [1..rk] do
                           if k in z and wts[j][k]=0 then
                              Add( z0, k );
                           fi;
                       od;
                       cont:= false;
                       mat:= List( [1..Length(s0)], s -> [ ] );
                       for k in [1..Length(s0)] do
                           for l in [k..Length(s0)] do
                               mat[k][l]:= wts[s0[k]]*A*wts[s0[l]];
                               mat[l][k]:= mat[k][l];
                           od;
                       od;
                       dt:= Permanent(mat);
                       row:= List( mat, Sum );
                       Sort( row );

                       #col:= List( TransposedMat(mat), Sum );
                       #Sort(col);
                       for l in [1..Length(s1)] do
                           if dt = dets[l] and row = rows[l] #and col = cols[l]
                                                             then
                              r:= RepresentativeAction( W, s0, s1[l], OnSets );
                              if r <> fail then
                                 cont:= true;
                                 break;
                              fi;
                           fi;
                       od;

                       if not cont then
                          Add( s1, s0 ); Add( z1, z0 ); 
                          Add( dets, dt ); Add( rows, row ); #Add( cols, col );
                       fi;
                    fi;
                 fi; 
             od;
         od;
         Add( sets, s1 ); Add( zeros, z1 );
     od; 
     
     return sets;        

end;


inconvexhull:= function( B, S0, p0, dist, ip ) 
                                            # S set of vecs in R^m (rat coords),
                                            # p a point in R^m, is p\in S?
                                            # dist: distance fct

    local m, i, one, eps, dists, pos, v, pp, k, j, u, t, S, p;

    S:= List( S0, x -> Coefficients( B, x ) );
    p:= Coefficients( B, p0 );
    one:= 1.000000000000000000000;
    S:= List( S, u -> u*one );
    p:= p*one;

    eps:= one*1/10; # small eps, but not very small, the algorithm for 
                    # the strata is rather sensitive to the choice of eps,
                    # smaller eps, longer runtime...

    dists:= List( S, s -> dist(s,p) );
    pos:= Position( dists, Minimum( dists ) );
    v:= S[pos];
    pp:= S[pos];

    while true do
       if dist(p,pp) < eps*dist(p,v) then
          return [ pp, true ];
       else
          k:= 0;
          for j in [1..Length(S)] do
              if dist(pp,S[j]) >= dist(p,S[j]) then
                 k:= j; break;
              fi;
          od;
          if k > 0 then
             v:= S[k];
          else
             return [ pp, false ];
          fi;
       fi;

       u:= pp-v;
       t:= -ip(u,p-pp)/ip(u,u);
       pp:= pp+t*(-u);

    od;
end;

hdimstrata:= function( R, H, BH, ip, rk, posR, csa, KM, h_wts, mults, wts, W, exps, A, bool )

    # R: the root system of the big Lie alg
    # H: Cartan subalgebra of the "big" Lie alg
    # BH: basis of H, wrt Chevalley basis vecs
    # ip: inner product function on H (fct of two arguments)
    # rk: rank of the input Lie algebra (in general a reductive subalgebra)
    # posR: pos roots of input Lie alg, as weights,
    # csa : basis of the Cartan of the input Lie alg
    # h_wts: List of wts of the rep, as elts in the CSA,
    # mults: their multiplicities
    # wts: the weights in usual form
    # W : list of perms on [1..Length(wts)], giving the action on the
    # Weyl group
    # exps: reduces expressions of the reflections corr to the rts in posR
    # bool: a boolean, if true then we do not consider only the stata of 
    #       highest dim.

    local dist, out, i, G, k, XX, OO, orbs, st, hst, diffs, V, j, hset, h,
          mat, sol, bas, B, dims, dim, cfs, p, inds, pR, wt0, ex0,
          h0, cs, hw0, mu0, perms, res, hs, dist0, w, ip0, bcsa, BC, bigger,
          sums, delt, xx, yy, hh, conjdomh, Onew, d, r, u, v, rep, len, N, 
          totlen, dets, dt, orbs0, q;

    dist:= function(u,v) return ip(u-v,u-v); end;

    dist0:= function(u,v) return (u-v)*KM*(u-v); end;
    ip0:= function(u,v) return u*KM*v; end;

    # detect the trivial rep, ie all weights are 0
    w:= List( h_wts, v -> List( csa, u -> ip(u,v) ) );
    if ForAll( w, IsZero ) then
       # no nilpotent elements
       return [ [], [] ];
    fi;       

    if Length(posR)=0 then  #torus
       out:= [ [], [] ];
       for i in [1..Length(h_wts)] do
           w:= List( csa, u -> ip(u,h_wts[i]) ); # so the weight corr.
           if not IsZero(w) then
              Add( out[1], h_wts[i] );
              Add( out[2], mults[i] );
           fi;
       od;
       return out;  
    fi;

    # compute simple roots, Weyl group etc.
    # to later erase W-conjugate h-s...

    sums:= [ ];
    for i in [1..Length(posR)] do
        for j in [i+1..Length(posR)] do
            Add( sums, posR[i]+posR[j] );
        od;
    od;
    delt:= Filtered( posR, x -> not x in sums );

    inds:= List( delt, x -> Position( PositiveRootsAsWeights(R), x ) );
    xx:= PositiveRootVectors(R){inds};
    yy:= NegativeRootVectors(R){inds};
    hh:= List( [1..Length(inds)], i -> xx[i]*yy[i] );

    conjdomh:= function( h )
           # the conjugate dominant elt in H to h.

       local h0, a, c, pos;
  
       h0:= h;
       while true do 
          c:= Coefficients( BH, h0 );
          a:= List( delt, u -> u*c );
          pos:= PositionProperty( a, x -> x<0 );
          if pos = fail then
             return h0;
          else
             h0:= h0-a[pos]*hh[pos];
          fi;
       od;

    end;        


       G:= Group(W);
       hs:= [ ];

       if bool then orbs0:= weylorbs( G, wts, A ); fi; 

       for k in [1..rk] do
           if bool then
              OO:= orbs0[k];
           else 
              N:= NrCombinations( [1..Length(h_wts)], k );

              if N <= 500000 then # some bound for memory reasons...
                 XX:= Combinations( [1..Length(h_wts)], k );
                 OO:= OrbitsDomain( G, XX, OnSets );
                 OO:= List( OO, u -> u[1] );

              else
                 Onew:= [ ];
                 totlen:= 0;
                 dets:= [ ];
                 for u in OO do
                     d:= u[Length(u)];
                     v:= ShallowCopy(u);
                     len:= Length(v)+1;
                     for i in [d+1..Length(h_wts)] do
                 
                         v[len]:= i;
                         dt:= Permanent( List( v, i -> List( v,
                                 j -> ip( h_wts[i], h_wts[j] ) ) ) );

                         rep:= false;
                         for j in [1..Length(Onew)] do
                             if dets[j] = dt then 
                                r:= RepresentativeAction( G, v, Onew[j], OnSets ); 
                                if r <> fail then
                                   rep:= true;
                                   break;
                                fi;
                             fi;
                         od;
                         if not rep then 
                            Add( Onew, ShallowCopy(v) );
                            Add( dets, dt );
                            totlen:= totlen + OrbitLength(G,v,OnSets);
                         fi;
                         if totlen=N then break; fi;
                     od;
                 od;
                 OO:= Onew;

              fi;
           fi;

           orbs:= Filtered( OO, v -> not 0*h_wts[1] in
                       h_wts{v} );
           for st in orbs do
               # find the affine space generated by st...

               hst:= h_wts{st};
               diffs:= [ ];
               for i in [1..Length(hst)] do
                   for j in [i+1..Length(hst)] do
                       Add( diffs, hst[j]-hst[i] );
                   od;
               od;
               V:= Subspace( H, diffs );
               
               # so the affine space is A=hst[1]+V...
               # see if there are more elms in this space

               hset:= ShallowCopy( hst );
               #bigger:= false;
               for h in h_wts do
                   if h-hst[1] in V and not h in hset then
                      Add( hset, h );
                      #bigger:= true;
                   fi;
               od;

               #if not bigger or k=rk then

                 # find point closest to 0 on A:
                 if Length(st)>1 then
                    mat:= List( [1..Dimension(H)], i -> 
                            List( [1..Dimension(V)], j -> 
                                     ip( Basis(H)[i], Basis(V)[j] ) ) );
                    sol:= List( NullspaceMat( mat ), u -> u*Basis(H) );

                   # so this is a basis of the space orthogonal to V...
                   # so sol and V span the whole space, therefore, finding the
                 # intersection point amounts to expressing hst[1] on this basis

                    bas:= -ShallowCopy( Basis(V) );
                    Append( bas, sol );
                    B:= Basis( H, bas );
                    cfs:= Coefficients( B, hst[1] );
                    h0:= hst[1]+cfs{[1..Dimension(V)]}*Basis(V);
                 else
                    h0:= h_wts[ st[1] ];
                 fi;

                 # see whether it is contained
                 # in the convex hull of hst.
                 
                 if not IsZero(h0) then
                    if Length(hst)=1 or 
                           inconvexhull( BH, hst, h0, dist0, ip0 )[2] then
                       h0:= (2/ip(h0,h0))*h0;
                       h0:= conjdomh(h0);
                       if not h0 in hs then
                          Add( hs, h0 );
                       fi; 
                    fi;
                 #fi;
              fi;
           od; 
       od;            

       # now for each elt of hs we compute the dimension of the corr stratum
       # (in case it is a characteristic).
     
       dims:= [ ];
       for h0 in hs do
          dim:= 2*Length(posR)+Length(csa);
          for i in [1..Length(h_wts)] do
              if ip(h0,h_wts[i]) >= 2 then dim:= dim+mults[i]; fi;
          od;
          cfs:= Coefficients( BH, h0 );
          for p in posR do
              if cfs*p <> 0 then # so either the pos or the neg root contrbs
                 dim:= dim-1;
              else
                 # now both the pos and the neg root contribs
                 dim:= dim-2;
              fi;
          od;
          dim:= dim-Length(csa);
          Add( dims, dim );
       od;    

       if not bool then
          dim:= 0; # compute maximum dim, less than total dim of V...
          for i in [1..Length(dims)] do
              if dims[i] > dim and dims[i] <= Sum( mults ) then
                 dim:= dims[i];
              fi;
          od;             
          inds:= Filtered( [1..Length(hs)], i -> dims[i] = dim );
          hs:= hs{inds};      
       else
          dim:= Sum( mults );
          inds:= Filtered( [1..Length(hs)], i -> dims[i] <= dim );
          hs:= hs{inds}; 
       fi;

       # now for each elt of hs, do a recursive call...

       out:= [ [], [] ]; # first the chars, then the dims of the corr stratum.

       for k in [1..Length(hs)] do

           h0:= hs[k];
           # have to compute tilde z(h)...
           # first its posR...

           pR:= [ ];
           ex0:= [ ];
           wt0:= [ ];
           cfs:= Coefficients( BH, h0 );
           for i in [1..Length(posR)] do
               if cfs*posR[i] = 0 then
                  Add( pR, posR[i] );
                  Add( ex0, exps[i] );
               fi;
           od;

           
           # next the csa:
           mat:= List( csa, h1 -> [ip(h1,h0)] );
           cs:= List( NullspaceMat(mat), u -> u*csa );

           bcsa:= ShallowCopy(cs); Add( bcsa, h0 );
           BC:= Basis( Subspace(H,bcsa), bcsa );
           # now the h_wts of V_2(h0):
           # those are the elts h of h_wts such that ip(h0,h)=2...
           hw0:= [ ];
           mu0:= [ ];
           for i in [1..Length(h_wts)] do
               if ip(h0,h_wts[i]) = 2 then
                  # project h_wts[i] on cs:
                  if Length(cs) > 0 then
                     cfs:= Coefficients( BC, h_wts[i] );
                     Add( hw0, cfs{[1..Length(cs)]}*cs );
                  else
                     Add( hw0, Zero(H) );
                  fi;
                  Add( mu0, mults[i] );
                  Add( wt0, wts[i] );
               fi;
           od;

           # and finally the Weyl group: 
           perms:= [ ];
           for i in [1..Length(pR)] do
               Add( perms, PermList( 
                 List( wt0, w -> Position( wt0, 
                               ApplyWeylElement(WeylGroup(R),w,ex0[i]) ))));
           od;
           res:= hdimstrata( R, H, BH, ip, rk-1, pR, cs, KM, hw0, mu0, wt0, 
                             perms, ex0, A, false );

           # is there a stratum in the recursive output of dimension equal
           # to the dimension of V_2(h)? If yes, then h is not a char.

           if not Sum( mu0 ) in res[2] then
              # so h0 is a char
              if bool then
                 Add( out[1], h0 ); Add( out[2], dims[k] ); 
              else
                 Add( out[1], h0 ); Add( out[2], dim );
              fi;
           fi;

       od;
       return out;

end;

   # Now we start with the main function.

    # first we compute the character of the module,
    # then map the weights to the CSA, where we use the Killing form.

    R:= RootSystem(L);
    ch:= DominantCharacter( L, hw );
    W:= WeylGroup( R );
    wts:= [ ];
    mults:= [ ];
    for w in [1..Length(ch[1])] do
        o:= WeylOrbitIterator( W, ch[1][w] );
        while not IsDoneIterator( o ) do 
            Add( wts, NextIterator(o) ); 
            Add( mults, ch[2][w] );
        od;
    od;

    hh:= ChevalleyBasis(L)[3];
    rk:= Length(hh);
    KM:= List( hh, h1 -> List( hh, h2-> TraceMat( AdjointMatrix(Basis(L),h1)*
           AdjointMatrix(Basis(L),h2) ) ) );

    hwts:= [ ];
    for w in wts do
        Add( hwts, SolutionMat( KM, w )*hh );
    od;

    # next we get permutations generating the permutation action of W on the
    # weights:

    perms:= [ ];
    for i in [1..rk] do
        Add( perms, PermList( 
              List( wts, w -> Position( wts, ApplyWeylElement(W,w,[i]) ))));
    od;

    # find reduced expressions for the reflections corr the pos rts:
    B:= BilinearFormMatNF(R);
    rho:= List( [1..rk], i -> 1);
    exprs:= [ ];
    for i in [1..Length(PositiveRoots(R))] do
        p:= PositiveRootsNF(R)[i];
        a:= Sum( [1..rk], j -> p[j]*B[j][j] );
        sa:= rho -a/(p*B*p)*PositiveRootsAsWeights(R)[i];
        w:= ConjugateDominantWeightWithWord( W, sa );
        Add( exprs, w[2] );
    od;

    H:= CartanSubalgebra(L);
    BH:= Basis(H, hh );

    ip:= function(h1,h2) return Coefficients(BH,h1)*KM*Coefficients(BH,h2);
         end;
    posR:= PositiveRootsAsWeights(R);
    csa:= ShallowCopy( hh );

    sim:= SimpleRootsAsWeights( R );
    sim:= Basis( VectorSpace( Rationals, sim ), sim );
    id:= IdentityMat(rk);
    A:= List( [1..rk], i -> [ ] );
    for i in [1..rk] do
        for j in [i..rk] do
            A[i][j]:= Coefficients(sim,id[i])*B*Coefficients(sim,id[j]);
            A[j][i]:= A[i][j];
        od;

    od;
    
    return  hdimstrata( R, H, BH, ip, rk, posR, csa, KM, hwts, mults, 
                 wts, perms, exprs, A, true );

end );



