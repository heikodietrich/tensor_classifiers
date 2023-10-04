LoadPackage("singular");
LoadPackage("SLA");
LoadPackage("corelg");
GBASIS:= SINGULARGBASIS;
LoadPackage("float");
SetFloats(MPFR);


######################################################################################################
######################################################################### methods from module.g
DeclareProperty( "IsIrreducibleHWModule", IsAlgebraModule );

DeclareAttribute( "HighestWeight", IsAlgebraModule );

DeclareAttribute( "HighestWeightVector", IsAlgebraModule );

DeclareOperation( "IsomorphismOfIrreducibleHWModules", [ IsAlgebraModule,
     IsAlgebraModule ] );


InstallMethod( HighestWeightVector,
     "for an irreducible highest weight module",
     true, [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection ], 0,
    function( V )

    local L, K, R, e, m, c, sp;

    if HasBasis(V) and IsWeightRepElement( Basis(V)[1]![1] ) then
       return Basis(V)[1];
    fi;

    L:= LeftActingAlgebra( V );

    #We assume that L is reductive, and that the action is "algebraic".

    if LieDerivedSubalgebra( L ) <> L then
       K:= LieDerivedSubalgebra(L);
    else
       K:= L;
    fi; 

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
true, [ IsAlgebraModule ], 0,

# IN FACT: we assume that it is a left algebra module!

function( V )

   local L, R, e, sp, x, m, c, sp0, K, h, U, es, u, M, b, hw;

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
           es:= Eigenspaces(LeftActingDomain(L),m);
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

    # we assume that highest weight and hw vector are known...

    local   L,  R,  hw,  cg,  paths,  strings,  p,  p1, word, k, b,
            st,  i,  j,  a,  y,  v,  bas, s1, i1, n1,  w,  sim, pos, posR, yy, 
            weylwordNF, e, sp, x, m, c, sp0, h, H, t0, s0;

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
   bas:= [ HighestWeightVector(V) ];

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

  return bas;
end;



InstallMethod( Basis,
    "for an irreducible highest weight module",
    true, [ IsFreeLeftModule and IsLeftAlgebraModuleElementCollection and
    IsIrreducibleHWModule], 0,
    function( V )

    local   vecs;

    vecs:= SLAfcts.canbasofhwrep( V );
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

    b1:= SLAfcts.canbasofhwrep( V1 );
    b2:= SLAfcts.canbasofhwrep( V2 );
    return LeftModuleHomomorphismByImages( V1, V2, b1, b2 );
    

end );


DecomposeNaturalRepresentation:= function( L )

        local r, M, d;

        # here L is a semisimple matrix Lie algebra, we decompose
        # the natural module.

        r:= AlgebraHomomorphismByImagesNC( L, L, Basis(L), Basis(L) );
        M:= LeftModuleByHomomorphismToMatAlg( L, r );
        d:= DirectSumDecomposition( M );
        return List( d, U -> [ HighestWeight(U), Dimension(U) ] );
end;

DecomposeNaturalRepresentation_mn:= function( L, m, n )

        local r, M, M1, M2, d1, d2;

        # here L is a semisimple matrix Lie algebra, we decompose
        # the natural module.

        r:= AlgebraHomomorphismByImagesNC( L, L, Basis(L), Basis(L) );
        M:= LeftModuleByHomomorphismToMatAlg( L, r );
        M1:= SubAlgebraModule( M, Basis(M){[1..m]}, "basis" );
        M2:= SubAlgebraModule( M, Basis(M){[m+1..m+n]}, "basis" );
        d1:= DirectSumDecomposition( M1 );
        d2:= DirectSumDecomposition( M2 );
        return [ List( d1, U -> [ HighestWeight(U), Dimension(U) ] ),
                 List( d2, U -> [ HighestWeight(U), Dimension(U) ] ) ];
end;



######################################################################################################
######################################################################################################

mySignature := function(l)
local ch,r;

   ch := CharacteristicPolynomial(l);
   ch := CoefficientsOfUnivariatePolynomial(ch);
   r  := RootsFloat(ch*1.0);
   return [Size(Filtered(r,x-> x>0*1.0)),Size(Filtered(r,x->x<0*1.0))];
end;

        
######################################################################################################
## 
## this is a list containing 30 records (corresponding to the 30 complex orbits);
## each of these 30 records has an entry reps for the real orbits according to
## Tablel 1 in our paper.
##
#######################################################################################################

ORBITS := 
[ rec( dim := 5, nr := 1, reps := [ "+(++--)" ], size := 1 ), 
  rec( dim := 6, nr := 2, reps := [ "+(++--)+(----)", 
                                    "+(++--)-(----)" ], size := 2 ), 
  rec( dim := 6, nr := 3, reps := [ "+(++--)+(+--+)", 
                                    "+(++--)-(+--+)" ], size := 2 ), 
  rec( dim := 6, nr := 4, reps := [ "+(++--)+(+-+-)", 
                                    "+(++--)-(+-+-)" ], size := 2 ), 
  rec( dim := 6, nr := 5, reps := [ "+(++-+)+(-+--)", 
                                    "+(++-+)-(-+--)" ], size := 2 ), 
  rec( dim := 6, nr := 6, reps := [ "+(+++-)+(-+--)", 
                                    "+(+++-)-(-+--)" ], size := 2 ), 
  rec( dim := 6, nr := 7, reps := [ "+(+++-)+(++-+)", 
                                    "+(+++-)-(++-+)" ], size := 2 ), 
  rec( dim := 8, nr := 8, 
      reps := [ "+(++-+)+(-+--)+(+---)", 
                "+(++-+)+(-+--)-(+---)", 
                "+(++-+)-(-+--)+(+---)", 
                "+(++-+)-(-+--)-(+---)" ], size := 4 ), 
  rec( dim := 8, nr := 9, 
      reps := [ "+(+++-)+(-+--)+(+---)", 
                "+(+++-)+(-+--)-(+---)", 
                "+(+++-)-(-+--)+(+---)", 
                "+(+++-)-(-+--)-(+---)" ], size := 4 ), 
  rec( dim := 8, nr := 10, 
      reps := [ "+(+++-)+(++-+)+(+---)", 
                "+(+++-)+(++-+)-(+---)", 
                "+(+++-)-(++-+)+(+---)", 
                "+(+++-)-(++-+)-(+---)" ], size := 4 ), 
  rec( dim := 8, nr := 11, 
      reps := [ "+(+++-)+(++-+)+(-+--)", 
                "+(+++-)+(++-+)-(-+--)", 
                "+(+++-)-(++-+)+(-+--)", 
                "+(+++-)-(++-+)-(-+--)" ], size := 4 ), 
  rec( dim := 9, nr := 12, 
      reps := [ "+(-+-+)+(++--)+(+--+)+(----)", 
                "+(-+-+)+(++--)+(+--+)-(----)", 
                "+(-+-+)+(++--)-(+--+)+(----)", 
                "+(-+-+)-(++--)+(+--+)+(----)", 
                "-(-+-+)+(++--)+(+--+)+(----)" ], size := 5 ), 
  rec( dim := 9, nr := 13, 
      reps := [ "+(-++-)+(++--)+(+-+-)+(----)", 
                "+(-++-)+(++--)+(+-+-)-(----)", 
                "+(-++-)+(++--)-(+-+-)+(----)", 
                "+(-++-)-(++--)+(+-+-)+(----)", 
                "-(-++-)+(++--)+(+-+-)+(----)" ], size := 5 ), 
  rec( dim := 9, nr := 14, 
      reps := [ "+(++++)+(++--)+(+--+)+(+-+-)", 
                "+(++++)+(++--)+(+--+)-(+-+-)", 
                "+(++++)+(++--)-(+--+)+(+-+-)", 
                "+(++++)-(++--)+(+--+)+(+-+-)", 
                "-(++++)+(++--)+(+--+)+(+-+-)" ], size := 5 ), 
  rec( dim := 9, nr := 15, 
      reps := [ "+(-+++)+(+++-)+(++-+)+(-+--)", 
                "+(-+++)+(+++-)+(++-+)-(-+--)", 
                "+(-+++)+(+++-)-(++-+)+(-+--)", 
                "+(-+++)-(+++-)+(++-+)+(-+--)", 
                "-(-+++)+(+++-)+(++-+)+(-+--)" ], size := 5 ), 
  rec( dim := 9, nr := 16, 
      reps := [ "+(+++-)+(++-+)+(-+--)+(+---)", 
                "+(+++-)+(++-+)+(-+--)-(+---)", 
                "+(+++-)+(++-+)-(-+--)+(+---)", 
                "+(+++-)+(++-+)-(-+--)-(+---)", 
                "+(+++-)-(++-+)+(-+--)+(+---)", 
                "+(+++-)-(++-+)+(-+--)-(+---)", 
                "+(+++-)-(++-+)-(-+--)+(+---)", 
                "+(+++-)-(++-+)-(-+--)-(+---)" ], size := 8 ), 
  rec( dim := 10, nr := 17, 
      reps := [ "+(+++-)+(++-+)+(----)", 
                "+(+++-)+(++-+)-(----)", 
                "+(+++-)-(++-+)+(----)", 
                "+(+++-)-(++-+)-(----)" ], size := 4 ), 
  rec( dim := 10, nr := 18, 
      reps := [ "+(+++-)+(-+--)+(+--+)", 
                "+(+++-)+(-+--)-(+--+)", 
                "+(+++-)-(-+--)+(+--+)", 
                "+(+++-)-(-+--)-(+--+)" ], size := 4 ), 
  rec( dim := 10, nr := 19, 
      reps := [ "+(++-+)+(-+--)+(+-+-)", 
                "+(++-+)+(-+--)-(+-+-)", 
                "+(++-+)-(-+--)+(+-+-)", 
                "+(++-+)-(-+--)-(+-+-)" ], size := 4 ), 
  rec( dim := 10, nr := 20, 
      reps := [ "+(-+-+)+(+++-)+(+---)", 
                "+(-+-+)+(+++-)-(+---)", 
                "+(-+-+)-(+++-)+(+---)", 
                "+(-+-+)-(+++-)-(+---)" ], size := 4 ), 
  rec( dim := 10, nr := 21, 
      reps := [ "+(-++-)+(++-+)+(+---)", 
                "+(-++-)+(++-+)-(+---)", 
                "+(-++-)-(++-+)+(+---)", 
                "+(-++-)-(++-+)-(+---)" ], size := 4 ), 
  rec( dim := 10, nr := 22, 
      reps := [ "+(++++)+(-+--)+(+---)", 
                "+(++++)+(-+--)-(+---)", 
                "+(++++)-(-+--)+(+---)", 
                "+(++++)-(-+--)-(+---)" ], size := 4 ), 
  rec( dim := 11, nr := 23, 
      reps := [ "+(+++-)+(-+--)+(----)+(+--+)", 
                "+(+++-)+(-+--)+(----)-(+--+)", 
                "+(+++-)+(-+--)-(----)+(+--+)", 
                "+(+++-)+(-+--)-(----)-(+--+)", 
                "+(+++-)-(-+--)+(----)+(+--+)", 
                "+(+++-)-(-+--)+(----)-(+--+)", 
                "+(+++-)-(-+--)-(----)+(+--+)", 
                "+(+++-)-(-+--)-(----)-(+--+)" ], size := 8 ), 
  rec( dim := 11, nr := 24, 
      reps := [ "+(-++-)+(++-+)+(+---)+(----)", "+(-++-)+(++-+)+(+---)-(----)", 
                "+(-++-)+(++-+)-(+---)+(----)", "+(-++-)+(++-+)-(+---)-(----)", 
                "+(-++-)-(++-+)+(+---)+(----)", "+(-++-)-(++-+)+(+---)-(----)", 
                "+(-++-)-(++-+)-(+---)+(----)", "+(-++-)-(++-+)-(+---)-(----)" ], size := 8 ), 
  rec( dim := 11, nr := 25, 
      reps := [ "+(++++)+(-+--)+(+---)+(+--+)", "+(++++)+(-+--)+(+---)-(+--+)", 
                "+(++++)+(-+--)-(+---)+(+--+)", "+(++++)+(-+--)-(+---)-(+--+)", 
                "+(++++)-(-+--)+(+---)+(+--+)", "+(++++)-(-+--)+(+---)-(+--+)", 
                "+(++++)-(-+--)-(+---)+(+--+)", "+(++++)-(-+--)-(+---)-(+--+)" ], size := 8 ), 
  rec( dim := 11, nr := 26, 
      reps := [ "+(++++)+(-+--)+(+---)+(+-+-)", "+(++++)+(-+--)+(+---)-(+-+-)", 
                "+(++++)+(-+--)-(+---)+(+-+-)", "+(++++)+(-+--)-(+---)-(+-+-)", 
                "+(++++)-(-+--)+(+---)+(+-+-)", "+(++++)-(-+--)+(+---)-(+-+-)", 
                "+(++++)-(-+--)-(+---)+(+-+-)", "+(++++)-(-+--)-(+---)-(+-+-)" ], size := 8 ), 
  rec( dim := 12, nr := 27, 
      reps := [ "+(-+-+)+(+++-)+(----)+(+--+)", "+(-+-+)+(+++-)+(----)-(+--+)", 
                "+(-+-+)+(+++-)-(----)+(+--+)", "+(-+-+)+(+++-)-(----)-(+--+)", 
                "+(-+-+)-(+++-)+(----)+(+--+)", "+(-+-+)-(+++-)+(----)-(+--+)", 
                "+(-+-+)-(+++-)-(----)+(+--+)", "+(-+-+)-(+++-)-(----)-(+--+)" ], size := 8 ), 
  rec( dim := 12, nr := 28, 
      reps := [ "+(-++-)+(++-+)+(----)+(+-+-)", "+(-++-)+(++-+)+(----)-(+-+-)", 
                "+(-++-)+(++-+)-(----)+(+-+-)", "+(-++-)+(++-+)-(----)-(+-+-)", 
                "+(-++-)-(++-+)+(----)+(+-+-)", "+(-++-)-(++-+)+(----)-(+-+-)", 
                "+(-++-)-(++-+)-(----)+(+-+-)", "+(-++-)-(++-+)-(----)-(+-+-)" ], size := 8 ), 
  rec( dim := 12, nr := 29, 
      reps := [ "+(++++)+(-+--)+(+--+)+(+-+-)", "+(++++)+(-+--)+(+--+)-(+-+-)", 
                "+(++++)+(-+--)-(+--+)+(+-+-)", "+(++++)+(-+--)-(+--+)-(+-+-)", 
                "+(++++)-(-+--)+(+--+)+(+-+-)", "+(++++)-(-+--)+(+--+)-(+-+-)", 
                "+(++++)-(-+--)-(+--+)+(+-+-)", "+(++++)-(-+--)-(+--+)-(+-+-)" ], size := 8 ), 
  rec( dim := 12, nr := 30, 
      reps := [ "+(++++)+(-++-)+(-+-+)+(+---)", "+(++++)+(-++-)+(-+-+)-(+---)", 
                "+(++++)+(-++-)-(-+-+)+(+---)", "+(++++)+(-++-)-(-+-+)-(+---)", 
                "+(++++)-(-++-)+(-+-+)+(+---)", "+(++++)-(-++-)+(-+-+)-(+---)", 
                "+(++++)-(-++-)-(-+-+)+(+---)", "+(++++)-(-++-)-(-+-+)-(+---)" ], size := 8 ) ];



   BASIS := [ ## here we have 1="-"="[0,1]" and 0="+"="[1,0]"
   [1,1,1,1], #1
   [0,1,1,1], #2
   [1,0,1,1], #3
   [1,1,0,1], #4
   [1,1,1,0], #5
   [0,0,1,1], #6
   [0,1,0,1], #7
   [0,1,1,0], #8
   [1,0,0,1], #9
   [1,0,1,0], #10
   [1,1,0,0], #11
   [0,0,0,1], #12
   [0,0,1,0], #13
   [0,1,0,0], #14
   [1,0,0,0], #15
   [0,0,0,0] ]; #16

  BASISPM := [
   "(----)", #1
   "(+---)", #2
   "(-+--)", #3
   "(--+-)", #4
   "(---+)", #5
   "(++--)", #6
   "(+-+-)", #7
   "(+--+)", #8
   "(-++-)", #9
   "(-+-+)", #10
   "(--++)", #11
   "(+++-)", #12
   "(++-+)", #13
   "(+-++)", #14
   "(-+++)", #15
   "(++++)" ]; #16



  P:= PolynomialRing( Rationals, 
       ["a11","a12","a21","a22","b11","b12","b21","b22",
        "c11","c12","c21","c22","d11","d12","d21","d22","u","v"] );

   id:= IndeterminatesOfPolynomialRing( P );
   a11:= id[1]; a12:= id[2]; a21:= id[3]; a22:= id[4];
   a:= [[a11,a12],[a21,a22]];
   b11:= id[5]; b12:= id[6]; b21:= id[7]; b22:= id[8];
   b:= [[b11,b12],[b21,b22]];
   c11:= id[9]; c12:= id[10]; c21:= id[11]; c22:= id[12];
   c:= [[c11,c12],[c21,c22]];
   d11:= id[13]; d12:= id[14]; d21:= id[15]; d22:= id[16];
   d:= [[d11,d12],[d21,d22]];
   u := id[17]; v:=id[18];


   ## MAT is the action matrix, act on row vectors wrt BASIS
   MAT := [];
   for i in [1..16] do
      row := [];
      v  := List(BASIS[i], j-> j+1); #pick this row of corresponding matrix
      for j1 in [1,2] do for j2 in [1,2] do for j3 in [1,2] do for j4 in [1,2] do
          pos := Position(BASIS,[j1-1,j2-1,j3-1,j4-1]);
          row[pos] := a[v[1]][j1]*b[v[2]][j2]*c[v[3]][j3]*d[v[4]][j4]; 
      od; od; od; od;
      MAT[i] := row;
   od;



######################################################################################
##
##
## lots of global variables defined: K, L, W, T, V0, M
##
######################################################################################

K:= SimpleLieAlgebra("A",1,Rationals);
L:= DirectSumOfAlgebras([K,K,K,K]);
W:= Rationals^2;
T:= TensorProduct( [W,W,W,W] );

##
## how x in L acts on v in T
##
LactOnT:= function( x, v ) # x in L, v in T
local mat, cx, xx, res, ev, i, j, k, u, u0, w, cf;

   ##get matrix wrt to standard SL2 basis
     mat:= z->[[z[3],z[1]],[z[2],-z[3]]];
    
     cx:= x![1];
     xx:= [ cx{[1,2,3]}, cx{[4,5,6]}, cx{[7,8,9]}, cx{[10,11,12]} ];
     xx:= List( xx, mat );

     res:= Zero(T);
     ev:= v![1];
     for k in [1,3..Length(ev)-1] do
        u:= ev[k];
        for i in [1..Length(u)] do
           w:= xx[i]*u[i];
           for j in [1,2] do
              u0:= ShallowCopy(u);
              if j=1 then u0[i]:= [1,0]; else u0[i]:= [0,1]; fi;
              cf:= ev[k+1]*w[j];
              if not IsZero(cf) then
                 res:= res + ObjByExtRep( ElementsFamily(FamilyObj(T)), [ u0, cf ] );
              fi;
           od;
        od;
     od;
     return res;
end;        

M := LeftAlgebraModule( L, LactOnT, T );  ##original module
V0:= HighestWeightModule( L, [1,1,1,1] ); ##natural 2-dim rep of SL2; hw [i] yields dim (i+1) module




##################################################
# two hw modules with same hwt
# v and w are hw vecs; produce isom
#
isomhwmodules:= function( V, v, W, w, hwt ) 
local weylwordNF, L, R, cg, paths, strings, p, p1, st, word, j, k, y,
        bas1, bas2, i, s1, i1, n1, pos, u, BV, BW;

   weylwordNF:= function( R, path )     
   local   w,  rho,  wt;     
     # the WeylWord in lex shortest form...
       w:= WeylWord( path );
       rho:= List( [1..Length( CartanMatrix(R))], x -> 1 );
       wt:= ApplyWeylElement( WeylGroup(R), rho, w );
       return ConjugateDominantWeightWithWord( WeylGroup(R), wt )[2];
   end;

   L:= LeftActingAlgebra(V);
   R:= RootSystem(L);
   cg:= CrystalGraph( R, hwt );
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
  y:= CanonicalGenerators( R )[2];
  bas1:= [ v ]; bas2:= [ w ];
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
     u:= bas1[pos];
     u:= y[i1]^u;
     u:= u/n1;
     Add( bas1, u );
     u:= bas2[pos];
     u:= y[i1]^u;
     u:= u/n1;
     Add( bas2, u );
  od;
  BV:= BasisNC(V,bas1); BW:= BasisNC(W,bas2);
  return function( u ) return Coefficients( BV, u )*BW; end;
end;




#
# canonical basis where hwv is a vector of hw
#
canbas:= function( V, hwv ) # hwv hw vec
local   L,  R,  hw,  cg,  paths,  strings,  p,  p1, word, k, b,
        st,  i,  j,  a,  y,  v,  bas, s1, i1, n1,  w,  sim, pos, posR, yy, 
        weylwordNF, e, sp, x, m, c, sp0, h;

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
   h:= CanonicalGenerators( R )[3];
   sp:= Basis( VectorSpace( Rationals, [hwv] ), [hwv] );
   hw:= List( h, x -> Coefficients( sp, x^hwv )[1] );
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
  return bas;
end; 


#############################################################################
## now get explicit isom between original module M and hwm [1,1,1,1]
## Basis(M)[16] is (1,0) x (1,0) x (1,0) x (1,0)
## both are hwm with hw [1,1,1,1]

F0:= isomhwmodules( M, Basis(M)[16], V0, Basis(V0)[1], [1,1,1,1] );
F0inv:= isomhwmodules(  V0, Basis(V0)[1],M, Basis(M)[16], [1,1,1,1] );


#############################################################################
# transform a tensor given as  "+(++--)-(-++-)" etc  to V0
#
maptens:= function( list )
local fc, u, k, ev, cf;
   fc:= function( i )
      if i = '+' then return [1,0]; else return [0,1]; fi;
   end;
   cf := function(i)
      if i = '+' then return 1; else return -1; fi;
   end;   

   u:= Zero(M);
   for k in [1..Length(list)/7] do
      ev:= [ List( list{[(k-1)*7+3..k*7-1]}, fc ), cf(list[(k-1)*7+1]) ];
      u:= u + ObjByExtRep( ElementsFamily(FamilyObj(M)),
          ObjByExtRep( ElementsFamily(FamilyObj(UnderlyingLeftModule(M))),ev ) );
   od;
 
  return F0(u);            
end;




#############################################################################
# basis of V0 corresponding to BASIS
#
basV0:=Basis(V0,List(BASISPM,x->maptens(Concatenation("+",x))));



#############################################################################
##
## symKV is module Sym^k(V0)
## v in V0, map it to v^k in sumkV
##
mapvIntoSymKV:= function( k, symkV,  v )
local cf, elm, i, j, l, elm0, mon, c, pos, u,basV0;
  
    basV0:=Basis(V0,List(BASISPM,x->maptens(Concatenation("+",x))));;

    cf:= Coefficients( basV0, v );
    elm:= [ ];
    for i in [1..Length(cf)] do
        if not IsZero(cf[i]) then Add( elm, [i] ); Add( elm, cf[i] ); fi;
    od;
    for j in [2..k] do
       elm0:= [ ];
       for i in [1..Length(cf)] do
          if not IsZero(cf[i]) then
             for l in [1,3..Length(elm)-1] do
                mon:= ShallowCopy( elm[l] );
                Add( mon, i ); Sort(mon);
                c:= cf[i]*elm[l+1];
                pos:= Position( elm0, mon );
                if pos <> fail then
                   elm0[pos+1]:= elm0[pos+1]+c;
                else
                   Add( elm0, mon ); Add( elm0, c );
                fi;
             od;
         fi;
      od;
      elm:= elm0;
   od;
   u:= Zero( symkV );
   for l in [1,3..Length(elm)-1] do
      u:= u + ObjByExtRep( ElementsFamily( FamilyObj(symkV) ),
          ObjByExtRep(ElementsFamily(FamilyObj(UnderlyingLeftModule(symkV))),
                      [ List( elm[l], x -> basV0[x] ), elm[l+1] ] ) );
   od;
   return u;
end;

#############################################################################

mapvUIntoSymKU:= function( k, U,symkU,  v )
local cf, elm, i, j, l, elm0, mon, c, pos, u;

    cf:= Coefficients( Basis(U), v );
    elm:= [ ];
    for i in [1..Length(cf)] do
        if not IsZero(cf[i]) then Add( elm, [i] ); Add( elm, cf[i] ); fi;
    od;
    for j in [2..k] do
       elm0:= [ ];
       for i in [1..Length(cf)] do
          if not IsZero(cf[i]) then
             for l in [1,3..Length(elm)-1] do
                mon:= ShallowCopy( elm[l] );
                Add( mon, i ); Sort(mon);
                c:= cf[i]*elm[l+1];
                pos:= Position( elm0, mon );
                if pos <> fail then
                   elm0[pos+1]:= elm0[pos+1]+c;
                else
                   Add( elm0, mon ); Add( elm0, c );
                fi;
             od;
         fi;
      od;
      elm:= elm0;
   od;
   u:= Zero( symkU );
   for l in [1,3..Length(elm)-1] do
      u:= u + ObjByExtRep( ElementsFamily( FamilyObj(symkU) ),
          ObjByExtRep(ElementsFamily(FamilyObj(UnderlyingLeftModule(symkU))),
                      [ List( elm[l], x -> Basis(U)[x] ), elm[l+1] ] ) );
   od;
   return u;
end;

        
#############################################################################

mapvIntoTensKV:= function( k, symkV,  v )
local cf, elm, i, j, l, elm0, mon, c, pos, u;

    cf:= Coefficients( Basis(V0), v );
    elm:= [ ];
    for i in [1..Length(cf)] do
        if not IsZero(cf[i]) then Add( elm, [i] ); Add( elm, cf[i] ); fi;
    od;
    for j in [2..k] do
       elm0:= [ ];
       for i in [1..Length(cf)] do
          if not IsZero(cf[i]) then
             for l in [1,3..Length(elm)-1] do
                mon:= ShallowCopy( elm[l] );
                Add( mon, i ); 
                c:= cf[i]*elm[l+1];
                pos:= Position( elm0, mon );
                if pos <> fail then
                   elm0[pos+1]:= elm0[pos+1]+c;
                else
                   Add( elm0, mon ); Add( elm0, c );
                fi;
             od;
         fi;
      od;
      elm:= elm0;
   od;
   u:= Zero( symkV );
   for l in [1,3..Length(elm)-1] do
      u:= u + ObjByExtRep( ElementsFamily( FamilyObj(symkV) ),
          ObjByExtRep(ElementsFamily(FamilyObj(UnderlyingLeftModule(symkV))),
                      [ List( elm[l], x -> Basis(V0)[x] ), elm[l+1] ] ) );
   od;
   return u;
end;
        
#############################################################################
actWithGroup := function(rep,v)
local cf, new,  sigs, basV0;

  ## MAT is wrt BASISPM/BASIS, so need this to get cf vector:
  basV0:=Basis(V0,List(BASISPM,x->maptens(Concatenation("+",x))));;
  new :=Coefficients(basV0,v)*MAT;;
  new:=List(new,c-> Value(c,
    [a11,a12,a21,a22,b11,b12,b21,b22,c11,c12,c21,c22,d11,d12,d21,d22],
    Concatenation(rep)));;
  Display(Filtered(List([1..16],x->[new[x],BASISPM[x]]),i-> not i[1]=0));
  new := new*basV0;;
  return new;
end;


#############################################################################
# the next function returns a function mapping a tensor like
# "+(-++-)+(--++)" to a symmetric matrix
# the input is k, which has to be even, Sym^k(V0), 
# hw1, which is the highest weight
# of an irreducible module in Sym^k(V0), hw2, which is the highest weight
# of an irreducible module W such that Sym^2(W) contains a submodule of
# highest weight hw1.

#
# get weights of h-components acting on u
#
wtofvec:= function( h, u )
local sp;
   sp:= Basis( VectorSpace( Rationals, [u] ), [u] );
   return List( h, x -> Coefficients( sp, x^u )[1] );
end;


symmatfromtens:= function( k, symkV, hw1, hw2 )
local h, dsym, i, wt, l1, l2, W, sym2W, dW, is, B0, vv, B1, fct, first;
    h   := CanonicalGenerators( RootSystem(L) )[3];

    dsym:= DirectSumDecomposition( symkV ); 
    Print("direct sum dec done\n");

    # look for submodle of wt hw1
    l1 := -1;
    for i in [1..Length(dsym)] do
       wt:= wtofvec( h, GeneratorsOfAlgebraModule( dsym[i] )[1] );
       if wt = hw1 then l1:= i; break; fi;
    od;
    if l1 = -1 then Error("could not find module in symkV"); fi;

    # here construct hw2 module W directly    
    # and look for submodule of wt hw1 in it
    W:= HighestWeightModule( L, hw2 );
    sym2W:= SymmetricPowerOfAlgebraModule( W, 2 );
        dW:= DirectSumDecomposition( sym2W );
    l2 := -1;
    for i in [1..Length(dW)] do
        wt:= wtofvec( h, GeneratorsOfAlgebraModule( dW[i] )[1] );
        if wt = hw1 then l2:= i; break;fi;
    od;
    if l2 = -1 then Error("could not find module in W"); fi;
    is:= isomhwmodules( dsym[l1], GeneratorsOfAlgebraModule(dsym[l1])[1],
                      dW[l2], GeneratorsOfAlgebraModule( dW[l2] )[1], hw1 );


    ## get basis / dims through direct sum decomp of symKV
    if not IsBound( symkV!.dims ) then
       Print("start special basis\n");
       B0:= List( dsym, U -> canbas( U, GeneratorsOfAlgebraModule(U)[1]) );
       symkV!.dims:= List( B0, Length );
       symkV!.canBas:= Basis( symkV, Concatenation(B0) );
       symkV!.listBas:= B0;
       Print("special basis done\n");
    fi;

    ## our submodules are dsym[l1] and dW[l2]
    fct:= function( ten )
    local vk, u, w, mat, ew, j, s, cf;
        vk:= mapvIntoSymKV( k, symkV, maptens( ten ) );
 
        # now get projection of vk into dsym[l1]
        cf:= Coefficients( symkV!.canBas, vk );
        cf:= cf{[Sum(symkV!.dims{[1..l1-1]})+1..Sum(symkV!.dims{[1..l1]})]};
        u:= cf*symkV!.listBas[l1];
   
        # now map this u via isom "is" into dW[l2] in W
        w:= is(u);
        mat:= NullMat( Dimension(W), Dimension(W) );
        if IsZero(w) then return mat; fi;
        ew:= ExtRepOfObj( ExtRepOfObj( w ) );
        for j in [1,3..Length(ew)-1] do
           s:= List( ew[j], x -> Position( BasisVectors(Basis(W)), x ) );
           if not s[1]=s[2] then
              mat[s[1]][s[2]]:= ew[j+1]/2;
              mat[s[2]][s[1]]:= ew[j+1]/2;
           else
              mat[s[1]][s[2]]:= ew[j+1];
              mat[s[2]][s[1]]:= ew[j+1];
           fi;
        od;
        return mat;
     end;
     return fct;
end;







## 
## tens must be list of tensor classifiers (f2 or f4 in my workspace)
## orb1 and orb2 must be numbers between 1..30 with 
## complex orb1 contained in orb2
## checks whether we can conclude that real orb1.i cannot lie in real orb2.j
##
compareClassifiersOf := function(tens,orb1, orb2)
local small, large, i, j, k,s;

   small := List(ORBITS[orb1].reps, orb -> List(tens, f-> mySignature(f(orb))));
   large := List(ORBITS[orb2].reps, orb -> List(tens, f-> mySignature(f(orb))));

   for s in [1..Size(small)] do 
    #Print("tensclass of smaller orbit ",[orb1,s],"\n");
    #Print(small[s],"\n");
     Print("\n");     

     for i in [1..Size(large)] do 
       #Print("tensclass for ",[orb2,i],": \n");
       #Print(large[i],"\n");
     od;

     for i in [1..Size(large)] do
        for j in [1..Size(large[i])] do
           if ForAny([1,2],x-> small[s][j][x]> large[i][j][x]) then
              Print("----> ", [orb1,s]," cannot lie in Orbit ",[orb2,i]," have",small[s][j]," ",large[i][j],"\n");
              break;
           fi;
        od;
     od;
   od;
end; 





compareALLClassifiers := function(alltens,orblist)
local small, large, i, j, k,s,ii,jj,orb1,orb2;

   for ii in [1..Size(orblist)-1] do
      for jj in [ii+1..Size(orblist)] do
         orb1 := orblist[ii];
         orb2 := orblist[jj];
         small:=alltens[ii];
         large:=alltens[jj];


         for s in [1..Size(small)] do
	 Print("\n");
         for i in [1..Size(large)] do
           for j in [1..Size(large[i])] do
            if ForAny([1,2],x-> small[s][j][x]> large[i][j][x]) then
               Print("----> ", [orb1,s]," cannot lie in Orbit ",[orb2,i]," have ",small[s][j]," ",large[i][j],"\n");
               break;
            fi;
         od;
      od;
    od;
    od;
    od;
end; 



##############################################################################

Display("now start the calculations for Sym2");
Display("edit GAP file to run it for Sym6, but this will take time");


S2  := SymmetricPowerOfAlgebraModule(V0,2);;
dS2 := DirectSumDecomposition(S2);
w2  := List( dS2, HighestWeight );
w2  := Filtered(w2, x-> ForAll(x,IsEvenInt));
f2  := List(w2,i-> symmatfromtens(2,S2,i,i/2));

#S6  := SymmetricPowerOfAlgebraModule(V0,6);;
#dS6 := DirectSumDecomposition(S6);
#w6  := List( dS6, HighestWeight );
#w6  := Filtered(w6, x-> ForAll(x,IsEvenInt));
#f6  := List(w6,i-> symmatfromtens(6,S6,i,i/2));



all:=f2;
orblist:=[1,7,11,15,16,22,26,30];
alltens:=[];
for x in orblist do  
   y:=List(ORBITS[x].reps,orb-> List(all, f-> mySignature(f(orb))));
   Display(x);Add(alltens,y);
od;

compareALLClassifiers(alltens,orblist);
