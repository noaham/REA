
// This file contains code to make calculations
// in the reflection equation algebra.


// Before you load this file make sure you have N set
printf "Setting up relations for the reflection equation algebra for N=%o\n", N;

////////////////////////////////////////////////////////////////
// CONTENTS
// 1. Simple helper functions
// 2. Setup of the REA algebra
// 3. Implement PBW relations for REA
// 4. Setup of the FRT algebra
// 5. Implement PBW relations for FRT
// 6. The R-matrix
// 7. Twisting of the REA multiplication to FRT
// 8. Inverse of the twist map
// 9. The adjoint action on the REA
// 10. The invariants
// 11. Truncated minors, DL minors and REA minors
// 12. The quantum Cayley Hamilton identity

////////////////////////////////////////////////////////////////
// 1. First we have some general helper functions

// delta function
d:= function(i,j)
    if i eq j then
        return 1;
    else
        return 0;
    end if;
end function;

// theta function
t:= function(x)
    if x gt 0 then
        return 1;
    else
        return 0;
    end if;
end function;

// For a word w, one can access letters by w[i] however w[2..5] does not work
// as expected. Instead we implement a function to solve this.
wordRange := function(w,L)
    wNew := w[L[1]];
    for i in L[2..#L] do
        wNew := wNew * w[i];
    end for;
    return wNew;
end function;


////////////////////////////////////////////////////////////////
// 2. Setting up the algebra and variables


// We work over the field with one indetirminent q over the rationals. 

G := SymmetricGroup(N);

F<q>:=FunctionField(Rationals(),1);

A:=FreeAlgebra(F,N^2);

// We rename the variables to make them easier to work with.
//This just renames the generators of the free algebra in a more reasonable way.

biIndex:=function(varName,k) 
    superScript:= (k div N)+1;
    subScript:= k mod N;
    if subScript eq 0 then
        subScript:=N; 
        superScript:=superScript-1;
    end if;
    returnString := "(" cat varName cat "^" cat IntegerToString(superScript) cat "_";
    returnString := returnString cat IntegerToString(subScript) cat ")";
    return returnString;
end function;

AssignNames(~A,[biIndex("a",t): t in [1..N^2]]);

// A function to return the relavent variable

a:=function(i,j)
    if (i-1)*N+j gt N^2 or (i-1)*N+j lt 1  then
        return 0;
    else
        return A.((i-1)*N+j);
    end if;
end function;

// a function to identify a generator, assumes y=a^i_j, returns i,j
identify_gen := function(y)
    for ti in [t: t in CartesianPower([1..N],2)] do
        if y eq a(ti[1],ti[2]) then
            return ti;
            break;
        end if;
    end for;
end function;

////////////////////////////////////////////////////////////////
// 3. Here we set up the PBW relations for the REA

forward PBWOrder,PBWOrderBackwards;

PBWSwapList:=AssociativeArray();

for i in [1..N] do
    for j in [1..i-1] do
        for m in [1..N] do
            for n in [1..N] do
                sum:=q^(d(i,n)+d(n,m)-d(m,j))*a(j,n)*a(i,m);
                sum:=sum + q^(d(i,m)-d(j,m))*t(n-m)*(q-1/q)*a(j,m)*a(i,n);
                for p in [i+1..N] do
                    sum:=sum + (q-1/q)*q^(d(n,m)-d(j,m))*d(i,n)*a(j,p)*a(p,m);
                    sum:=sum + (q-1/q)^2*q^(-d(m,j))*d(i,m)*t(n-m)*a(j,p)*a(p,n);
                end for;
                if j eq m then
                    for p in [j+1..N] do
                        sum:=sum - (1-1/q^2)*a(i,p)*a(p,n);
                    end for;
                end if;
                PBWSwapList[a(i,m)*a(j,n)]:=sum;
            end for;
        end for;
    end for;    
    for m in [1..N] do
         for n in [1..m-1] do
            sum:=q^(d(i,n)-d(m,i)-1)*a(i,n)*a(i,m);
            for p in [i+1..N] do
                sum:= sum + q^(-1-d(m,i))*(q-1/q)*a(i,p)*d(i,n)*a(p,m);
                sum:= sum - (1-1/q^2)*d(m,i)*a(i,p)*a(p,n);
            end for;
            PBWSwapList[a(i,m)*a(i,n)]:=sum;
        end for;
    end for;
end for;                 

function PBWOrderMonomial(m)
    for i in [1..Length(m)-1] do
        if IsDefined(PBWSwapList,m[i]*m[i+1]) then
            prod1:=1;
            for j in [1..i-1] do
                prod1:=prod1*m[j];
            end for;
            prod2:=PBWSwapList[m[i]*m[i+1]];
            prod3:=1;
            for j in [i+2..Length(m)] do
                prod3:=prod3*m[j];
            end for;
            return PBWOrder(prod1*prod2*prod3);
        end if;
    end for;
    return m;    
end function;

function PBWOrderMonomialBackwards(m)
    for i in [1..Length(m)-1] do
        iBack:=Length(m)-i;
        if IsDefined(PBWSwapList,m[iBack]*m[iBack+1]) then
            prod1:=1;
            for j in [1..iBack-1] do
                prod1:=prod1*m[j];
            end for;
            prod2:=PBWSwapList[m[iBack]*m[iBack+1]];
            prod3:=1;
            for j in [iBack+2..Length(m)] do
                prod3:=prod3*m[j];
            end for;
            return PBWOrderBackwards(prod1*prod2*prod3);
        end if;
    end for;
    return m;    
end function;

function PBWOrder(a)
    orderedExpr:=0;
    for m in Monomials(a) do
        orderedExpr:= orderedExpr + MonomialCoefficient(a,m)*PBWOrderMonomial(m);
    end for;
    return orderedExpr;
end function;

function PBWOrderBackwards(a)
    orderedExpr:=0;
    for m in Monomials(a) do
        orderedExpr:= orderedExpr + MonomialCoefficient(a,m)*PBWOrderMonomialBackwards(m);
    end for;
    return orderedExpr;
end function;

// This is necessary because the relations as written don't automatically
// put things in PBW order, just closer to PBW order

for k in Keys(PBWSwapList) do
	PBWSwapList[k]:=PBWOrder(PBWSwapList[k]);
end for;                    

// This functions checks if something is in PBW order.

function PBWOrdered(m)
   for i in [1..Length(m)-1] do
   if IsDefined(PBWSwapList,m[i]*m[i+1]) then return false; end if;
   end for;
   return true;
end function;

////////////////////////////////////////////////////////////////
// 4. The FRT algebra

// The FRT algebra is similar to the REA algebra and we set it up in
// the same way.

B:=FreeAlgebra(F,N^2);

// We rename the variables to make them easier to work with.
//This just renames the generators of the free algebra in a more reasonable way.

AssignNames(~B,[biIndex("x",t): t in [1..N^2]]);

// A function to return the relavent variable

x:=function(i,j)
    if (i-1)*N+j gt N^2 or (i-1)*N+j lt 1  then
        return 0;
    else
        return B.((i-1)*N+j);
    end if;
end function;

// a function to identify a generator, assumes y=a^i_j, returns i,j
identify_genFRT := function(y)
    for ti in [t: t in CartesianPower([1..N],2)] do
        if y eq x(ti[1],ti[2]) then
            return ti;
            break;
        end if;
    end for;
end function;

////////////////////////////////////////////////////////////////
// 5. Here we set up the FRT-PBW relations

forward FRTPBWOrder,FRTPBWOrderBackwards;

FRTPBWSwapList:=AssociativeArray();

for i in [1..N] do
    for j in [1..i-1] do
        for k in [1..N] do
            for l in [1..N] do
                if k eq l then
                    new := q^(-1)*x(j,k)*x(i,k);
                elif k lt l then
                    new := x(j,l)*x(i,k);
                elif l lt k then
                    new := x(j,l)*x(i,k) + (q^(-1)-q)*x(j,k)*x(i,l);
                end if;
                FRTPBWSwapList[x(i,k)*x(j,l)]:=new;
            end for;
        end for;
    end for;    
    for k in [1..N] do
         for l in [1..k-1] do
            new := q^(-1)*x(i,l)*x(i,k);
            FRTPBWSwapList[x(i,k)*x(i,l)]:=new;
        end for;
    end for;
end for;                 

function FRTPBWOrderMonomial(m)
    for i in [1..Length(m)-1] do
        if IsDefined(FRTPBWSwapList,m[i]*m[i+1]) then
            prod1:=1;
            for j in [1..i-1] do
                prod1:=prod1*m[j];
            end for;
            prod2:=FRTPBWSwapList[m[i]*m[i+1]];
            prod3:=1;
            for j in [i+2..Length(m)] do
                prod3:=prod3*m[j];
            end for;
            return FRTPBWOrder(prod1*prod2*prod3);
        end if;
    end for;
    return m;    
end function;

function FRTPBWOrderMonomialBackwards(m)
    for i in [1..Length(m)-1] do
        iBack:=Length(m)-i;
        if IsDefined(FRTPBWSwapList,m[iBack]*m[iBack+1]) then
            prod1:=1;
            for j in [1..iBack-1] do
                prod1:=prod1*m[j];
            end for;
            prod2:=FRTPBWSwapList[m[iBack]*m[iBack+1]];
            prod3:=1;
            for j in [iBack+2..Length(m)] do
                prod3:=prod3*m[j];
            end for;
            return FRTPBWOrderBackwards(prod1*prod2*prod3);
        end if;
    end for;
    return m;    
end function;

function FRTPBWOrder(a)
    if a eq 0 then
        return 0;
    else
        orderedExpr:=0;
        for m in Monomials(a) do
            orderedExpr:= orderedExpr + MonomialCoefficient(a,m)*FRTPBWOrderMonomial(m);
        end for;
        return orderedExpr;
    end if;
end function;

function FRTPBWOrderBackwards(a)
    orderedExpr:=0;
    for m in Monomials(a) do
        orderedExpr:= orderedExpr + MonomialCoefficient(a,m)*FRTPBWOrderMonomialBackwards(m);
    end for;
    return orderedExpr;
end function;

// This is necessary because the relations as written don't automatically
// put things in FRTPBW order, just closer to FRTPBW order

for k in Keys(FRTPBWSwapList) do
	FRTPBWSwapList[k]:=FRTPBWOrder(FRTPBWSwapList[k]);
end for;                    

// This functions checks if something is in FRTPBW order.

function FRTPBWOrdered(m)
   for i in [1..Length(m)-1] do
   if IsDefined(FRTPBWSwapList,m[i]*m[i+1]) then return false; end if;
   end for;
   return true;
end function;

////////////////////////////////////////////////////////////////
// 6. The R-matrix

// The following is a map from [11..1N,21..NN] to [1..N^2]that swaps between the
// two ways of indexing into the Kronecker product of 2 NxN matrices. It sets up
// the lexigraphic order on pairs.

indexIntoKronecker := function(i,j)
    return (i-1)*N + j;
end function;

indexIntoKroneckerInv := function(i)
    return Ceiling(i/N), i - (Ceiling(i/N)-1)*N;
end function;

// Some code to set up the elementary matrices

Elmat := function(i,j)
    return Matrix([[d(b,i)*d(a,j) : a in [1..N]] : b in [1..N]]);
end function;

// Calculating the R-matrix and its inverse

Rmatrix := 0;
for i in [1..N] do
    Rmatrix := Rmatrix + q*KroneckerProduct(Elmat(i,i),Elmat(i,i));
end for;
for i in [1..N] do
    for j in [j : j in {1..N} diff {i} ] do
        Rmatrix := Rmatrix + KroneckerProduct(Elmat(i,i),Elmat(j,j));
    end for;
end for;
for i in [1..N] do
    for j in [j : j in [1..i-1]] do
        Rmatrix := Rmatrix + (q-q^(-1))*KroneckerProduct(Elmat(i,j),Elmat(j,i));
    end for;
end for;

iRmatrix := 0;
for i in [1..N] do
    iRmatrix := iRmatrix + q^(-1)*KroneckerProduct(Elmat(i,i),Elmat(i,i));
end for;
for i in [1..N] do
    for j in [j : j in {1..N} diff {i} ] do
        iRmatrix := iRmatrix + KroneckerProduct(Elmat(i,i),Elmat(j,j));
    end for;
end for;
for i in [1..N] do
    for j in [j : j in [1..i-1]] do
        iRmatrix := iRmatrix - (q-q^(-1))*KroneckerProduct(Elmat(i,j),Elmat(j,i));
    end for;
end for;

// Given an N^2 x N^2 matrix, this transposes on the second factor

transpose2 := function(M)
    newMat := M;
    for indexes in CartesianPower({1..N},2) do
        i := 1 + N*(indexes[1] - 1);
        j := 1 + N*(indexes[2] - 1);
        B := Transpose(Submatrix(M,i,j,N,N));
        newMat := InsertBlock(newMat,B,i,j);
    end for;
    return newMat;
end function;


// R-tilde is ((R^t2)^-1)^t2, where t2 is conjugation in the second factor

RmatrixTilde := transpose2((transpose2(Rmatrix)^(-1)));

// Here we provide a standard way of indexing into the various R-matrices
// The first provides R^ij_kl

R := function(i,j,k,l)
    return Rmatrix[indexIntoKronecker(i,j),indexIntoKronecker(k,l)];
end function;

Rinv := function(i,j,k,l)
    return iRmatrix[indexIntoKronecker(i,j),indexIntoKronecker(k,l)];
end function;

Rtilde := function(i,j,k,l)
    return RmatrixTilde[indexIntoKronecker(i,j),indexIntoKronecker(k,l)];
end function;


////////////////////////////////////////////////////////////////
// 7. Twisting of the REA multiplication to FRT

// There is an isomorphism (of vector spaces) REA -> FRT implemented
// below as twist(). On generators it sends a^i_j -> x^i_j

// first on deg two terms
// twist(a^i_j * a^j_l) = R^in_st x^s_m Rtilde^mk_jn x^t_l

twist_deg2 := function(ab)
    result := 0;
    sij := identify_gen(ab[1]);
    i := sij[1];
    j := sij[2];
    tkl := identify_gen(ab[2]);
    k := tkl[1];
    l := tkl[2];
    for indexes in CartesianPower({1..N},4) do
        n := indexes[1];
        s := indexes[2];
        t := indexes[3];
        m := indexes[4];
        result := result + R(i,n,s,t)*a(s,m)*Rtilde(m,k,j,n)*a(t,l);
    end for;
    return result;
end function;

// now we define the REA to FRT of a*p where a is deg 1 and p is
// arbitrary (but is an FRT element)

indexIntoMon := function(m,I)
    prod := 1;
    for i in I do
        prod := prod * m[i];
    end for;
    return prod;
end function;


twist_1mon := function(ab,mon)
    sij := identify_gen(ab[1]);
    i := sij[1];
    j := sij[2];
    deg := Degree(mon);
    if deg eq 1 then
        newmon := twist_deg2(ab*mon);
    else
        last := mon[deg];
        fl_terms := twist_deg2(ab*last);
        newmon := 0;
        for mmon in Monomials(fl_terms) do
            pre := mmon[1];
            post := mmon[2];
            newmmon := $$(pre,indexIntoMon(mon,[1..deg-1]))*post;
            newmon := newmon + MonomialCoefficient(fl_terms,mmon)*newmmon;
        end for;
    end if;
    return newmon;
end function;                

twist_1arb := function(ab,p)
    result := 0;
    sij := identify_gen(ab[1]);
    i := sij[1];
    j := sij[2];
    for mon in Monomials(p) do
        result := result + MonomialCoefficient(p,mon)*twist_1mon(ab,mon);
    end for;
    return result;
end function;


// now the twist on a general element.

internal_twist := function(p)
    newp := 0;
    if p eq 0 then
        return 0;
    else 
        for mon in Monomials(p) do
            deg := Degree(mon);
            if deg eq 1 then
                newmon := mon;
            else
                first := mon[1];
                rest := indexIntoMon(mon,[2..deg]);
                newmon := twist_1arb(first,$$(rest));
            end if;
            newp := newp + MonomialCoefficient(p,mon)*newmon;
        end for;
        return newp;
    end if;
end function;

atox := function(p)
    result := 0;
    for mon in Monomials(p) do
        if Degree(mon) eq 0 then
            newmon := mon;
        else
            newmon := 1;
            for i in [1..Degree(mon)] do
                aij := identify_gen(mon[i]);
                newmon := newmon*x(aij[1],aij[2]);
            end for;
        end if;
        result := result + MonomialCoefficient(p,mon)*newmon;
    end for;
    return result;
end function;

twist := function(p)
    return atox(internal_twist(p));
end function;


////////////////////////////////////////////////////////////////
// 8. Inverse of the twist

// This is a map FRT -> REA

// first on deg two terms
// itwist(x^i_j * x^k_l) = a^s_t a^v_l iR^ik_su R^tu_jv

itwist_deg2 := function(ab)
    result := 0;
    sij := identify_gen(ab[1]);
    i := sij[1];
    j := sij[2];
    tkl := identify_gen(ab[2]);
    k := tkl[1];
    l := tkl[2];
    for indexes in CartesianPower({1..N},4) do
        s := indexes[1];
        t := indexes[2];
        u := indexes[3];
        v := indexes[4];
        result := result + x(s,t)*x(v,l)*Rinv(i,k,s,u)*R(t,u,j,v);
    end for;
    return result;
end function;

// now we define the REA to FRT of a*p where a is deg 1 and p is
// arbitrary (but is an REA element)

itwist_1mon := function(mon,ab)
    sij := identify_gen(ab[1]);
    i := sij[1];
    j := sij[2];
    deg := Degree(mon);
    if deg eq 1 then
        newmon := itwist_deg2(mon*ab);
    else
        first := mon[1];
        fl_terms := itwist_deg2(first*ab);
        newmon := 0;
        for mmon in Monomials(fl_terms) do
            pre := mmon[1];
            post := mmon[2];
            newmmon := pre*$$(indexIntoMon(mon,[2..deg]),post);
            newmon +:= MonomialCoefficient(fl_terms,mmon)*newmmon;
        end for;
    end if;
    return newmon;
end function;                

itwist_1arb := function(p,ab)
    result := 0;
    sij := identify_gen(ab[1]);
    i := sij[1];
    j := sij[2];
    for mon in Monomials(p) do
        result := result + MonomialCoefficient(p,mon)*itwist_1mon(mon,ab);
    end for;
    return result;
end function;


// now the twist on a general element.

internal_itwist := function(p)
    newp := 0;
    if p eq 0 then
        return 0;
    else 
        for mon in Monomials(p) do
            deg := Degree(mon);
            if deg eq 1 then
                newmon := mon;
            else
                last := mon[deg];
                rest := indexIntoMon(mon,[1..deg-1]);
                newmon := itwist_1arb($$(rest),last);
            end if;
            newp := newp + MonomialCoefficient(p,mon)*newmon;
        end for;
        return newp;
    end if;
end function;

xtoa := function(p)
    result := 0;
    for mon in Monomials(p) do
        if Degree(mon) eq 0 then
            newmon := mon;
        else
            newmon := 1;
            for i in [1..Degree(mon)] do
                aij := identify_genFRT(mon[i]);
                newmon := newmon*a(aij[1],aij[2]);
            end for;
        end if;
        result := result + MonomialCoefficient(p,mon)*newmon;
    end for;
    return result;
end function;

itwist := function(p)
    return xtoa(internal_itwist(p));
end function;


////////////////////////////////////////////////////////////////
// 9. The adjoint action

// Implements the action of K,E,F,H,K^{-1} and H^{-1} on the REA

K := function(m,p)
	if p eq 0 or p eq 1 then
        return p;
    else
        pNew := 0;
        monomials := Monomials(p);
        for n in monomials do
            if Length(n) eq 1 then
                tij := identify_gen(n);
                i := tij[1];
                j := tij[2];
                nNew := q^(d(m,i) - d(m,j))*n;
            else
                L:= Length(n);
                nNew := $$(m,n[1])*$$(m,wordRange(n,[2..L])); 
            end if;                                           
            pNew := pNew + MonomialCoefficient(p,n)*nNew;
        end for;
        return pNew;
    end if;
end function;


invK := function(m,p)
	if p eq 0 or p eq 1 then
        return p;
    else
        pNew := 0;
        monomials := Monomials(p);
        for n in monomials do
            if Length(n) eq 1 then
                tij := identify_gen(n);
                i := tij[1];
                j := tij[2];
                nNew := q^(d(m,j) - d(m,i))*n;
            else
                L:= Length(n);
                nNew := $$(m,n[1])*$$(m,wordRange(n,[2..L])); 
            end if;                                           
            pNew := pNew + MonomialCoefficient(p,n)*nNew;
        end for;
        return pNew;
    end if;
end function;

H := function(m,p)
    return K(m,invK(m+1,p));
end function;

invH := function(m,p)
    return invK(m,K(m+1,p));
end function;


E := function(m,p)
	if p eq 0 or p eq 1 then
        return p;
    else
        pNew := 0;
        monomials := Monomials(p);
        for n in monomials do
            if Length(n) eq 1 then
                tij := identify_gen(n);
                i := tij[1];
                j := tij[2];
                nNew := d(m,j)*a(i,j+1) - d(m+1,i)*q^(d(m+1,j)-d(m,j)+1)*a(i-1,j);
            else
                L:= Length(n);
                rest := wordRange(n,[2..L]);
                nNew := $$(m,n[1])*H(m,rest) + n[1]*$$(m,rest); 
            end if; 
            pNew := pNew + MonomialCoefficient(p,n)*nNew;
        end for;
        return pNew;
    end if;
end function;


F := function(m,p)
	if p eq 0 or p eq 1 then
        return p;
    else
        pNew := 0;
        monomials := Monomials(p);
        for n in monomials do
            if Length(n) eq 1 then
                tij := identify_gen(n);
                i := tij[1];
                j := tij[2];
                nNew := d(m+1,j)*q^(d(m+1,i) - d(m,i))*a(i,j-1) - d(m,i)*q^(-1)*a(i+1,j);
            else
                L:= Length(n);
                rest := wordRange(n,[2..L]);
                nNew := $$(m,n[1])*rest + invH(m,n[1])*$$(m,rest); 
            end if; 
            pNew := pNew + MonomialCoefficient(p,n)*nNew;
        end for;
        return pNew;
    end if;
end function;

// These return apply E or F and the PBW order the result.
                        
PE := function(m,p)
    res := E(m,p);
    if res eq 1 or res eq 0 then
        return res;
    else
        return PBWOrder(res);
    end if;
end function;


PF := function(m,p)
    res := F(m,p);
    if res eq 1 or res eq 0 then
        return res;
    else
        return PBWOrder(res);
    end if;
end function;

////////////////////////////////////////////////////////////////
// 10. The invariants

// This code sets up the invariants in the REA algebra

c_inv:=function(k)
    S := Subsets({1..N},k);
    summation := 0;
    for I in S do
	J:= {1..N} diff I;
	absI:= &+I;
	H := {g : g in G | forall{i:i in J|i eq i^g} };
	for tau in H do
	    term := 1;
	    for i in I do
	        term := term*a(i,i^tau);
	    end for;
            l:=#[i: i in CartesianPower([1..N],2)| i[1] lt i[2] and i[1]^tau gt i[2]^tau];
            n:=#[i: i in [1..N] | i^tau gt i];
	    summation:= summation + (-1)^l*q^(-2*absI+l+n)*term;
	end for; // tau in G
    end for; // I in S
    return summation;
end function;

////////////////////////////////////////////////////////////////
// 11. Truncated minors, DL minors and REA minors

// Say I,J, are k element subsets of [N] and sigma is a permutation in S_k, then this induces
// a bijection I-->J (the identity perm goes to the unique order preserving bij). We define the length
// and exceedence.

exceedance := function(I,J,sigma)
    return #[i: i in [1..#I] | J[i^sigma] gt I[i]];
end function;

length := function(I,J,sigma: U := [1..N])
    k := #I;
    part1 := #[i: i in CartesianPower([1..k],2)| i[1] lt i[2] and i[1]^sigma gt i[2]^sigma];
    part2 := #[i: i in CartesianProduct(U,[1..k])| i[1] notin I and i[1] notin J and i[1] lt I[i[2]] and i[1] gt J[i[2]^sigma]];
    part3 := #[i: i in CartesianProduct([1..k],U)| i[2] notin I and i[2] notin J and I[i[1]] lt i[2] and J[i[1]^sigma] gt i[2]];
    return part1 + part2 + part3;
end function;

Tmin := function(I,J: U := [1..N])
    if #I eq 0 then
        return 1;
    else
        min := 0;
        S := Sym(#I);
        for sigma in S do
            coef := (-q)^(length(I,J,sigma: U:=U))*q^(exceedance(I,J,sigma));
            mon := 1;
            for i in [1..#I] do
                mon := mon * a(I[i],J[i^sigma]);
            end for;
            min := min + coef*mon;
        end for;
        return min;
    end if;
end function;

DLmin := function(I,J)
    min := 0;
    S := Sym(#I);
    for sigma in S do
        coef := (-q)^(length([1..#I],[1..#I],sigma));
        mon := 1;
        for i in [1..#I] do
            mon := mon * x(I[i],J[i^sigma]);
        end for;
        min := min + coef*mon;
    end for;
    return min;
end function;

DL_inv := function(k)
    c := 0;
    for Iset in Subsets({1..N},k) do
        I := Sort(SetToSequence(Iset));
        c +:= q^(-2*(&+I))*DLmin(I,I);
    end for;
    return c;
end function;

////////////////////////////////////////////////////////////////
// 12. The quantum Cayley Hamilton identity

MA := function(f,Mat)
    n:=Nrows(Mat);
    return Matrix([[f(Mat[i,j]): j in [1..n]]: i in [1..n]]);
end function;

AA := Matrix([[a(i,j): j in [1..N]]: i in [1..N]]);

qCH := function()
    sum := AA^N;
    for k in [0..N-1] do
        sum +:= (-1)^(N-k)*q^(2*(N-k))*c_inv(N-k)*AA^k;
    end for;
    return MA(PBWOrder,sum);
end function;
