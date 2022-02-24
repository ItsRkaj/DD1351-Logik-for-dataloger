%----------------------------Main Predicate----------------------------
verify(InputFileName) :-   
    see(InputFileName),
    read(Prem), read(Goal), read(Proof),
    seen,
    proofValid(Prem, Goal, Proof).

%----------------------------Validate Proof----------------------------
proofValid(Prem, Goal, Proof) :-
    proofVerified(Prem, Goal, Proof, Proof,[]), 
    write("   Yes").

proofValid(Prem, Goal, Proof) :-
    \+ proofVerified(Prem, Goal, Proof, Proof,[]),
    write(" No "),
    fail.

%----------------------------Verify Proof----------------------------
%Basfall
proofVerified(Prem, Goal, _,[H], Val) :-   
    lineValid(Prem, Goal, H, C, Val),
    !,
    Goal = C.

%Box
proofVerified(Prem, Goal, Proof, [[[Row, C, assumption]|BT]|T], Val) :-
    L = [Row, C, assumption],
    boxValid(Prem, Goal, BT, [L| Val]),
    proofVerified(Prem, Goal, Proof, T, [[L|BT]|Val]).

%Rad
proofVerified(Prem, Goal, Proof, [H|T], Val) :-
    lineValid(Prem, Goal, H, _,Val),
    proofVerified(Prem, Goal, Proof, T, [H|Val]).

%----------------------------Box Handling----------------------------
%Slut på box
boxValid( _, _, [], _).

%Box in box
boxValid(Prem, Goal, [[[Row, C, assumption]|BT]|T], Val) :-
    L = [Row, C, assumption],
    boxValid(Prem, Goal, BT, [L| Val]),
    boxValid(Prem, Goal, T, [[L|BT]|Val]).

%Line in box
boxValid(Prem, Goal, [H|T], Val) :-
    lineValid(Prem, Goal, H,_,Val),
    boxValid(Prem, Goal, T, [H|Val]).

%----------------------------Line Handling----------------------------
%Individual lines
lineValid(Prem, _, [_, C, Rule], C, Val) :-
    ruleFinder(Rule, C, Prem, Val).

%----------------------------RULES----------------------------
%premise
ruleFinder('premise', C, Prem, _) :-
    member(C, Prem).
%copy
ruleFinder(copy(X), C,_, Val) :-
    clauseFinder(X, Val, C).
%andint
ruleFinder(andint(X,Y), and(XC,YC),_, Val) :-
   clauseFinder(X, Val, XC),
   clauseFinder(Y, Val, YC).
%andel1
ruleFinder(andel1(X), C,_, Val) :-
    clauseFinder(X, Val, and(C,_)).
%andel2
ruleFinder(andel2(Y), C,_, Val) :-
    clauseFinder(Y, Val, and(_,C)).
%orint1
ruleFinder(orint1(X), or(XC,_),_, Val) :-
    clauseFinder(X, Val, XC).
%orint2
ruleFinder(orint2(Y), or(_,YC),_, Val) :-
    clauseFinder(Y, Val, YC).
%orel
ruleFinder(orel(X,Y,U,V,W), C,_, Val) :-
    clauseFinder(X, Val, or(XC, YC)),
    boxFinder(Y, Val, YB),
    clauseFinder(Y, YB, XC),
    clauseFinder(U, YB, C),
    boxFinder(V, Val, VB),
    clauseFinder(V, VB, YC),
    clauseFinder(W, VB, C).
%impel
ruleFinder(impel(X,Y), YC,_, Val) :-
    clauseFinder(X, Val, XC),
    clauseFinder(Y, Val, imp(XC, YC)).
%impint
ruleFinder(impint(X,Y), imp(XC,YC),_, Val) :-
    boxFinder(X, Val, B),
    clauseFinder(X, B, XC),
    clauseFinder(Y, B, YC).
%negnegel
ruleFinder(negnegel(X), C,_, Val) :-
    clauseFinder(X, Val, neg(neg(C))).
%negnegint
ruleFinder(negnegint(X), neg(neg(C)),_, Val) :-
    clauseFinder(X, Val, C).
%lem
ruleFinder(lem, or(X, neg(X)),_,_).
%negint
ruleFinder(negint(X,Y), neg(XC),_, Val) :-
    boxFinder(X, Val, B),
    clauseFinder(X, B, XC),
    clauseFinder(Y, B, cont).
%negel
ruleFinder(negel(X,Y), cont,_, Val) :-
    clauseFinder(X, Val, C),
    clauseFinder(Y, Val, neg(C)).
%contel
ruleFinder(contel(X),_,_, Val) :-
    clauseFinder(X, Val, cont).
%mt
ruleFinder(mt(X,Y), neg(XC),_,Val) :-
    clauseFinder(X, Val, imp(XC,YC)),
    clauseFinder(Y, Val, neg(YC)).
%pbc
ruleFinder(pbc(X,Y), XC,_,Val) :-
    boxFinder(X, Val, B),
    clauseFinder(X, B, neg(XC)),
    clauseFinder(Y, B, cont).

%----------------------------Find Clause----------------------------
%No match
clauseFinder(_,[],_) :-
    fail.

clauseFinder(Row, [[Row, C,_]|_], C).

clauseFinder(Row, [_|T], C) :-
    clauseFinder(Row, T, C).

%----------------------------Find Box----------------------------    
boxFinder(Row, [H|_], H) :-
   member([Row,_,_], H).

boxFinder(Row, [_|T], B) :-
    boxFinder(Row, T, B).
