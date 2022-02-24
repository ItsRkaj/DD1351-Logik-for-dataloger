verify(InputFileName) :-    see(InputFileName),
                            read(Prems), read(Goal), read(Proof),
                            seen,
                            valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
    Remaining_proof = Proof,
    verify_proof(Prems, Goal, Proof, Remaining_proof,[]).

verify_proof(Prems, Goal,_,[H], Validated) :-
    validate_line(Prems, Goal, H, Clause, Validated),
    !,
    Goal = Clause.
%Predicate which will match on the opening of a box
verify_proof(Prems, Goal, Proof, [[[Row,Clause, assumption]|BoxTail]|Tail], Validated) :-
    Line = [Row, Clause, assumption],
    validate_box(Prems, Goal, BoxTail, [Line| Validated]),
    verify_proof(Prems, Goal, Proof, Tail, [[Line|BoxTail]|Validated]). 

verify_proof(Prems, Goal, Proof,[H|Tail], Validated) :-
    validate_line(Prems, Goal, H,_,Validated),
    verify_proof(Prems, Goal, Proof, Tail, [H|Validated]).

%Predicate for handling boxes
validate_box(_,_,[],_). % end of box

%Handle Box in box
validate_box(Prems, Goal, [[[Row, Clause, assumption]|BoxTail]|Tail], Validated) :-
    Line = [Row, Clause, assumption],
    validate_box(Prems, Goal, BoxTail, [Line| Validated]),
    validate_box(Prems, Goal, Tail, [[Line|BoxTail]|Validated]).

%Normal predicate for handling rows in boxes
validate_box(Prems, Goal, [H|Tail], Validated) :-
    validate_line(Prems, Goal, H,_,Validated),
    validate_box(Prems, Goal, Tail, [H|Validated]).

%Predicate for verifying individual rows
validate_line(Prems, _, [_, Clause, Rule], Clause, Validated) :-
    apply_rule(Rule, Clause, Prems, Validated). % Ensure that the rule application results in the given clause

%premise
apply_rule('premise', Clause, Prems, _) :-
    member(Clause, Prems).
%copy
apply_rule(copy(X), Clause,_, Validated) :-
    find_clause(X, Validated, Clause).

%andint
apply_rule(andint(X,Y), and(XClause,YClause),_, Validated) :-
   find_clause(X, Validated, XClause),
   find_clause(Y, Validated, YClause).

%andel1
apply_rule(andel1(X), Clause,_, Validated) :-
    find_clause(X, Validated, and(Clause,_)).

%andel2
apply_rule(andel2(Y), Clause,_, Validated) :-
    find_clause(Y, Validated, and(_,Clause)).

%orint1
apply_rule(orint1(X), or(XClause,_),_, Validated) :-
    find_clause(X, Validated, XClause).

%orint2
apply_rule(orint2(Y), or(_,YClause),_, Validated) :-
    find_clause(Y, Validated, YClause).

%orel
apply_rule(orel(X,Y,U,V,W), Clause,_, Validated) :-
    find_clause(X, Validated, or(XClause, YClause)),
    find_box(Y, Validated, YBox),
    find_clause(Y, YBox, XClause),
    find_clause(U, YBox, Clause),
    find_box(V, Validated, VBox),
    find_clause(V, VBox, YClause),
    find_clause(W, VBox, Clause).
%impel
apply_rule(impel(X,Y), YClause,_, Validated) :-
    find_clause(X, Validated, XClause),
    find_clause(Y, Validated, imp(XClause, YClause)).

%impint
apply_rule(impint(X,Y), imp(XClause,YClause),_, Validated) :-
    find_box(X, Validated, Box),
    find_clause(X, Box, XClause),
    find_clause(Y, Box, YClause).

%negnegel
apply_rule(negnegel(X), Clause,_, Validated) :-
    find_clause(X, Validated, neg(neg(Clause))).

%negnegint
apply_rule(negnegint(X), neg(neg(Clause)),_, Validated) :-
    find_clause(X, Validated, Clause).

%lem
apply_rule(lem, or(X, neg(X)),_,_).

%negint
apply_rule(negint(X,Y), neg(XClause),_, Validated) :-
    find_box(X, Validated, Box),
    find_clause(X, Box, XClause),
    find_clause(Y, Box, cont).

%negel
apply_rule(negel(X,Y), cont,_, Validated) :-
    find_clause(X, Validated, Clause),
    find_clause(Y, Validated, neg(Clause)).

%contel
apply_rule(contel(X),_,_, Validated) :-
    find_clause(X, Validated, cont).

%mt
apply_rule(mt(X,Y), neg(XClause),_,Validated) :-
    find_clause(X, Validated, imp(XClause,YClause)),
    find_clause(Y, Validated, neg(YClause)).

%pbc
apply_rule(pbc(X,Y), XClause,_,Validated) :-
    find_box(X, Validated, Box),
    find_clause(X, Box, neg(XClause)),
    find_clause(Y, Box, cont).

find_clause(_,[],_) :-
    fail.
find_clause(Row, [[Row, Clause,_]|_], Clause).
find_clause(Row, [_|T], Clause) :-
    find_clause(Row, T, Clause).

find_box(Row, [H|_], H) :-
   member([Row,_,_], H). 
find_box(Row, [_|Tail], Box) :-
    find_box(Row, Tail, Box). 

