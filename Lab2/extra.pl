verify(InputFileName) :-    see(InputFileName),
                            read(Prems), read(Goal), read(Proof),
                            seen,
                            valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
    Remaining_proof = Proof,
    verify_proof(Prems, Goal, Proof, Remaining_proof,[]).       %skapar en tom lista för validated



%verify_proof är första steget i att bryta ner koden för att verifiera varje rad
%3 möjliga fall:
%1. basfall, sista raden, då ska man ha fått goal.
%2. ny låda, då det är assumption som atom på regelplatsen i nästa rad
%3. Då nästa rad är en "vanlig" rad, då kaller man bara på validate_line sen körs 
%verify_proof med tailen, alltså resten av raderna.

%1
verify_proof(Prems, Goal,_,[H], Validated) :-           %bara H kvar => sista raden, då ska clause = goal, som att bevisa på papper
    validate_line(Prems, Goal, H, Clause, Validated),   % sista raden ok om sann
    !,
    Goal = Clause.

%2
verify_proof(Prems, Goal, Proof, [[[Row,Clause, assumption]|BoxTail]|Tail], Validated) :-
    Line = [Row, Clause, assumption],
    validate_box(Prems, Goal, BoxTail, [Line| Validated]),
    verify_proof(Prems, Goal, Proof, Tail, [[Line|BoxTail]|Validated]). 

%3
verify_proof(Prems, Goal, Proof,[H|Tail], Validated) :-
    validate_line(Prems, Goal, H,_,Validated),
    verify_proof(Prems, Goal, Proof, Tail, [H|Validated]).



%Fixar boxarna
%1 Basfall då boxen är tom. (Boxen ligger i en lista på 3 "argumentet"
%2 Om det är en ny box (alltså assumption) på nästa rad så kallar den rekursivt på 
% sig själv med Boxtail alltså resten av boxen.
%3 När det väl är en egen rad så är det som vanligt att ba kolla nästa rad om den är rätt



%1      Predicate for handling boxes
validate_box(_,_,[],_). % end of box

%2      Handle Box in box
validate_box(Prems, Goal, [[[Row, Clause, assumption]|BoxTail]|Tail], Validated) :-
    Line = [Row, Clause, assumption],
    validate_box(Prems, Goal, BoxTail, [Line| Validated]),
    validate_box(Prems, Goal, Tail, [[Line|BoxTail]|Validated]).

%3      Normal predicate for handling rows in boxes
validate_box(Prems, Goal, [H|Tail], Validated) :-
    validate_line(Prems, Goal, H,_,Validated),
    validate_box(Prems, Goal, Tail, [H|Validated]).




%Den vanliga som bara lyfter ut regeln och clause för att kalla på apply_rule
%Predicate for verifying individual rows
validate_line(Prems, Goal, [_, Clause, Rule], Clause, Validated) :-
    apply_rule(Rule, Clause, Prems, Validated). 



% Ensure that the rule application results in the given clause
%Alla regler är egentligen ba kollat så att det stämmer enligt formelpappret
%imp elimination ska det exempelvis finnas en imp på en rad och en variabel som uppfyller den.
%Är det falskt så är regelin inte rätt och då beviset fel


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
apply_rule(orint2(Y), or(,YClause),, Validated) :-
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

%Anteckningar: Det ända reglerna gör är att kolla. Är båda utrycken sanna? Om ja->true annars false


%Får in en lista på mitten argumentet. 
%1. om listan skalas ner tom så blir det fail, inte hunnits hittats.
%2. annars har den stannats här på tvåan då den kommer in där om [Row, Clause, _]
% har funnits i listan.
%3. Skalar ba ner, alltså skickar vidare tailen så nästa rad är head.

%1
find_clause(_,[],_) :-
    fail.

%2
find_clause(Row, [[Row, Clause,_]|_], Clause). 

%3
find_clause(Row, [_|T], Clause) :-
    find_clause(Row, T, Clause).



%för att hitta en box med  [Row,_,_] i sig, alltså rätt radsnummer.
%Så är det member finns den och då är H själva boxen, eftersom H så står i find_box
% så går den tillbaka via H först och sen Box till Box för att komma tillbaka till
%Box i find_box, exempelvis i pbc


find_box(Row, [H|_], H) :-
   member([Row,_,_], H). 
find_box(Row, [_|Tail], Box) :-
    find_box(Row, Tail, Box).