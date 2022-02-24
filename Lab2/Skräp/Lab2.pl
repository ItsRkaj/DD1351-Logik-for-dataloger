verifiera(InputFileName) :-     see(InputFileName),
                                read(Premiss), read(Dest), read(Bevis),
                                seen,
                                giltigt_bevis(Premiss, Dest, Bevis).

giltigt_bevis(Premiss, Dest, Bevis) :-
    Resterande_bevis = Bevis,
    verifiera_bevis(Premiss, Dest, Bevis, Resterande_bevis,[]).

verifiera_bevis(Premiss, Dest,_,[H], Validerad) :-
    validera_line(Premiss, Dest, H, Klausul, Validerad),
    !,
    Dest = Klausul.
%Predikat som kommer att matcha vid öppningen av en box
verifiera_bevis(Premiss, Dest, Bevis, [[[Row,Klausul, antagande]|BoxTail]|Tail], Validerad) :-
    Line = [Row, Klausul, antagande],
    validera_box(Premiss, Dest, BoxTail, [Line| Validerad]),
    verifiera_bevis(Premiss, Dest, Bevis, Tail, [[Line|BoxTail]|Validerad]). 

verifiera_bevis(Premiss, Dest, Bevis,[H|Tail], Validerad) :-
    validera_line(Premiss, Dest, H,_,Validerad),
    verifiera_bevis(Premiss, Dest, Bevis, Tail, [H|Validerad]).

%Predikat för hantering av boxar
validera_box(_,_,[],_). % slutet av box

%Hantera Boxar i boxar
validera_box(Premiss, Dest, [[[Row, Klausul, antagande]|BoxTail]|Tail], Validerad) :-
    Line = [Row, Klausul, antagande],
    validera_box(Premiss, Dest, BoxTail, [Line| Validerad]),
    validera_box(Premiss, Dest, Tail, [[Line|BoxTail]|Validerad]).

%Normalt predikat för hanterin av rader i boxar
validera_box(Premiss, Dest, [H|Tail], Validerad) :-
    validera(Premiss, Dest, H,_,Validerad),
    validera_box(Premiss, Dest, Tail, [H|Validerad]).

%Predikat för verifiering av inviduella rader
validera_line(Premiss, _, [_, Klausul, Regel], Klausul, Validerad) :-
    tillampa_regel(Regel, Klausul, Premiss, Validerad). %Se till att regeltillämpningen resulterar i det givna klausulen

%premiss
tillampa_regel('premiss', Klausul, Premiss, _) :-
    member(Klausul, Premiss).
%copy
tillampa_regel(copy(X), Klausul,_, Validerad) :-
    hitta_klausul(X, Validerad, Klausul).

%andint
tillampa_regel(andint(X,Y), and(XKlausul,YKlausul),_, Validerad) :-
   hitta_klausul(X, Validerad, XKlausul),
   hitta_klausul(Y, Validerad, YKlausul).

%andel1
tillampa_regel(andel1(X), Klausul,_, Validerad) :-
    hitta_klausul(X, Validerad, and(Klausul,_)).

%andel2
tillampa_regel(andel2(Y), Klausul,_, Validerad) :-
    hitta_klausul(Y, Validerad, and(_,Klausul)).

%orint1
tillampa_regel(orint1(X), or(XKlausul,_),_, Validerad) :-
    hitta_klausul(X, Validerad, XKlausul).

%orint2
tillampa_regel(orint2(Y), or(_,YKlausul),_, Validerad) :-
    hitta_klausul(Y, Validerad, YKlausul).

%orel
tillampa_regel(orel(X,Y,U,V,W), Klausul,_, Validerad) :-
    hitta_klausul(X, Validerad, or(XKlausul, YKlausul)),
    hitta_box(Y, Validerad, YBox),
    hitta_klausul(Y, YBox, XKlausul),
    hitta_klausul(U, YBox, Klausul),
    hitta_box(V, Validerad, VBox),
    hitta_klausul(V, VBox, YKlausul),
    hitta_klausul(W, VBox, Klausul).
%impel
tillampa_regel(impel(X,Y), YKlausul,_, Validerad) :-
    hitta_klausul(X, Validerad, XKlausul),
    hitta_klausul(Y, Validerad, imp(XKlausul, YKlausul)).

%impint
tillampa_regel(impint(X,Y), imp(XKlausul,YKlausul),_, Validerad) :-
    hitta_box(X, Validerad, Box),
    hitta_klausul(X, Box, XKlausul),
    hitta_klausul(Y, Box, YKlausul).

%negnegel
tillampa_regel(negnegel(X), Klausul,_, Validerad) :-
    hitta_klausul(X, Validerad, neg(neg(Klausul))).

%negnegint
tillampa_regel(negnegint(X), neg(neg(Klausul)),_, Validerad) :-
    hitta_klausul(X, Validerad, Klausul).

%lem
tillampa_regel(lem, or(X, neg(X)),_,_).

%negint
tillampa_regel(negint(X,Y), neg(XKlausul),_, Validerad) :-
    hitta_box(X, Validerad, Box),
    hitta_klausul(X, Box, XKlausul),
    hitta_klausul(Y, Box, cont).

%negel
tillampa_regel(negel(X,Y), cont,_, Validerad) :-
    hitta_klausul(X, Validerad, Klausul),
    hitta_klausul(Y, Validerad, neg(Klausul)).

%contel
tillampa_regel(contel(X),_,_, Validerad) :-
    hitta_klausul(X, Validerad, cont).

%mt
tillampa_regel(mt(X,Y), neg(XKlausul),_,Validerad) :-
    hitta_klausul(X, Validerad, imp(XKlausul,YKlausul)),
    hitta_klausul(Y, Validerad, neg(YKlausul)).

%pbc
tillampa_regel(pbc(X,Y), XKlausul,_,Validerad) :-
    hitta_box(X, Validerad, Box),
    hitta_klausul(X, Box, neg(XKlausul)),
    hitta_klausul(Y, Box, cont).


hitta_klausul(_,[],_) :-
    fail.
hitta_klausul(Row, [[Row, Klausul,_]|_], Klausul).
hitta_klausul(Row, [_|T], Klausul) :-
    hitta_klausul(Row, T, Klausul).

hitta_box(Row, [H|_], H) :-
   member([Row,_,_], H). 
hitta_box(Row, [_|Tail], Box) :-
    hitta_box(Row, Tail, Box).


