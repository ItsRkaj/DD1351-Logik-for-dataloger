append(X, [], [X]).
append(X, [Head|Tail], [Head|Y]) :-
    append(X, Tail, Y).

remove_duplicates(In, E) :-
    move(In, [], E).


move([], _, []).

move([Head|Tail], Tp, E):-
    member(Head,Tp),
    move(Tail, Tp, E).

move([Head|Tail], Tp, [Head|Ts]) :-
    \+ member(Head, Tp),   %finns Head i Tp i någon lista?
    move(Tail, [Head|Tp], Ts).
