edge(1, 6).
edge(2, 1).
edge(2, 3).
edge(2, 4).
edge(3, 1).
edge(3, 4).
edge(4, 5).
edge(5, 2).
edge(5, 6).
edge(6, 4).
edge(1, 2).

path(Start, End, P) :-
    path(Start, End, [], P).

path(Start, Start, _, [Start]):-!.
path(Start, End, Visited, [Start|Path]) :-
    \+ member(Start, Visited),
    edge(Start, Node),
    path(Node, End, [Start|Visited], Path).
