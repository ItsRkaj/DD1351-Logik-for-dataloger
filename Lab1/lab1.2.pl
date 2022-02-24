reverselist([],[]).
reverselist([H|T], F):-
    reverselist(T, T2),
    append(T2, [H], F).

remove_duplicates([], []).
remove_duplicates(L, E) :-
    reverselist(L, R),
    remove_duplicates2(R, R2),
    reverselist(R2, E).

remove_duplicates2([], []).
remove_duplicates2([H|T], F) :-
    member(H, T),
    remove_duplicates2(T, F).

remove_duplicates2([H|T], [H|F]) :-
    \+ (member(H, T)),
    remove_duplicates2(T, F).
