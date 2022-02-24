% For SICStus, uncomment line below: (needed for member/2)
% use_module(library(lists)).
% Load model, initial state and formula from file.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).
% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid. %
% (T,L), S |- F %U
% To execute: consult('your_file.pl'). verify('input.txt').
% Literals
%check(_, L, S, [], X) :- ... %check(_, L, S, [], neg(X)) :- ...
% And
%check(T, L, S, [], and(F,G)) :- ...

%-------------------------------CHECK-------------------------------
check(_,[],_,_,_):-
    fail.

check(_, [[S|[T]]|_], S, [], X) :-
    atom(X),
    atom_length(X,1),
    member(X,T).

check(_, [_|T], S, [], X) :-
    atom(X),
    atom_length(X,1),
    check(_,T, S, [], X).

%-------------------------------RULES-------------------------------
% Neg
check(T, L, S, [], neg(X)) :-
    \+check(T,L, S, [] ,X).
% And
check(T, L, S, [], and(X,Y)) :-
    check(T, L, S, [], X),
    check(T, L, S, [] ,Y).
% Or
check(T, L, S, [], or(X, Y)) :-
    check(T, L, S, [], X);
    check(T, L, S, [] ,Y).
% AX
check(T, L, S, _, ax(X)) :-
    getInnerSTL(T, S, SL),
    ctrlAX(SL, T, L, X).
% EX
check(T, L, S, [], ex(X)) :-
    getInnerSTL(T, S, SL),
    ctrlEX(SL, T, L, X).
% AG
check(T, L, S, HK, ag(X)) :-
    getInnerSTL(T, S, SL),
    ctrlAG(SL, S, T, L, X, HK).
% EG
check(T, L, S, HK, eg(X)) :-
    getInnerSTL(T, S, SL),
    ctrlEG(SL, S, T, L, X, HK).
% EF
check(T, L, S, HK, ef(X)) :-
    getInnerSTL(T, S, SL),
    ctrlEF(SL, S, T, L, X, HK).
% AF
check(T, L, S, HK, af(X)) :-
    getInnerSTL(T, S, SL),
    ctrlAF(SL, S, T, L, X, HK).

%-----------------------------RULES EXT.----------------------------
% AX
ctrlAX([], _, _, _).

ctrlAX([H|Tail], T, L, X) :-
    check(T, L, H, [], X),
    ctrlAX(Tail, T, L, X).
% EX
ctrlEX([H|Tail], T, L, X) :-
    check(T, L, H, [], X);
    ctrlEX(Tail, T, L, X).
% AG
ctrlAG(SL,S, T, L, X, HK) :-   % True if a loop is detected
    member(S, HK).

ctrlAG(SL, S, T, L, X, HK) :-  % Verifys AG recursively 
    not(member(S, HK)),
    check(T, L, S, [],X),
    foreachCtrlAG(SL, T, L, X, [S|HK]).

foreachCtrlAG([],_,_,_,_).     % Does forEach on all elements in Tail

foreachCtrlAG([H|Tail], T, L, X, HK) :-
    check(T, L, H, HK, ag(X)),
    foreachCtrlAG(Tail, T, L, X, HK).
% EG
ctrlEG(SL, S, T, L, X, HK) :-
    member(S, HK).

ctrlEG(SL, S, T, L, X, HK) :-
    not(member(S, HK)),
    check(T, L, S, [], X),
    foreachCtrlEG(SL, T, L, X, [S|HK]).

foreachCtrlEG([H|Tail], T, L , X, HK) :-
    check(T, L, H, HK, eg(X));
    foreachCtrlEG(Tail, T, L, X, HK).
% EF
ctrlEF(_, S, _, _,_,HK) :-
    member(S, HK),
    fail.

ctrlEF(SL, S, T, L, X, HK) :-
    not(member(S, HK)),
    (
    check(T, L, S, [], X);
    foreachCtrlEF(SL, T, L, X, [S|HK])
).

foreachCtrlEF([H|Tail], T, L, X, HK) :-
    check(T, L, H, HK, ef(X));
    foreachCtrlEF(Tail, T, L, X, HK).
% AF
ctrlAF(_, S, _, _, _,HK) :-
    member(S, HK),
    fail.

ctrlAF(SL, S, T, L, X, HK) :-
    not(member(S, HK)),
    (
    check(T, L, S, [], X);
    foreachCtrlAF(SL, T, L, X, [S|HK])
).

foreachCtrlAF([], T, L, X, HK).

foreachCtrlAF([H|Tail], T, L, X, HK) :-
    foreachCtrlAF(Tail, T, L, X, HK),
    check(T, L, H, HK, af(X)).

%-------------------GET INNER STATE TRANSITION LIST---------------------
% Gets the Inner State Transition List for state S
getInnerSTL([[S,[]]|_], S, _) :-
    !,
    fail.

getInnerSTL([[S|[Tail]]|_], S, SL) :-
    SL = Tail.

getInnerSTL([_|Tail], S, SL) :-
    getInnerSTL(Tail, S, SL).