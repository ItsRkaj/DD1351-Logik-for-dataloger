ƒ% For SICStus, uncomment line below: (needed for member/2)
%:- use_module(library(lists)).
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
% Should evaluate to true iff the sequent below is valid. 
%
% (T,L), S |- F 
% U
% To execute: consult('your_file.pl'). verify('input.txt').
% --------------------------------------------Literals-------------------------------------------
% ----------------------Check All Neighbours----------------------
checkAllNeighb(T, L, S, U, F) :-
    member([S, N], T),
    checkAllStates(T, L, U, F, N).

% ----------------------Check All States----------------------
checkAllStates(_, _, _, _, []).
checkAllStates(T, L, U, F, [H|Tl]) :-   
    check(T, L, H, U, F),
    checkAllStates(T, L, U, F, Tl).

% ----------------------Check Any Neighbours----------------------
checkAnyNeighb(T, L, S, U, F) :-
    member([S, N], T),
    checkAnyStates(T, L, U, F, N).

% ----------------------Check Any States----------------------
checkAnyStates(T, L, U, F, [H|Tl]) :-
    check(T, L, H, U, F);
    checkAnyStates(T, L, U, F, Tl).

% ----------------------Check----------------------
check(_, L, S, [], X) :-
    member([S, A], L),
    member(X, A).

% --------------------------------------------RULES--------------------------------------------
% A - över alla vägar
% E - över någon väg

% X - för nästa tillstånd i vägen
% G - för alla tillstånd i vägen
% F - för något tillstånd i vägen
% ----------------------Neg---------------------
check(_, L, S, [], neg(X)) :-
    member([S, A], L),
    \+ member(X, A).
% ----------------------And---------------------
check(T, L, S, [], and(F,G)) :-
    check(T, L, S, [], F),
    check(T, L, S, [], G).
% ----------------------Or----------------------
check(T, L, S, [], or(F,G)) :-
    check(T, L, S, [], F);
    check(T, L, S, [], G).
% ----------------------AX----------------------
check(T, L, S, [], ax(F)) :-
    checkAllNeighb(T, L, S, [], F).
% ----------------------EX----------------------
check(T, L, S, [], ex(F)) :-
    checkAnyNeighb(T, L, S, [], F).
% ----------------------AG----------------------
% AG1
check(_, _, S, U, ag(_)) :-
    member(S, U).
% AG2
check(T, L, S, U, ag(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),
    checkAllNeighb(T, L, S, [S|U], ag(F)).
% ----------------------EG----------------------
% EG1
check(_, _, S, U, eg(_)) :-
    member(S, U).
% EG2
check(T, L, S, U, eg(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),
    checkAnyNeighb(T, L, S, [S|U], eg(F)).
% ----------------------EF----------------------
% EF1
check(T, L, S, U, ef(F)) :- 
    \+ member(S,U),
    check(T, L, S, [], F).
% EF2
check(T, L, S, U, ef(F)) :- 
    \+ member(S,U),
    checkAnyNeighb(T, L, S, [S|U], ef(F)).
% ----------------------AF----------------------
% AF1
check(T, L, S, U, af(F)) :- 
    \+ member(S, U),
    check(T, L, S, [], F).
% AF2
check(T, L, S, U, af(F)) :- 
    \+ member(S, U),
    checkAllNeighb(T, L, S, [S|U], af(F)).