partstring(X,L,F):-
    append([_,F,_], X),
    length(F,L),
    F \= [].


















%append med 2st är append(listoflist,list).
%Det append gör här att vi låter prolog kolla alla möjliga fall av X som den kan dela in 
%i 3 listor. Det vi tillsist tar hänsyn till är det mellersta elementet F. 
%Prolog kollar alla möjliga kombinationer som den kan ta fram med de element vi 
%har samt hur de distruputeras.
