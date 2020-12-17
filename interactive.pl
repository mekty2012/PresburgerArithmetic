:- [arithlexer].
:- [presburger].

:- use_module(readLine,[readLine/1]).

runOk([bye]).

preburgerDecide :-
  write('Enter your equation >'),nl,
  readLine(X),nl,
  sentence(Sem, X, []),
  (isClosed(Sem) ->
    toQuantifierFree(Sem, FQuantiFree),
    decideClosedQuantifierFree(FQuantiFree, TF),
    (TF =:= 0 ->
      write('Your equation is not true.');
      write('Your equation is true.'));
    write('Your equation is not quantifier free.')  
  )

presburgercurt :-
  interactiveSystem(andList([])).

interactiveSystem(KB) :-
  write('Enter your equation >'),nl,
  readLine(X),nl,
  (runOk(X) ->
    write('Bye!');
    sentence(Sem, X, []),
    checkImpossibility(KB, Sem, Impossible),
    checkUninformativeness(KB, Sem, Uninform).
    (Impossible =:= 0 ->
      % Impossible
      write("That's impossible!"),
      interactiveSystem(KB)
      ;
      write("I believe that."),
      (Uninform =:= 0 ->
        write("That gives me information."),
        interactiveSystem(andL(KB, Sem))
        ;
        write("That is trivial!"),
        interactiveSystem(andL(KB))
        )
      )
    ).

unionSet([], [], []) :- !.
unionSet(L, [], L) :- !.
unionSet([], L, L) :- !.
unionSet([Head | Rest1], [Head | Rest2], [Head | Res]) :-
  unionSet(Rest1, Rest2, Res), !.
unionSet([Head1 | Rest1], [Head2 | Rest2], ResR) :-
  unionSet(Rest1, Rest2, Res),
  (Head1 @< Head2 ->
    ResR is [Head1 | [Head2 | Res]] ;
    ResR is [Head2 | [Head1 | Res]]
    ).

setMinus([], _, []).
setMinus([Head | Rest], Head, Rest) :- !.
setMinus([Head | Rest], X, [Head | Res]) :-
  setMinus(Rest, X, Res).

freeVariable([], []).
freeVariable([(0, _) | Rest], Res) :-
  freeVariable(Rest, Res), !.
freeVariable([(K, _) | Rest], [K | Res]) :-
  freeVariable(Rest, Res).

freeVariable(sltA(A), Res) :-
  freeVariable(A, Res).
freeVariable(sleA(A), Res) :-
  freeVariable(A, Res).
freeVariable(seqA(A), Res) :-
  freeVariable(A, Res).
freeVariable(sneqA(A), Res) :-
  freeVariable(A, Res).
freeVariable(sdivA(_, A), Res) :-
  freeVariable(A, Res).
freeVariable(sndivA(_, A), Res) :-
  freeVariable(A, Res).
freeVariable(andL(F1, F2), Res) :-
  freeVariable(F1, R1),
  freeVariable(F2, R2),
  unionSet(R1, R2, Res).
freeVariable(orL(F1, F2), Res) :-
  freeVariable(F1, R1),
  freeVariable(F2, R2),
  unionSet(R1, R2, Res).
freeVariable(notL(F), R) :-
  freeVariable(F, R).
freeVariable(andL([]), []).
freeVariable(orL([]), []).
freeVariable(andL([Head | Rest]), R) :-
  freeVariable(Head, Res),
  freeVariable(andL(Rest), ResRest),
  unionSet(Res, ResRest, R).
freeVariable(orL([Head | Rest]), R) :-
  freeVariable(Head, Res),
  freeVariable(orL(Rest), ResRest),
  unionSet(Res, ResRest, R).
freeVariable(existsL(X, F), Res) :-
  freeVariable(F, R),
  setMinus(R, X, Res).
freeVariable(forallL(X, F), Res) :-
  freeVariable(F, R),
  setMinus(R, X, Res).

addForall(F, [], F).
addForall(F, [Head | Rest], forallL(Head, F1)) :-
  addForall(F, Rest, F1).

toClosed(F, R) :-
  freeVariable(F, FV),
  addForall(F, FV, R).

checkUninformativeness(KB, F, TF) :-
  toClosed(andL(F, KB), FClosed),
  toQuantifierFree(FClosed, FQuantiFree),
  decideClosedQuantifierFree(FQuantiFree, TF).

checkImpossibility(KB, F, TF) :-
  toClosed(notL(andL(F, KB)), FClosed),
  toQuantifierFree(FClosed, FQuantiFree),
  decideClosedQuantifierFree(FQuantiFree, TF).
