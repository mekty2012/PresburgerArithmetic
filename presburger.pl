% The all terms in Presburger arithmetic is defined as following.
presburgerAtom(varA(X)) :- integer(X), 0 @< X.
presburgerAtom(natA(X)) :- integer(X), 0 @< X.
presburgerAtom(addA(X, Y)) :- presburgerAtom(X), presburgerAtom(Y).

% If X, Y are two maps representing addition, mergeMap computes its addition.
mergeMap([], Y, Y).
mergeMap([XHead | XRest], [], [XHead | XRest]).

mergeMap([(HeadVar, XHeadCount) | XRest],
         [(HeadVar, YHeadCount) | YRest],
         [(HeadVar, Sum) | RestRes]) :-
    mergeMap(XRest, YRest, RestRes),
    Sum is XHeadCount + YHeadCount,
    Sum \= 0.

mergeMap([(HeadVar, XHeadCount) | XRest],
         [(HeadVar, YHeadCount) | YRest],
         RestRes) :-
    mergeMap(XRest, YRest, RestRes),
    XHeadCount + YHeadCount = 0.

mergeMap([(XHeadVar, XHeadCount) | XRest],
         [(YHeadVar, YHeadCount) | YRest],
         [(XHeadVar, XHeadCount) | RestRes]) :-
    XHeadVar @< YHeadVar,
    mergeMap(XRest, [(YHeadVar, YHeadCount) | YRest], RestRes).

mergeMap([(XHeadVar, XHeadCount) | XRest],
         [(YHeadVar, YHeadCount) | YRest],
         [(YHeadVar, YHeadCount) | RestRes]) :-
    YHeadVar @< XHeadVar,
    mergeMap([(XHeadVar, XHeadCount) | XRest], YRest, RestRes).

% Simplifies atom to sorted map
simplifyAtom(natA(X), [(0, X)]).
simplifyAtom(varA(X), [(X, 1)]).
simplifyAtom(addA(X, Y), Res) :- simplifyAtom(X, XRes), simplifyAtom(Y, YRes), mergeMap(XRes, YRes, Res).

% X to -X
negateMap([], []).
negateMap([(Head, Var) | Rest], [(Head, NVar) | ResRest]) :-
  NVar is 0 - Var,
  negateMap(Rest, ResRest).

% Given two sorted map X, Y, subtract similar terms and return X-Y.
subtractMap([], Y, NY) :-
  negateMap(Y, NY).
subtractMap([XHead | XRest], [], [XHead | XRest]).
subtractMap([(HeadVar, HeadCount) | XRest], [(HeadVar, HeadCount) | YRest], Rest) :-
  subtractMap(XRest, YRest, Rest).
subtractMap([(HeadVar, XHeadCount) | XRest], [(HeadVar, YHeadCount) | YRest], [(HeadVar, HeadCount) | Rest]) :-
  HeadCount is XHeadCount - YHeadCount,
  subtractMap(XRest, YRest, Rest).

subtractMap([(XHeadVar, XHeadCount) | XRest], [(YHeadVar, YHeadCount) | YRest], [(XHeadVar, XHeadCount) | Rest]) :-
  XHeadVar @< YHeadVar,
  subtractMap(XRest, [(YHeadVar, YHeadCount) | YRest], Rest).
subtractMap([(XHeadVar, XHeadCount) | XRest], [(YHeadVar, YHeadCount) | YRest], [(YHeadVar, NYHeadCount) | Rest]) :-
  YHeadVar @< XHeadVar,
  NYHeadCount is 0 - YHeadCount,
  subtractMap([(XHeadVar, XHeadCount) | XRest], YRest, Rest).

% A function that simplifies all the atoms.
simplifyFormula(ltA(X, Y), sltA(Res)) :- simplifyAtom(X, XRes), simplifyAtom(Y, YRes), subtractMap(XRes, YRes, Res).
simplifyFormula(leA(X, Y), sleA(Res)) :- simplifyAtom(X, XRes), simplifyAtom(Y, YRes), subtractMap(XRes, YRes, Res).
simplifyFormula(eqA(X, Y), seqA(Res)) :- simplifyAtom(X, XRes), simplifyAtom(Y, YRes), subtractMap(XRes, YRes, Res).
simplifyFormula(neqA(X, Y), sneqA(Res)) :- simplifyAtom(X, XRes), simplifyAtom(Y, YRes), subtractMap(XRes, YRes, Res).
simplifyFormula(divA(C, X), sdivA(C, XRes)) :- simplifyAtom(X, XRes).
simplifyFormula(ndivA(C, X), sndivA(C, XRes)) :- simplifyAtom(X, XRes).
simplifyFormula(andL(F1, F2), andL(Res1, Res2)) :- simplifyFormula(F1, Res1), simplifyFormula(F2, Res2).
simplifyFormula(orL(F1, F2), orL(Res1, Res2)) :- simplifyFormula(F1, Res1), simplifyFormula(F2, Res2).
simplifyFormula(notL(F), notL(Res)) :- simplifyFormula(F, Res).
simplifyFormula(existsL(X, F), existsL(X, Res)) :- simplifyFormula(F, Res).
simplifyFormula(forallL(X, F), forallL(X, Res)) :- simplifyFormula(F, Res).
simplifyFormula(orList([]), orList([])).
simplifyFormula(orList([FHead | FRest]), orList([ResHead | ResRest])) :-
  simplifyFormula(FHead, ResHead), simplifyFormula(orList(FRest), orList(ResRest)).
simplifyFormula(andList([]), andList([])).
simplifyFormula(andList([FHead | FRest]), andList([ResHead | ResRest])) :-
  simplifyFormula(FHead, ResHead), simplifyFormula(andList(FRest), andList(ResRest)).

% This function tests whether term is quantifier free.
quantifierFree(sltA(_)).
quantifierFree(sleA(_)).
quantifierFree(seqA(_)).
quantifierFree(sneqA(_)).
quantifierFree(sdivA(_)).
quantifierFree(sndivA(_)).
quantifierFree(andL(X, Y)) :- quantifierFree(X), quantifierFree(Y).
quantifierFree(orL(X, Y)) :- quantifierFree(X), quantifierFree(Y).
quantifierFree(orList([])).
quantifierFree(orList([FHead | FRest])) :-
  quantifierFree(FHead), quantifierFree(orList(FRest)).
quantifierFree(andList([])).
quantifierFree(andList([FHead | FRest])) :-
  quantifierFree(FHead), quantifierFree(andList(FRest)).
quantifierFree(notL(X)) :- quantifierFree(X).

% This function converts the formula into not-free.
toNNF(F, Res) :- toNNF(F, 1, Res).
toNNF(sltA(X), 1, sltA(X)).
toNNF(sltA(X), 0, sleA(NX)) :- negateMap(X, NX).
toNNF(sleA(X), 1, sleA(X)).
toNNF(sleA(X), 0, sltA(NX)) :- negateMap(X, NX).
toNNF(seqA(X), 1, seqA(X)).
toNNF(seqA(X), 0, sneqA(X)).
toNNF(sneqA(X), 1, sneqA(X)).
toNNF(sneqA(X), 0, seqA(X)).
toNNF(sdivA(X, Y), 1, sdivA(X, Y)).
toNNF(sdivA(X, Y), 0, sndivA(X, Y)).
toNNF(sndivA(X, Y), 1, sndivA(X, Y)).
toNNF(sndivA(X, Y), 0, sdivA(X, Y)).

toNNF(andL(X, Y), 1, andL(XRes, YRes)) :- toNNF(X, 1, XRes), toNNF(Y, 1, YRes).
toNNF(orL(X, Y), 1, orL(XRes, YRes)) :- toNNF(X, 1, XRes), toNNF(Y, 1, YRes).
toNNF(andL(X, Y), 0, orL(XRes, YRes)) :- toNNF(X, 0, XRes), toNNF(Y, 0, YRes).
toNNF(orL(X, Y), 0, andL(XRes, YRes)) :- toNNF(X, 0, XRes), toNNF(Y, 0, YRes).
toNNF(orList([]), 1, orList([])).
toNNF(orList([FHead | FRest]), 1, orList([ResHead | ResRest])) :-
  toNNF(FHead, 1, ResHead),
  toNNF(orList(FRest), 1, orList(ResRest)).
toNNF(orList([]), 0, andList([])).
toNNF(orList([FHead | FRest]), 0, andList([ResHead | ResRest])) :-
  toNNF(FHead, 0, ResHead),
  toNNF(orList(FRest), 0, andList(ResRest)).
toNNF(andList([]), 1, andList([])).
toNNF(andList([FHead | FRest]), 1, andList([ResHead | ResRest])) :-
  toNNF(FHead, 1, ResHead),
  toNNF(andList(FRest), 1, andList(ResRest)).
toNNF(andList([]), 0, orList([])).
toNNF(andList([FHead | FRest]), 0, orList([ResHead | ResRest])) :-
  toNNF(FHead, 0, ResHead),
  toNNF(andList(FRest), 0, orList(ResRest)).
toNNF(notL(X), 1, XRes) :- toNNF(X, 0, XRes).
toNNF(notL(X), 0, XRes) :- toNNF(X, 1, XRes).

% This function removes NDiv by replacing it with disjunctions of Div.
removeNDiv(C, X, Res) :- Counter is C - 1, removeNDiv(C, X, Counter, Res).
removeNDiv(C, X, 1, orList([andList([sdivA(C, X1)])])) :- addK(X, 1, X1).
removeNDiv(C, X, Counter, orList([andList([sdivA(C, XK)]) | ResRest])) :-
  Counter \= 1,
  NextCounter is Counter - 1,
  addK(X, Counter, XK),
  removeNDiv(C, X, NextCounter, orList(ResRest)).

% Helper function for dnf conversion.
dnfExtend(_, [], []).
dnfExtend(L1, [andList(Or1) | Rest], [andList(LRes) | ResRest]) :-
  dnfExtend(L1, Rest, ResRest), append(L1, Or1, LRes).
dnfCombine([], _, []).
dnfCombine([andList(Or1) | Rest], orList(YDNF), Res) :-
  dnfExtend(Or1, YDNF, Or1Res),
  dnfCombine(Rest, orList(YDNF), RestRes),
  append(Or1Res, RestRes, Res).

% Adds constant K to a sorted map.
addK([], K, [(0, K)]).
addK([(0, N) | Rest], K, [(0, Np1) | Rest]) :- Np1 is N + K, Np1 \= 0.
addK([(0, N) | Rest], K, Rest) :- N + K = 0.
addK([(X, N) | Rest], K, [(0, K) | [(X, N) | Rest]]) :- X \= 0.

% Converts quantifier free NNF formula to DNF.
toDNF(sltA(X), orList([andList([sltA(X)])])).
toDNF(sleA(X), orList([andList([sltA(Xp1)])])) :- addK(X, -1, Xp1).
toDNF(seqA(X), Res) :- toDNF(andL(sleA(X), sleA(X)), Res).
toDNF(sneqA(X), Res) :- toDNF(orL(sltA(X), sltA(X)), Res).
toDNF(sdivA(C, X), orList([andList([sdivA(C, X)])])).
toDNF(sndivA(C, X), Res) :- removeNDiv(C, X, Res).
toDNF(orL(X, Y), orList(Res)) :- toDNF(X, orList(XDNF)), toDNF(Y, orList(YDNF)), append(XDNF, YDNF, Res).
toDNF(andL(X, Y), orList(Res)) :- toDNF(X, orList(XDNF)), toDNF(Y, orList(YDNF)), dnfCombine(XDNF, YDNF, Res).
toDNF(orList([]), orList([])).
toDNF(andList([]), orList([andList([])])).
toDNF(orList([FHead | FRest]), orList(Res)) :-
  toDNF(FHead, orList(ResHead)),
  toDNF(orList(FRest), orList(ResRest)),
  append(ResHead, ResRest, Res).
toDNF(andList([FHead | FRest]), orList(Res)) :-
  toDNF(FHead, orList(ResHead)),
  toDNF(orLIst(FRest), orList(ResRest)),
  dnfCombine(ResHead, ResRest, Res).

% Helper function for splitting DNF whether it contains a variable.
containsSimple(N, [(N, _) | _]).
containsSimple(N, [_ | Rest]) :- containsSimple(N, Rest).
contains(N, sltA(X)) :- containsSimple(N, X).
contains(N, sdivA(_, X)) :- containsSimple(N, X).

% Splits list to whether it contains X.
splitList([], _, [], []).
splitList([Head | Rest], X, [Head | Rest1], Rest0) :- contains(X, Head), splitList(Rest, X, Rest1, Rest0).
splitList([Head | Rest], X, Rest1, [Head | Rest0]) :- \+contains(X, Head), splitList(Rest, X, Rest1, Rest0).

% Splits dnf into whether it contains X.
splitDNF(orList([]), _, orList([])).
splitDNF(orList([andList(Head) | Rest]), X, orList([andList([andList(Res1), andList(Res0)]) | RestRes])) :-
  splitList(Head, X, Res1, Res0), splitDNF(orList(Rest), X, orList(RestRes)).

negCoeff(N, [(N, NVal) | _]) :- NVal @< 0.
negCoeff(N, [(M, _) | Rest]) :-
  N \= M,
  negCoeff(N, Rest).

% Splits dnf into Lt, Gt, Div.
classifyContain(andList([]), _, andList([]), andList([]), andList([])).
classifyContain(andList([sdivA(C, X) | Rest]), N, andList(LtRest), andList(GtRest), andList([sdivA(C, X) | DivRest])) :-
  classifyContain(andList(Rest), N, andList(LtRest), andList(GtRest), andList(DivRest)).
classifyContain(andList([sltA(X) | Rest]), N, andList([(sltA(X)) | LtRest]), andList(GtRest), andList(DivRest)) :-
  classifyContain(andList(Rest), N, andList(LtRest), andList(GtRest), andList(DivRest)),
  \+ negCoeff(N, X).
classifyContain(andList([sltA(X) | Rest]), N, andList(LtRest), andList([sltA(X) | GtRest]), andList(DivRest)) :-
  classifyContain(andList(Rest), N, andList(LtRest), andList(GtRest), andList(DivRest)),
  negCoeff(N, X).

classifyDNF(orList([]), _, orList([])).
classifyDNF(orList([andList([RT, RF]) | Rest]), N, orList([andList([andList([LtRest, GtRest, DivRest]), RF]) | ResRest])) :-
  classifyDNF(orList(Rest), N, orList(ResRest)),
  classifyContain(RT, N, LtRest, GtRest, DivRest).

% Functions computing gcd.
lcm([], 1).
lcm([Head | Rest], Res) :- lcm(Rest, ResRest), lcm(Head, ResRest, Res).
gcd(X, X, X).
gcd(X, Y, G) :-
  X @< Y,
  Sub is Y - X,
  gcd(X, Sub, G).
gcd(X, Y, G) :-
  Y @< X,
  Sub is X - Y,
  gcd(Sub, Y, G).
lcm(X, Y, L) :-
  gcd(X, Y, G),
  XY is X * Y,
  L is XY // G.

% Get coefficient of X in the sorted map.
getConstant([(X, N) | _], X, N).
getAbsConstant([(Y, _) | Rest], X, Res) :- X \= Y, getAbsConstant(Rest, X, Res).
getAbsConstant(A, X, NAbs) :-
  getConstant(A, X, N),
  abs(N, NAbs).
getLeftLCM([], _, 1).
getLeftLCM([sltA(A) | Rest], X, Res) :-
  getLeftLCM(Rest, X, ResRest),
  getAbsConstant(A, X, ResHead),
  lcm(ResRest, ResHead, Res).
getDivLCM([], _, 1).
getDivLCM([sdivA(_, XHead) | Rest], X, Res) :-
  getDivLCM(Rest, X, ResRest),
  getAbsConstant(XHead, X, ResHead),
  lcm(ResRest, ResHead, Res).

% Compute lcm of all coefficient.
computeMultiplier(andList(LtClauses), andList(GtClauses), andList(DivClauses), N, Res) :-
  getLeftLCM(LtClauses, N, LtRes),
  getLeftLCM(GtClauses, N, RtRes),
  getDivLCM(DivClauses, N, DivRes),
  lcm(LtRes, RtRes, Res1),
  lcm(Res1, DivRes, Res).

% Adjust formula so that coefficient of N is 1, by multiplying.
updateLtAtom([], _, _, []).
updateLtAtom([(N, K) | Rest], Multiplier, N, [(N, 1) | ResRest]) :-
  0 @< K,
  updateLtAtom(Rest, Multiplier, N, ResRest).
updateLtAtom([(N, K) | Rest], Multiplier, N, [(N, -1) | ResRest]) :-
  K @< 0,
  updateLtAtom(Rest, Multiplier, N, ResRest).
updateLtAtom([(M, MCount) | Rest], Multiplier, N, [(M, CountRes) | ResRest]) :-
  M \= N,
  updateLtAtom(Rest, Multiplier, N, ResRest),
  CountRes is MCount * Multiplier.

updateDivAtom([], _, _, []).
updateDivAtom([(N, _) | Rest], Multiplier, N, [(N, 1) | ResRest]) :-
  updateDivAtom(Rest, Multiplier, N, ResRest).
updateDivAtom([(M, MCount) | Rest], Multiplier, N, [(M, CountRes) | ResRest]) :-
  M \= N,
  updateDivAtom(Rest, Multiplier, N, ResRest),
  CountRes is MCount * Multiplier.

updateLt(sltA(X), Multiplier, N, sltA(Res)) :-
  getAbsConstant(X, N, Constant),
  MultiplierDiv is Multiplier // Constant,
  updateLtAtom(X, MultiplierDiv, N, Res).

updateLts([], _, _, []).
updateLts([Head | Rest], Multiplier, N, [ResHead | ResRest]) :-
  updateLt(Head, Multiplier, N, ResHead),
  updateLts(Rest, Multiplier, N, ResRest).

updateDiv(sdivA(C, X), Multiplier, Constant, N, sdivA(CAbs, Res)) :-
  getConstant(X, N, Constant),
  MultiplierDiv is Multiplier // Constant,
  updateDivAtom(X, MultiplierDiv, N, Res),
  CRes is C * MultiplierDiv,
  abs(CRes, CAbs).

updateDivs([], _, _, []).
updateDivs([Head | Rest], Multiplier, N, [ResHead | ResRest]) :-
  updateDiv(Head, Multiplier, N, ResHead),
  updateDivs(Rest, Multiplier, N, ResRest).

% With helper functions, rewrite formula so that coefficient of x is 1.
equivalentForm(andList(LtLefts), andList(LtRights), andList(Divs), N,
               andList(LtLeftRes), andList(LtRightRes), andList([sdivA(Multiplier, [(N, 1)]) | DivRes])) :-
  computeMultiplier(andList(LtLefts), andList(LtRights), andList(Divs), N, Multiplier),
  updateLts(LtLefts, Multiplier, N, LtLeftRes),
  updateLts(LtRights, Multiplier, N, LtRightRes),
  updateDivs(Divs, Multiplier, N, DivRes).

% Compute the constant which is lcm of b, divisors of sdivA
computeDisjunctionConstant([], _, Multiplier, Multiplier).
computeDisjunctionConstant([sdivA(C, F) | Rest], X, Multiplier, Res) :-
  getAbsConstant(F, X, N),
  abs(N, NAbs),
  ResF is (Multiplier * C) // NAbs,
  computeDisjunctionConstant(Rest, X, Multiplier, ResRest),
  lcm(ResF, ResRest, Res).

% Remove X and return N * its coeff
substituteAtom([], _, _, [], 0).
substituteAtom([(Y, YVal) | Rest], X, N, [(Y, YVal) | ResRest], ResVal) :-
  X \= Y,
  substituteAtom(Rest, X, N, ResRest, ResVal).
substituteAtom([(X, XVal) | Rest], X, N, Rest, ResVal) :-
  ResVal is XVal * N.

% Substitute X with N
substituteAtom([(0, C) | Rest], X, N, [(0, Res) | ResRest]) :-
  substituteAtom(Rest, X, N, ResRest, ResVal),
  Res is C + ResVal,
  Res \= 0.
substituteAtom([(0, C) | Rest], X, N, ResRest) :-
  substituteAtom(Rest, X, N, ResRest, ResVal),
  C + ResVal = 0.
substituteAtom([(K, C) | Rest], X, N, [(0, ResVal) | ResRest]) :-
  K \= 0,
  substituteAtom([(K, C) | Rest], X, N, ResRest, ResVal),
  ResVal \= 0.
substituteAtom([(K, C) | Rest], X, N, ResRest) :-
  K \= 0,
  substituteAtom([(K, C) | Rest], X, N, ResRest, 0).

% Substitute X with N in Slt / SDiv
substituteForm(sltA(F), X, N, sltA(R)) :-
  substituteAtom(F, X, N, R).

substituteForm(sdivA(C, F), X, N, sdivA(C, R)) :-
  substituteAtom(F, X, N, R).

substituteList([], _, _, []).
substituteList([F | Rest], X, N, [R | ResRest]) :-
  substituteList(Rest, X, N, ResRest),
  substituteForm(F, X, N, R).

% [F[X/Curr-1], ..., F[X/Under]]
loopSubstitute(_, _, _, _, Under, Under, orList([])).
loopSubstitute(andList(Lts), andList(Rts), andList(Divs), X, Under, Curr,
               orList([andList([andList(LtRes), andList(RtRes), andList(DivRes)]) | Rest])) :-
  Curr \= Under,
  NextCurr is Curr - 1,
  loopSubstitute(andList(Lts), andList(Rts), andList(Divs), X, Under, NextCurr, orList(Rest)),
  substituteList(Lts, X, NextCurr, LtRes),
  substituteList(Rts, X, NextCurr, RtRes),
  substituteList(Divs, X, NextCurr, DivRes).

removeVar([], _, [], 0).
removeVar([(X, K) | Rest], X, Rest, K).
removeVar([(Y, YVal) | Rest], X, [(Y, YVal) | ResRest], K) :-
  X \= Y,
  removeVar(Rest, X, ResRest, K).

substituteLtForm([], _, _, []).
substituteLtForm([sltA(A) | Rest], X, F, [sltA(ARes) | ResRest]) :-
  removeVar(A, X, ARemoved, 1),
  mergeMap(ARemoved, F, ARes),
  substituteLtForm(Rest, X, F, ResRest).

substituteGtForm([], _, _, []).
substituteGtForm([sltA(A) | Rest], X, F, [sltA(ARes) | ResRest]) :-
  removeVar(A, X, ARemoved, -1),
  negateMap(F, FNeg),
  mergeMap(ARemoved, FNeg, ARes),
  substituteLtForm(Rest, X, F, ResRest).

substituteDivForm([], _, _, []).
substituteDivForm([sdivA(C, A) | Rest], X, F, [sdivA(C, ARes) | ResRest]) :-
  removeVar(A, X, ARemoved, 1),
  mergeMap(ARemoved, F, ARes),
  substituteLtForm(Rest, X, F, ResRest).
substituteDivForm([sdivA(C, A) | Rest], X, F, [sdivA(C, ARes) | ResRest]) :-
  removeVar(A, X, ARemoved, -1),
  negateMap(F, FNeg),
  mergeMap(ARemoved, FNeg, ARes),
  substituteLtForm(Rest, X, F, ResRest).

% Replace X to F + (under, ..., curr) to list
substituteListLtForm(andList(Lts), andList(Gts), andList(Divs), X, F, Under, Under,
                     orList([andList([andList(LtRes), andList(GtRes), andList(DivRes)])])) :-
  addK(F, Under, FAdded),
  substituteLtForm(Lts, X, FAdded, LtRes),
  substituteGtForm(Gts, X, FAdded, GtRes),
  substituteDivForm(Divs, X, FAdded, DivRes).

substituteListLtForm(andList(Lts), andList(Gts), andList(Divs), X, F, Under, Curr,
                     orList([andList([andList(LtRes), andList(GtRes), andList(DivRes)]) | ResRest])) :-
  Curr \= Under,
  addK(F, Curr, FAdded),
  substituteLtForm(Lts, X, FAdded, LtRes),
  substituteGtForm(Gts, X, FAdded, GtRes),
  substituteDivForm(Divs, X, FAdded, DivRes),
  NextCurr is Curr - 1,
  substituteListLtForm(andList(Lts), andList(Gts), andList(Divs), X, F, Under, NextCurr, orList(ResRest)).

removeX(sltA([(X, -1) | Rest]), X, Rest).
removeX(sltA([(Y, YVal) | Rest]), X, [(Y, YVal) | ResRest]) :-
  X \= Y,
  removeX(sltA(Rest), X, ResRest).

substituteListFormLoop(Lts, Gts, Divs, X, [F], LoopCounter, Res) :-
  removeX(F, X, FRes),
  substituteListLtForm(Lts, Gts, Divs, X, FRes, 1, LoopCounter, Res).
substituteListFormLoop(Lts, Gts, Divs, X, [FHead | [FHead2 | FRest2]], Counter, orList([orList(ResHead) | ResRest])) :-
  removeX(FHead, X, FRes),
  substituteListLtForm(Lts, Gts, Divs, X, FRes, 1, Counter, orList(ResHead)),
  substituteListFormLoop(Lts, Gts, Divs, X, [FHead2 | FRest2], Counter, orList(ResRest)).

equivalentWithoutQuantifier(Lts, andList([]), andList(Divs), X, Multiplier, Res) :-
  computeDisjunctionConstant(Divs, X, Multiplier, Counter),
  loopSubstitute(Lts, andList([]), andList(Divs), X, 0, Counter, Res).

equivalentWithoutQuantifier(Lts, andList([GtHead | GtRest]), andList(Divs), X, Multiplier, Res) :-
  computeDisjunctionConstant(Divs, X, Multiplier, Counter),
  LoopCounter is Counter - 1,
  substituteListFormLoop(Lts, andList([GtHead | GtRest]), andList(Divs), X, [GtHead | GtRest], LoopCounter, Res).

equivWOQuantList(orList([]), _, orList([])).
equivWOQuantList(orList([andList([andList([Lts, Gts, Divs]), Nots]) | ConjRest]), X, orList([andList([Res, Nots]) | ResRest])) :-
  computeMultiplier(Lts, Gts, Divs, X, Multiplier),
  equivalentForm(Lts, Gts, Divs, X, LtEq, GtEq, DivEq),
  equivalentWithoutQuantifier(LtEq, GtEq, DivEq, X, Multiplier, Res),
  equivWOQuantList(orList(ConjRest), X, orList(ResRest)).

eliminateQuantifier(F, X, Res) :-
  quantifierFree(F),
  toNNF(F, NNF),
  toDNF(NNF, DNF),
  splitDNF(DNF, X, Splitted),
  classifyDNF(Splitted, X, Classified),
  equivWOQuantList(Classified, X, Res).

toQuantifierFree(andL(F1, F2), andL(R1, R2)) :-
  toQuantifierFree(F1, R1),
  toQuantifierFree(F2, R2).
toQuantifierFree(orL(F1, F2), orL(R1, R2)) :-
  toQuantifierFree(F1, R1),
  toQuantifierFree(F2, R2).
toQuantifierFree(notL(F), notL(R)) :-
  toQuantifierFree(F, R).
toQuantifierFree(existsL(X, F), R) :-
  eliminateQuantifier(F, X, R).
toQuantifierFree(existsL(X, F), Res) :-
  \+ quantifierFree(F),
  toQuantifierFree(F, R),
  removeRedundanct(R, RR),
  eliminateQuantifier(RR, X, Res).
toQuantifierFree(forallL(X, F), notL(R)) :-
  eliminateQuantifier(notL(F), X, R).
toQuantifierFree(forallL(X, F), notL(Res)) :-
  \+ quantifierFree(F),
  toQuantifierFree(F, R),
  removeRedundancy(R, RR),
  eliminateQuantifier(notL(RR), X, Res).
toQuantifierFree(orList([]), orList([])).
toQuantifierFree(orList([Head | Rest]), orList([ResHead | ResRest])) :-
  toQuantifierFree(Head, ResHead),
  toQuantifierFree(orList(Rest), orList(ResRest)).
toQuantifierFree(andList([]), andList([])).
toQuantifierFree(andList([Head | Rest]), andList([ResHead | ResRest])) :-
  toQuantifierFree(Head, ResHead),
  toQuantifierFree(andList(Rest), andList(ResRest)).

containedList(X, [X | _]).
containedList(X, [Y | Rest]) :-
  X \= Y,
  containedList(X, Rest).

isClosed(F) :- isClosed(F, []).
isClosed([], _).
isClosed([(0, _) | Rest], State) :- isClosed(Rest, State).
isClosed([(N, _) | Rest], State) :-
  containedList(N, State),
  isClosed(Rest, State).
isClosed(sltA(A), State) :- isClosed(A, State).
isClosed(sleA(A), State) :- isClosed(A, State).
isClosed(seqA(A), State) :- isClosed(A, State).
isClosed(sneqA(A), State) :- isClosed(A, State).
isClosed(sdivA(_, A), State) :- isClosed(A, State).
isClosed(sndivA(_, A), State) :- isClosed(A, State).
isClosed(andL(F1, F2), State) :-
  isClosed(F1, State),
  isClosed(F2, State).
isClosed(orL(F1, F2), State) :-
  isClosed(F1, State),
  isClosed(F2, State).
isClosed(orList([]), _).
isClosed(andList([]), _).
isClosed(orList([Head | Rest]), State) :-
  isClosed(Head, State),
  isClosed(orList(Rest), State).
isClosed(andList([Head | Rest]), State) :-
  isClosed(Head, State),
  isClosed(andList(Rest), State).
isClosed(notL(F), State) :- isClosed(F, State).
isClosed(existsL(X, F), State) :-
  isClosed(F, [X | State]).
isClosed(forallL(X, F), State) :-
  isClosed(F, [X | State]).

decideClosedQuantifierFree(sltA([(0, N)]), 1) :-
  N @< 0.
decideClosedQuantifierFree(sltA([(0, N)]), 0) :-
  0 @=< N.
decideClosedQuantifierFree(sltA([]), 0).
decideClosedQuantifierFree(sleA([(0, N)]), 1) :-
  N @=< 0.
decideClosedQuantifierFree(sleA([(0, N)]), 0) :-
  0 @< N.
decideClosedQuantifierFree(sleA([]), 1).
decideClosedQuantifierFree(seqA([(0, N)]), 1) :-
  N =:= 0.
decideClosedQuantifierFree(seqA([(0, N)]), 0) :-
  N =\= 0.
decideClosedQuantifierFree(seqA([]), 1).
decideClosedQuantifierFree(sneqA([(0, N)]), 1) :-
  N =\= 0.
decideClosedQuantifierFree(sneqA([(0, N)]), 0) :-
  N =:= 0.
decideClosedQuantifierFree(sneqA([]), 0).
decideClosedQuantifierFree(sdivA(C, [(0, N)]), 1) :-
  rem(N, C) =:= 0.
decideClosedQuantifierFree(sdivA(C, [(0, N)]), 0) :-
  rem(N, C) =\= 0.
decideClosedQuantifierFree(sdivA(_, []), 1).
decideClosedQuantifierFree(sndivA(C, [(0, N)]), 1) :-
  rem(N, C) =\= 0.
decideClosedQuantifierFree(sndivA(C, [(0, N)]), 0) :-
  rem(N, C) =:= 0.
decideClosedQuantifierFree(sndivA(_, []), 0).
decideClosedQuantifierFree(andL(F1, F2), TF) :-
  decideClosedQuantifierFree(F1, TF1),
  decideClosedQuantifierFree(F2, TF2),
  TF is TF1 * TF2.
decideClosedQuantifierFree(orL(F1, F2), TF) :-
  decideClosedQuantifierFree(F1, TF1),
  decideClosedQuantifierFree(F2, TF2),
  TF is TF1 + TF2.
decideClosedQuantifierFree(andList([]), 1).
decideClosedQuantifierFree(orList([]), 0).
decideClosedQuantifierFree(orList([Head | Rest]), TF) :-
  decideClosedQuantifierFree(Head, TF1),
  decideClosedQuantifierFree(orList(Rest), TF2),
  TF is TF1 + TF2.
decideClosedQuantifierFree(andList([Head | Rest]), TF) :-
  decideClosedQuantifierFree(Head, TF1),
  decideClosedQuantifierFree(andList(Rest), TF2),
  TF is TF1 * TF2.
decideClosedQuantifierFree(notL(F), NTF) :-
  decideClosedQuantifierFree(F, TF),
  sign(TF, STF), abs(STF, ATF), NTF is 1 - ATF.

decide(F, Res) :-
  isClosed(F),
  toQuantifierFree(F, R),
  decideClosedQuantifierFree(R, Res).

isTrue(andList([])).
isFalse(orList([])).

containsTrue([orList([]) | _]).
containsTrue([Head | Rest]) :-
  Head \= orList([]),
  containsTrue(Rest).
containsFalse([andList([]) | _]).
containsFalse([Head | Rest]) :-
  Head \= andList([]),
  containsFalse(Rest).

filterTrue([], []).
filterTrue([andList([]) | Rest], ResRest) :-
  filterTrue(Rest, ResRest).
filterTrue([Head | Rest], [Head | ResRest]) :-
  Head \= andList([]),
  filterTrue(Rest, ResRest).

filterFalse([], []).
filterFalse([orList([]) | Rest], ResRest) :-
  filterFalse(Rest, ResRest).
filterFalse([Head | Rest], [Head | ResRest]) :-
  Head \= orList([]),
  filterFalse(Rest, ResRest).

% andList([]) and orList([]) is not required, so we will...delete does.
removeRedundancy(sltA(A), sltA(A)).
removeRedundancy(sleA(A), sleA(A)).
removeRedundancy(seqA(A), seqA(A)).
removeRedundancy(sneqA(A), sneqA(A)).
removeRedundancy(sdivA(C, A), sdivA(C, A)).
removeRedundancy(sndivA(C, A), sndivA(C, A)).
removeRedundancy(andL(F1, F2), Res) :-
  removeRedundancy(F1, R1),
  removeRedundancy(F2, R2),
  ({isFalse(R1) ; isFalse(R2)} ->
    Res is orList([]) ;
    (isTrue(R1) ->
      Res is R2;
      (isTrue(R2) ->
        Res is R1;
        Res is andL(R1, R2)
        )
      )
    ).
removeRedundancy(orL(F1, F2), Res) :-
  removeRedundancy(F1, R1),
  removeRedundancy(F2, R2),
  ({isTrue(R1) ; isTrue(R2)} ->
    Res is andList([]) ;
    (isFalse(R1) ->
      Res is R2;
      (isFalse(R2) ->
        Res is R1;
        Res is orL(R1, R2)
        )
      )
    ).
removeRedundancy(andList(List), Res) :-
  removeRedundancyList(List, ResList),
  (containsFalse(ResList) ->
    Res is orList([]);
    Res is filterTrue(ResList)
    ).
removeRedundancy(orList(List), Res) :-
  removeRedundancyList(List, ResList),
  (containsTrue(ResList) ->
    Res is andList([]);
    Res is filterFalse(ResList)
    ).
removeRedundancy(notL(F), andList([])) :-
  removeRedundancy(F, orList([])).
removeRedundancy(notL(F), orList([])) :-
  removeRedundancy(F, andList([])).
removeRedundancy(notL(F), notL(R)) :-
  removeRedundancy(F, R),
  \+isTrue(R), \+isFalse(R).
removeRedundancy(forallL(_, F), andList([])) :-
  removeRedundancy(F, andList([])).
removeRedundancy(forallL(_, F), orList([])) :-
  removeRedundancy(F, orList([])).
removeRedundancy(forallL(X, F), forallL(X, R)) :-
  removeRedundancy(F, R),
  \+isTrue(R), \+isFalse(R).
removeRedundancy(existsL(_, F), andList([])) :-
  removeRedundancy(F, andList([])).
removeRedundancy(existsL(_, F), orList([])) :-
  removeRedundancy(F, orList([])).
removeRedundancy(existsL(X, F), existsL(X, R)) :-
  removeRedundancy(F, R),
  \+isTrue(R), \+isFalse(R).

removeRedundancyList([], []).
removeRedundancyList([Head | Rest], [ResHead | ResRest]) :-
  removeRedundancy(Head, ResHead),
  removeRedundancyList(Rest, ResRest).
