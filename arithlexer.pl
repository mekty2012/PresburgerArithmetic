% nat -> 0-9 nat
sentence(forallL(var(N), F)) --> quantifier(forall, var(N)), sentence(F).
sentence(existsL(var(N), F)) --> quantifier(exists, var(N)), sentence(F).
sentence(F) --> formula(F).
quantifier(forall, var(N)) --> [for], [all], varLex(N).
quantifier(exists, var(N)) --> [there], [exists], varLex(N), [that].
formula(andL(L, F)) --> literal(L), [and], formula(F).
formula(orL(L, F)) --> literal(L), [or], formula(F).
formula(F) --> literal(F).
literal(neqA(A1, A2)) --> atom(A1), [is], [not], atom(A2).
literal(eqA(A1, A2)) --> atom(A1), [is], atom(A2).
literal(ltA(A1, A2)) --> atom(A1), [is], [less], [than], atom(A2).
literal(ltA(A2, A1)) --> atom(A1), [is], [larger], [than], atom(A2).
atom(varA(N)) --> varLex(N).
atom(natA(N)) --> natLex(N).
atom(addA(var(N), F)) --> varLex(N), [+], atom(F).
atom(addA(nat(N), F)) --> natLex(N), [+], atom(F).

natLex(N) --> [N], {integer(N), N > -1}.

varLex(1) --> [a].
varLex(2) --> [b].
varLex(3) --> [c].
varLex(4) --> [d].
varLex(5) --> [e].
varLex(6) --> [f].
varLex(7) --> [g].
varLex(8) --> [h].
varLex(9) --> [i].
varLex(10) --> [j].
varLex(11) --> [k].
varLex(12) --> [l].
varLex(13) --> [m].
varLex(14) --> [n].
varLex(15) --> [o].
varLex(16) --> [p].
varLex(17) --> [q].
varLex(18) --> [r].
varLex(19) --> [s].
varLex(20) --> [t].
varLex(21) --> [u].
varLex(22) --> [v].
varLex(23) --> [w].
varLex(24) --> [x].
varLex(25) --> [y].
varLex(26) --> [z].
