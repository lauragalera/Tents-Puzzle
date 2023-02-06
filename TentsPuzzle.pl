%%%%%%%%%%% PRÀCTICA PROLOG TENDES %%%%%%%%%%%
% Autors: Laura Galera i Aleix Fernández

%%%%%%%%%% RESOL %%%%%%%%%%
% resol(+N,+LA,+LF,+LC) => mostra la solució al problema de tendes amb quadricula NxN, LA les posicions dels arbres, LF les tendes per fila i LC les tendes per columna
resol(N,LA,LF,LC):-codifica(N,LA,LF,LC,CNF),sat(CNF,[],M),mostra(N,LA,LF,LC,M).

%%%% PREDICATS PEL SAT SOLVER %%%%

% sat(F,I,M) => donada una fórmula F en CNF i una interpretació I, es satisfà quan M sigui un model de F construit extenent I
sat([],I,I):- write('SAT:'), write(I),nl,nl,!.
sat(CNF,I,M):-tria(CNF,L),simplif(L,CNF,CNFS),append(I,[L],IR),sat(CNFS,IR,M).
sat(CNF,I,M):-tria(CNF,L),N is -L,simplif(N,CNF,CNFS),append(I,[N],IR),sat(CNFS,IR,M).

% tria(CNF,Lit) => Lit és el primer literal d'una clàsula unitària de CNF, un literal qualsevol de la CNF si no n'hi ha cap
tria(CNF,Lit):- append(_,[[Lit]|_],CNF),!.
tria(CNF,Lit):-append(_,[[Lit|_]|_],CNF),!.

% simplif(+Lit,CNF,CNFS) => CNFS és la CNF sense les clàusules amb el literal Lit i sense el literal -Lit
simplif(_,[],[]).
simplif(X,[Y|YS],REC):-append(_,[X|_],Y),!,simplif(X,YS,REC).
simplif(X,[[E]|_],_):-E is -X, !,fail.
simplif(X,[Y|YS],[Z|REC]):-append(L,[E|ES],Y),E is -X,!,append(L,ES,Z),simplif(X,YS,REC).
simplif(X,[Y|YS],[Y|REC]):-simplif(X,YS,REC).

%%%% PREDICATS PER A LA CODIFICACIÓ %%%%

% codifica(+N,+LA,+LF,+LC,CNF) => CNF és la concatenació de CNFs resultants de cada restricció del problema per un puzle NxN, amb arbres a les posicions LA i tantes tendes requerides per fila i columna com marca LF i LC
codifica(N,LA,LF,LC,CNF):-generarmatriu(1,N,N,M),veins(M,N,LA,CNF1),tendesfilacolumna(M,LF,LC,CNF2),noveins(M,N,CNF3),noarbres(LA,M,CNF4),
                          append(CNF1,CNF2,L1),append(L1,CNF3,L2),append(L2,CNF4,CNF).

%%%% generarmatriu 

% generarmatriu(+F,+N1,+N2,M):- M és la matriu d'enters de mida N1xN2 amb la primera casella a F i la resta incrementada una unitat respecte la casella de l'esquerra
generarmatriu(_,0,_,[]):-!.
generarmatriu(F,I,N,[X|M]):- N2 is F+N-1, generarfila(F,N2,X), F2 is N2+1, I2 is I-1, generarmatriu(F2,I2,N,M).

% generarfila(+F,+N,M) :- M és la llista de números des de F fins N
generarfila(N,N,[N]):-!.
generarfila(F,N,[F|M]):-F < N, F2 is F+1, generarfila(F2,N,M).

%%%% veins

% veins(LLV,+N,+LA,CNF) => CNF es satisfà quan tots els arbres de LA tenen almenys una variable certa al costat
veins(_,_,[],[]).
veins(M,N,[A|LA],CNF):-veinselem(M,N,A,L),unCert(L,CNF1),veins(M,N,LA,CNF2),append(CNF1,CNF2,CNF).

% veinselem(M,+N,+A,L) => L són les variables veines de l'arbre A de la matriu M de mida N
veinselem(M,N,(F,C),L):-F1 is F-1, F2 is F+1, C1 is C-1, C2 is C+1,
                    trobarelem((F1,C),M,N,E1), trobarelem((F,C1),M,N,E2), trobarelem((F,C2),M,N,E3), trobarelem((F2,C),M,N,E4),
                    append(E1,E2,L1),append(L1,E3,L2),append(L2,E4,L).

% trobarelem(+P,M,+N,E) => E és una llista amb l'element de la matriu M de mida N a la posició P. Si P està fora la llista E és buida
trobarelem((F,C),M,N,[E]):- F>0,C>0,F=<N,C=<N,!,elem(M,F,E2),elem(E2,C,E).
trobarelem(_,_,_,[]).

% elem(L,+N,E) => E és l'element de L a la posició N
elem([X|_],1,X):-!.
elem([_|XS],Y,R):-Y1 is Y-1,elem(XS,Y1,R).

% unCert(Xs,CNF) => CNF satisfà quan almenys 1 variable de Xs és certa
unCert(X,CNF):-atleastK(X,1,CNF).

% atleastK(Xs,+K,CNF) => CNF satisfactible quan K variables de Xs són certes
atleastK(Xs,K,CNF):-allargada(Xs,N), Np is N-K+1, Np > 0, findall(C, comb(Np,Xs,C),CNF).

% comb(+N,X,Comb) => Comb es un subset del set X. L'ordre es irrellevant
comb(0,_,[]).
comb(N,[X|T],[X|Comb]):-N>0,N1 is N-1,comb(N1,T,Comb).
comb(N,[_|T],Comb):-N>0,comb(N,T,Comb).

% allargada(L,+N) => N es l'allargada de L.
allargada([],0).
allargada([_|Xs],N):-allargada(Xs,Np), N is Np+1.

%%%% tendesfilacolumna

% tendesfilacolumna(M,+LF,+LC,CNF) => CNF satisfactible quan cada fila de M té Xi literals certs i cada columna té Xj literals certs, essent Xi el valor i de LF, Xj el valor j de LC.
tendesfilacolumna(M,LF,LC,CNF):-tendesfila(M,LF,CNF1),transpose(M,T),tendesfila(T,LC,CNF2), append(CNF1,CNF2,CNF).

% transpose(M,T) => T és la matriu M transposada
transpose([[]|_], []).
transpose(Matrix, [Row|Rows]) :- transpose_1st_col(Matrix, Row, RestMatrix),
                                 transpose(RestMatrix, Rows).
% transpose_1st_col(M,R,T) => R és la primera columna de M i T és M sense la columna R
transpose_1st_col([], [], []).
transpose_1st_col([[H|T]|Rows], [H|Hs], [T|Ts]) :- transpose_1st_col(Rows, Hs, Ts).

% tendesfila(M,+L,CNF) => CNF satisfactible quan cada fila de M té Xi literals certs, essent Xi el valor i de L
tendesfila([],[],[]).
tendesfila([F|M],[N|NS],CNF):-exactlyK(F,N,CNF1),tendesfila(M,NS,CNF2),append(CNF1,CNF2,CNF).

% exactlyK(L,+K,CNF) => CNF satisfactible quan té exactament K literals de L certs
exactlyK(L,K,CNF):- atleastK(L,K,CNF1), atmostK(L,K,CNF2), append(CNF1,CNF2,CNF).

% atmostK(Xs,+K,CNF) => CNF satisfactible quan té com a molt K literals de Xs certs
atmostK(Xs,K,CNF):- Np is K+1, Np > 0, findall(CN, (comb(Np,Xs,C), negate(C,CN)), CNF).

% negate(+X,Y) => Y és una llista amb tots els elements de X negats
negate([],[]).
negate([X|Xs],[Y|Ys]):- Y is -X, negate(Xs,Ys).

%%%% noveins

% noveins(LLV,N,CNF) => CNF es satisfà quan a la matriu LLV de mida N no hi ha dues variables certes que es toquin
noveins([],_,[]).
noveins([X|XS],N,CNF):- tractarfila([X|XS],1,N,CNF1), noveins(XS,N,CNF2), append(CNF1,CNF2,CNF).

% tractarfila(LLV,+Y,N,CNF) => CNF es satisfà quan les variables certes de la primera fila de LLV a partir de la posició Y no tenen cap variable certa al costat
tractarfila([_],N,N,[]):-!.
tractarfila([X],Y,N,[[E1,E2]|CNF]):-nelem(X,Y,E1),Y2 is Y+1,nelem(X,Y2,E2), tractarfila([X],Y2,N,CNF).
tractarfila([X,Y|XS],1,N,[[E1,E2],[E1,E3],[E1,E4]|CNF]):-!,nelem(X,1,E1), nelem(X,2,E2), nelem(Y,1,E3),
                                                           nelem(Y,2,E4), tractarfila([X,Y|XS],2,N,CNF).
tractarfila([X,Y|_],N,N,[[E1,E2],[E1,E3]]):-!,nelem(X,N,E1), nelem(Y,N,E2), N2 is N-1, nelem(Y,N2,E3).
tractarfila([X,Y|XS],Z,N,[[E1,E2],[E1,E3],[E1,E4],[E1,E5]|CNF]):-nelem(X,Z,E1), Z2 is Z+1, nelem(X,Z2,E2), nelem(Y,Z,E3),
                                                                 nelem(Y,Z2,E4), Z3 is Z-1, nelem(Y,Z3,E5), tractarfila([X,Y|XS],Z2,N,CNF).
% nelem(L,+N,NE) => NE és l'element de L a la posició N negat
nelem(L,N,NE):-elem(L,N,E),NE is -E.

%%%% noarbres

% noarbres(+LA,M,CNF) => CNF es satisfà quan els literals de les posicions de LA de la matriu M són falsos
noarbres([],_,[]).
noarbres([(F,C)|L],M,[[X]|CNF]):-elem(M,F,E),nelem(E,C,X),noarbres(L,M,CNF).

%%%% PREDICATS PER MOSTRAR RESULTAT %%%%

% mostra(+N,LA,LF,LC,M) => mostra el tauler de mida N amb els arbres LA i les tendes LF, LC, siguent M el seu model
mostra(N,LA,LF,LC,M):-write('  '),mostra_LC(LC),write(' '),G is N*2+1,mostra_guions(G),mostra_files(1,N,LA,LF,M).

% mostra_LC(LC) => mostra la llista LC amb un espai en blanc entre tots els elements
mostra_LC([LC]):-!,write(LC),nl.
mostra_LC([LC|LCS]):-write(LC),write(' '),mostra_LC(LCS).

% mostra_guions(+N) => mostra N guions
mostra_guions(0):-!,nl.
mostra_guions(N):-write('-'),M is N-1,mostra_guions(M).

% mostra_files(+F,+N,LA,LF,M) => mostra la fila F i les següent de la matiu de mida N segons els arbres LA i el model M
mostra_files(F,N,_,_,_):-F>N,!.
mostra_files(Fila,N,LA,[LF|LFS],M):-write(LF),write('|'),mostra_caselles(Fila,1,N,LA,M),write(' '),G is N*2+1,mostra_guions(G),
                                    FR is Fila+1,mostra_files(FR,N,LA,LFS,M).

% mostra_caselles(+F,+C,+N,LA,M) => mostra les caselles de la fila F a partir de la C en una matriu de mida N segons els arbres LA i el model M
mostra_caselles(_,C,N,_,_):-C>N,!,nl.
mostra_caselles(F,C,N,LA,M):-append(_,[(F,C)|_],LA),!,write('A'),write('|'),CR is C+1,mostra_caselles(F,CR,N,LA,M).
mostra_caselles(F,C,N,LA,M):-P is (F-1)*N+C, append(_,[P|_],M),!,write('T'),write('|'),CR is C+1,mostra_caselles(F,CR,N,LA,M).
mostra_caselles(F,C,N,LA,M):-write(' |'),CR is C+1,mostra_caselles(F,CR,N,LA,M).