:- dynamic adjective/5.
% A noun phrase is a determiner followed by adjectives followed
% by a noun followed by an optional prepositional phrase.
noun_phrase(T0,T4,Obj,C0,C4) :-
    det(T0,T1,Obj,C0,C1),
    adjectives(T1,T2,Obj,C1,C2),
    noun(T2,T3,Obj,C2,C3),
    mp(T3,T4,Obj,C3,C4).

% Determiners are ignored in this oversimplified example.
det([the | T],T,_,C,C).
det([a | T],T,_,C,C).
det(T,T,_,C,C).

% adjectives consist of a sequence of adjectives.
adjectives(T,T,_,C,C).
adjectives(T0,T2,Obj,C0,C2) :-
    adjective(T0,T1,Obj,C0,C1),
    adjectives(T1,T2,Obj,C1,C2).

% An optional modifying phrase / relative clause is either
% nothing or
% a prepositional phrase or
% that followed by a verb phrase
mp(T,T,_,C,C).
mp(T0,T2,O1,C0,C2) :-
    reln(T0,T1,O1,O2,C0,C1),
    noun_phrase(T1,T2,O2,C1,C2).
mp([that|T0],T2,O1,C0,C2) :-
    reln(T0,T1,O1,O2,C0,C1),
    noun_phrase(T1,T2,O2,C1,C2).

% DICTIONARY
noun([X | T],T,X,C,C) :- course(X).
noun([X | T],T,X,C,C) :- course_list(X).
reln([the,prerequisites,of | T],T,O1,O2,C,[requirements(O2,[],O1)|C]).
reln([the,prerequisites,of,Course,with,the,following,courses,taken | T],T,O1,O2,C,[requirements(Course,O2,O1)|C]).
% reln([the,prerequisites,of,Course,with,the,following,courses,taken | T],T,O1,O2,C,[requirements(Course,[O2],O1)|C]).



% question(Question,QR,Object,Q0,Query) is true if Query provides an answer about Object to Question
question([is | T0],T2,Obj,C0,C2) :-
    noun_phrase(T0,T1,Obj,C0,C1),
    mp(T1,T2,Obj,C1,C2).
question([what,is | T0],T1,Obj,C0,C1) :-
    mp(T0,T1,Obj,C0,C1).
question([what,is | T0],T1,Obj,C0,C1) :-
    noun_phrase(T0,T1,Obj,C0,C1).
question([what,are | T0],T1,Obj,C0,C1) :-
    mp(T0,T1,Obj,C0,C1).
question([what,are | T0],T1,Obj,C0,C1) :-
    noun_phrase(T0,T1,Obj,C0,C1).
question([what | T0],T2,Obj,C0,C2) :-
    noun_phrase(T0,T1,Obj,C0,C1),
    mp(T1,T2,Obj,C1,C2).

% ask(Q,A) gives answer A to question Q
ask(Q,A) :-
    question(Q,[],A,[],C),
    prove_all(C).

% prove_all(L) proves all elements of L against the database
prove_all([]).
prove_all([H|T]) :-
    call(H),
    prove_all(T).

% course_list(L) is true if each element in the list L is a course
course_list([]).
course_list([H|T]) :-
	course(H),
	course_list(T).
% requirements(Course, Taken, List) is true if List contains all of the prerequisites of Course (and the prerequisites to those courses) minus the courses in Taken
requirements(Course, _, []) :-
	\+ prop(Course, requires, _).
requirements(Course, Taken, L) :-
	prop(Course, requires, Reqs),
	subtract(Reqs, Taken, TrimReqs),
	requirements_list(TrimReqs, Taken, Subreqs),
	union(Subreqs, TrimReqs, L).

% requirements_list(Courses, Taken, List) is true if List contains all of the prerequisites of all courses in Courses minus the courses in Taken
requirements_list([], _, []).
requirements_list([H | T], Taken, L) :-
	requirements(H, Taken, ReqsH),
	requirements_list(T, Taken, ReqsT),
	union(ReqsH, ReqsT, L).

% schedule(Course, Taken, Schedule) is true if Schedule contains a list of lists of courses which, taken in that order, will allow a student to take Course in the final semester while ensuring all prerequisites are met.
schedule(Course, Taken, L) :-
	requirements(Course, Taken, List),
	build_schedule([Course|List], Taken, L).

% build_schedule(List, Taken, Schedule) is true if Schedule contains a division of courses in List such that no course comes before any of its prerequisites.
build_schedule([], _, []).
build_schedule(List, Taken, [S | L]) :-
	List \== [],
	S \== [],
	list_reqs_met(List, Taken, S),
	subtract(List, S, TrimList),
	union(Taken, S, AddTaken),
	build_schedule(TrimList, AddTaken, L).

% list_reqs_met(List, Taken, Met) is true if Met contains all courses in List whose requirements are met by the courses in Taken.
list_reqs_met([], _, []).
list_reqs_met([H | T], Taken, [H | L]) :-
	requirements(H, Taken, []),
	list_reqs_met(T, Taken, L).
list_reqs_met([H | T], Taken, L) :-
	\+ requirements(H, Taken, []),
	list_reqs_met(T, Taken, L).

% shortest_list(L, S) is true if S is the shortest list in the list of lists L.
shortest_list([Shortest], Shortest) :- is_list(Shortest).
shortest_list([H|T], H) :-
	is_list(H),
	shortest_list(T, TShortest),
	length(H,HLength),
	length(TShortest, TSLength),
	HLength =< TSLength.
shortest_list([H|T], TShortest) :-
	is_list(H),
	shortest_list(T, TShortest),
	length(H,HLength),
	length(TShortest, TSLength),
	HLength >= TSLength.

% shortest_schedule(C, T, S) is true if S is the schedule with the least amount of terms that satisfies schedule(C, T, S).
shortest_schedule(Course, Taken, Sched) :-
	setof(X, schedule(Course,Taken,X), Scheds),
	shortest_list(Scheds, Sched).

%  The Database of Facts to be Queried
course(cs103).
course(cs110).
course(cs121).
course(cs210).
course(cs213).
course(cs221).
course(cs260).
course(cs261).
course(cs302).
course(cs304).
course(cs310).
course(cs311).
course(cs313).
course(cs314).
course(cs317).
course(cs319).
course(cs320).
course(cs322).
course(cs340).
course(cs344).
course(cs349).
course(cs404).
course(cs406).
course(cs415).
course(cs418).
course(cs420).
course(cs421).
course(cs422).
course(cs424).
course(cs444).
course(cs445).
course(cs449).
course(bs200).
course(bs300).
course(bs301).
course(bs500).
prop(cs210,requires,[cs110]).
prop(cs210,requires,[cs260]).
prop(cs213,requires,[cs121,cs210]).
prop(cs221,requires,[cs210,cs121]).
prop(cs261,requires,[cs260]).
prop(cs302,requires,[cs103]).
prop(cs302,requires,[cs110]).
prop(cs302,requires,[cs260]).
prop(cs303,requires,[cs103]).
prop(cs303,requires,[cs110]).
prop(cs303,requires,[cs260]).
prop(cs304,requires,[cs221]).
prop(cs304,requires,[cs260,cs210]).
prop(cs310,requires,[cs210]).
prop(cs311,requires,[cs210]).
prop(cs312,requires,[cs210]).
prop(cs313,requires,[cs213,cs221]).
prop(cs313,requires,[cs210,cs213,cs260]).
prop(cs314,requires,[cs221]).
prop(cs314,requires,[cs260]).
prop(cs317,requires,[cs213,cs221]).
prop(cs319,requires,[cs310]).
prop(cs320,requires,[cs221]).
prop(cs322,requires,[cs221]).
prop(cs322,requires,[cs260,cs210]).
prop(cs340,requires,[cs221]).
prop(cs340,requires,[cs260,cs210]).
prop(cs344,requires,[cs210]).
prop(cs404,requires,[cs304,cs213]).
prop(cs404,requires,[cs304,cs261]).
prop(cs406,requires,[cs302]).
prop(cs406,requires,[cs303]).
prop(cs410,requires,[cs310]).
prop(cs411,requires,[cs213,cs221,cs311]).
prop(cs415,requires,[cs313]).
prop(cs416,requires,[cs313,cs317]).
prop(cs418,requires,[cs261,cs320]).
prop(cs420,requires,[cs320]).
prop(cs421,requires,[cs221]).
prop(cs421,requires,[cs260]).
prop(cs422,requires,[cs322]).
prop(cs424,requires,[cs320]).
prop(cs444,requires,[cs310,cs344]).
prop(cs445,requires,[cs320]).
prop(cs449,requires,[cs349]).

prop(bs500,requires,[bs300]).
prop(bs300,requires,[bs200]).
prop(bs500,requires,[bs301]).

% prop(C,corequires,L) means that course C co-requires all courses in list L.
prop(cs121,corequires,[cs110]).

/* Try the following queries:
?- requirements(cs110,[],X).
?- requirements(cs110,[math430],X).
?- requirements(cs110,[math430],X).
?- requirements(cs210,[],X).
?- requirements(cs210,[cs110,cs260],X).
?- requirements(cs444,[cs260,cs210,cs310],X).

?- schedule(cs9001,[],X).
?- schedule(cs210,[cs110],X).
?- schedule(cs210,[cs260],X).
?- schedule(cs210,[cs110,cs260],X).
?- schedule(cs444,[cs210,cs260],X).
?- schedule(cs411,[],X).

?- shortest_schedule(bs500, [], X).
?- shortest_schedule(cs313, [cs213], X).
?- ask([what,are,the,prerequisites,of,cs313],A).
?- ask([what,are,the,prerequisites,of,cs313,with,the,following,courses,taken,[cs213]],A).
?- ask([what,are,the,prerequisites,of,cs313,with,the,following,courses,taken,[cs213,cs260]],A).
*/
