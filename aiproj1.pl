%%%%%%%%%% Rule Based Expert System Shell %%%%%%%%%%
%%%
%%% This is the expert system with the example from the textbook:
%%%
%%% Artificial Intelligence:
%%% Structures and strategies for complex problem solving
%%%
%%% by George F. Luger and William A. Stubblefield
%%%
%%% These programs are copyrighted by Benjamin//Cummings Publishers.
%%%
%%% Modified by Shaun-inn Wu
%%%
%%% These program are offered for educational purposes only.
%%%
%%% Disclaimer: These programs are provided with no warranty whatsoever as to
%%% their correctness, reliability, or any other property.  We have written
%%% them for specific educational purposes, and have made no effort
%%% to produce commercial quality computer programs.  Please do not expect
%%% more of them then we have intended.
%%%
%%% This code has been tested with SWI-Prolog (Multi-threaded, Version 7.6.4)
%%% and appears to function as intended.


% solve(Goal): solve(resolve_car(Advice)) for the car problem.
% Top level call.  Initializes working memory; attempts to solve Goal
% with certainty factor; prints results; asks user if they would like a
% trace.

solve(Goal) :-
    init, print_help,
    solve(Goal,C,[],1),
    nl,write('Solved '),write(Goal),
    write(' With Certainty = '),write(C),nl,nl,
    ask_for_trace(Goal).

% init
% purges all facts from working memory.

init :- retractm(fact(X)), retractm(untrue(X)).

% solve(Goal,CF,Rulestack,Cutoff_context)
% Attempts to solve Goal by backwards chaining on rules;  CF is
% certainty factor of final conclusion; Rulestack is stack of
% rules, used in why queries, Cutoff_context is either 1 or -1
% depending on whether goal is to be proved true or false
% (e.g. not Goal requires Goal be false in oreder to succeed).

solve(true,100,Rules,_).

solve(A,100,Rules,_) :-
    fact(A).

solve(A,-100,Rules,_) :-
    untrue(A).

solve(not(A),C,Rules,T) :-
    T2 is -1 * T,
    solve(A,C1,Rules,T2),
    C is -1 * C1.

solve((A,B),C,Rules,T) :-
    solve(A,C1,Rules,T),
    above_threshold(C1,T),
    solve(B,C2,Rules,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

solve(A,C,Rules,T) :-
    rule((A :- B),C1),
    solve(B,C2,[rule(A,B,C1)|Rules],T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

solve(A,C,Rules,T) :-
    rule((A), C),
    above_threshold(C,T).

solve(A,C,Rules,T) :-
    askable(A),
    not(known(A)),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% respond( Answer, Query, CF, Rule_stack).
% respond will process Answer (yes, no, how, why, help).
% asserting to working memory (yes or no)
% displaying current rule from rulestack (why)
% showing proof trace of a goal (how(Goal)
% displaying help (help).
% Invalid responses are detected and the query is repeated.

respond(Bad_answer,A,C,Rules) :-
    not(member(Bad_answer,[help, yes,no,why,how(_)])),
    write('answer must be either help, (y)es, (n)o, (h)ow(X), (w)hy'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(yes,A,100,_) :-
    assert(fact(A)).

respond(no,A,-100,_) :-
    assert(untrue(A)).

respond(why,A,C,[Rule|Rules]) :-
    display_rule(Rule),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(why,A,C,[]) :-
    write('Back to goal, no more explanation  possible'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,[]).

respond(how(Goal),A,C,Rules) :-
    respond_how(Goal),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(help,A,C,Rules) :-
    print_help,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% ask(Query, Answer)
% Writes Query and reads the Answer.  Abbreviations (y, n, h, w) are
% trnslated to appropriate command be filter_abbreviations

ask(Query,Answer) :-
    display_query(Query),
    read(A),
    filter_abbreviations(A,Answer),!.

% filter_abbreviations( Answer, Command)
% filter_abbreviations will expand Answer into Command.  If
% Answer is not a known abbreviation, then Command = Answer.

filter_abbreviations(y,yes).
filter_abbreviations(n,no).
filter_abbreviations(w,why).
filter_abbreviations(h,help).
filter_abbreviations(h(X),how(X)).
filter_abbreviations(X,X).

% known(Goal)
% Succeeds if Goal is known to be either true or untrue.

known(Goal) :- fact(Goal).
known(Goal) :- untrue(Goal).

% ask_for_trace(Goal).
% Invoked at the end of a consultation, ask_for_trace asks the user if
% they would like a trace of the reasoning to a goal.

ask_for_trace(Goal) :-
    write('Trace of reasoning to goal ? '),
    read(Answer),nl,
    show_trace(Answer,Goal),!.

% show_trace(Answer,Goal)
% If Answer is ``yes'' or ``y,'' show trace will display  a trace
% of Goal, as in a ``how'' query.  Otherwise, it succeeds, doing nothing.

show_trace(yes,Goal) :- respond_how(Goal).

show_trace(y,Goal) :- respond_how(Goal).

show_trace(_,_).

% print_help
% Prints a help screen.

print_help :-
    write('Exshell allows the following responses to queries:'),nl,nl,
    write('   yes - query is known to be true.'),nl,
    write('   no - query is false.'),nl,
    write('   why - displays rule currently under consideration.'),nl,
    write('   how(X) - if X has been inferred, displays trace of reasoning.'),nl,
    write('   help - prints this message.'),nl,
    write('   Your response may be abbreviated to the first letter and must end with a period (.).'),nl.

% display_query(Goal)
% Shows Goal to user in the form of a query.

display_query(Goal) :-
    write(Goal),
    write('? ').

% display_rule(rule(Head, Premise, CF))
% prints rule in IF...THEN form.

display_rule(rule(Head,Premise,CF)) :-
    write('IF       '),
    write_conjunction(Premise),
    write('THEN     '),
    write(Head),nl,
    write('CF   '),write(CF),
    nl,nl.

% write_conjunction(A)
% write_conjunction will print the components of a rule premise.  If any
% are known to be true, they are so marked.

write_conjunction((A,B)) :-
    write(A), flag_if_known(A),!, nl,
    write('     AND '),
    write_conjunction(B).

write_conjunction(A) :- write(A),flag_if_known(A),!, nl.

% flag_if_known(Goal).
% Called by write_conjunction, if Goal follows from current state
% of working memory, prints an indication, with CF.

flag_if_known(Goal) :-
    build_proof(Goal,C,_,1),
    write('     ***Known, Certainty = '),write(C).

flag_if_known(A).

% Predicates concerned with how queries.

% respond_how(Goal).
% calls build_proof to determine if goal follows from current state of working
% memory.  If it does, prints a trace of reasoning, if not, so indicates.

respond_how(Goal) :-
    build_proof(Goal,C,Proof,1),
    interpret(Proof),nl,!.

respond_how(Goal) :-
    build_proof(Goal,C,Proof,-1),
    interpret(Proof),nl,!.

respond_how(Goal) :-
    write('Goal does not follow at this stage of consultation.'),nl.

% build_proof(Goal, CF, Proof, Cutoff_context).
% Attempts to prove Goal, placing a trace of the proof in Proof.
% Functins the same as solve, except it does not ask for unknown information.
% Thus, it only proves goals that follow from the rule base and the current
% contents of working memory.

build_proof(true,100,(true,100),_).

build_proof(Goal, 100, (Goal :- given,100),_) :- fact(Goal).

build_proof(Goal, -100, (Goal :- given,-100),_) :- untrue(Goal).

build_proof(not(Goal), C, (not(Proof),C),T) :-
    T2 is -1 * T,
    build_proof(Goal,C1,Proof,T2),
    C is -1 * C1.

build_proof((A,B),C,(ProofA, ProofB),T) :-
    build_proof(A,C1,ProofA,T),
    above_threshold(C1,T),
    build_proof(B,C2,ProofB,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

build_proof(A, C, (A :- Proof,C),T) :-
    rule((A :- B),C1),
    build_proof(B, C2, Proof,T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

build_proof(A, C, (A :- true,C),T) :-
    rule((A),C),
    above_threshold(C,T).

% interpret(Proof).
% Interprets a Proof as constructed by build_proof,
% printing a trace for the user.

interpret((Proof1,Proof2)) :-
    interpret(Proof1),interpret(Proof2).

interpret((Goal :- given,C)):-
    write(Goal),
    write(' was given. CF = '), write(C),nl,nl.

interpret((not(Proof), C)) :-
    extract_body(Proof,Goal),
    write('not '),
    write(Goal),
    write(' CF = '), write(C),nl,nl,
    interpret(Proof).

interpret((Goal :- true,C)) :-
    write(Goal),
        write(' is a fact, CF = '),write(C),nl.

interpret(Proof) :-
    is_rule(Proof,Head,Body,Proof1,C),
    nl,write(Head),write(' CF = '),
    write(C), nl,write('was proved using the rule'),nl,nl,
    rule((Head :- Body),CF),
    display_rule(rule(Head, Body,CF)), nl,
    interpret(Proof1).

% isrule(Proof,Goal,Body,Proof,CF)
% If Proof is of the form Goal :- Proof, extracts
% rule Body from Proof.

is_rule((Goal :- Proof,C),Goal, Body, Proof,C) :-
    not(member(Proof, [true,given])),
    extract_body(Proof,Body).

% extract_body(Proof).
% extracts the body of the top level rule from Proof.

extract_body((not(Proof), C), (not(Body))) :-
    extract_body(Proof,Body).

extract_body((Proof1,Proof2),(Body1,Body2)) :-
    !,extract_body(Proof1,Body1),
    extract_body(Proof2,Body2).

extract_body((Goal :- Proof,C),Goal).

% Utility Predicates.

retractm(X) :- retract(X), fail.
retractm(X) :- retract((X:-Y)), fail.
retractm(X).

member(X,[X|_]).
member(X,[_|T]) :- member(X,T).

minimum(X,Y,X) :- X =< Y.
minimum(X,Y,Y) :- Y < X.

above_threshold(X,1) :- X >= 20.
above_threshold(X,-1) :- X =< -20.


%%%
%%% The following is the knowledge base for nutrition advice:
%%%

% Top level goal, starts search.
rule((dietician(Advice) :-
	problems(Y), resolve(Y,Advice)),100).

% rules to infer final diagnostic:

rule((problems(no_interest) :-
issues(not_interested)),80).

rule((problems(obesity) :-
	issues(overweight),not(emotional_eating), not(eating_sweeets_more_than_3_per_week)),90).
rule((problems(obesity11) :-
	issues(overweight11),not(emotional_eating), not(eating_sweeets_more_than_3_per_week)),90).
rule((problems(obesity12) :-
	issues(overweight12),not(emotional_eating), not(eating_sweeets_more_than_3_per_week)),90).


rule((problems(obesity1) :-
	issues(overweight1),not(emotional_eating)),85).
rule((problems(obesity21) :-
	issues(overweight21),not(emotional_eating)),85).
rule((problems(obesity22) :-
	issues(overweight22),not(emotional_eating)),85).


rule((problems(obesity2) :-
	issues(overweight),not(emotional_eating), eating_sweeets_more_than_3_per_week),90).
rule((problems(obesity23) :-
	issues(overweight11),not(emotional_eating), eating_sweeets_more_than_3_per_week),90).
rule((problems(obesity24) :-
	issues(overweight12),not(emotional_eating), eating_sweeets_more_than_3_per_week),90).

rule((problems(emotional_obesity) :-
	issues(overweight),(emotional_eating)),70).
rule((problems(emotional_obesity1) :-
	issues(overweight11),(emotional_eating)),70).
rule((problems(emotional_obesity2) :-
	issues(overweight12),(emotional_eating)),70).



rule((problems(triglycerides) :-
	issues(cholesterol_problem),cholesterol_problem_Triglycerides),90).
rule((problems(triglycerides1) :-
	issues(cholesterol_problem1),cholesterol_problem_Triglycerides),90).
rule((problems(triglycerides2) :-
	issues(cholesterol_problem2),cholesterol_problem_Triglycerides),90).

rule((problems(ldl) :-
	issues(cholesterol_problem), cholesterol_problem_LDL),80).
rule((problems(ldl1) :-
	issues(cholesterol_problem1), cholesterol_problem_LDL),80).
rule((problems(ldl2) :-
	issues(cholesterol_problem2), cholesterol_problem_LDL),80).



rule((problems(bp) :-
	issues(high_blood_pressure)),90).
rule((problems(bp11) :-
	issues(high_blood_pressure1)),90).
rule((problems(bp12) :-
	issues(high_blood_pressure2)),90).


rule((problems(bp1) :-
	high_blood_pressure, not(add_salt_to_meals_at_table), not(sugaryjuices_more_than_1_per_day)),90).
rule((problems(bp21) :-
	high_blood_pressure, not(add_salt_to_meals_at_table), not(sugaryjuices_more_than_1_per_day)),90).
rule((problems(bp22) :-
	high_blood_pressure, not(add_salt_to_meals_at_table), not(sugaryjuices_more_than_1_per_day)),90).

rule((problems(bp2) :-
	high_blood_pressure, not(add_salt_to_meals_at_table), sugaryjuices_more_than_1_per_day),90).
rule((problems(bp23) :-
	high_blood_pressure, not(add_salt_to_meals_at_table), sugaryjuices_more_than_1_per_day),90).
rule((problems(bp33) :-
	high_blood_pressure, not(add_salt_to_meals_at_table), sugaryjuices_more_than_1_per_day),90).


rule((problems(diabetic1) :-
	issues(diabetes), prediabetic),80).
rule((problems(diabetic11) :-
	issues(diabetes11), prediabetic),80).
rule((problems(diabetic12) :-
	issues(diabetes12), prediabetic),80).



rule((problems(diabetic2) :-
	issues(diabetes1)), 90).
rule((problems(diabetic21) :-
	issues(diabetes21)), 90).
rule((problems(diabetic211) :-
	issues(diabetes22)), 90).


rule((problems(diabetic3) :-
	diabetic, not(bloodsugar_level_above_160mg/dL)),80).
rule((problems(diabetic31) :-
	diabetic, not(bloodsugar_level_above_160mg/dL)),80).
rule((problems(diabetic32) :-
	diabetic, not(bloodsugar_level_above_160mg/dL)),80).


rule((problems(bh1) :-
	issues(osteoprosis1), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),80).
rule((problems(bh11) :-
	issues(osteoprosis11), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),80).
rule((problems(bh12) :-
	issues(osteoprosis12), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),80).


rule((problems(bh2) :-
	issues(osteoprosis1), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),95).
rule((problems(bh21) :-
	issues(osteoprosis11), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),95).
rule((problems(bh22) :-
	issues(osteoprosis12), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),95).


rule((problems(bh3) :-
	issues(osteoprosis1), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),90).
rule((problems(bh31) :-
	issues(osteoprosis11), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),90).
rule((problems(bh32) :-
	issues(osteoprosis12), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),90).


rule((problems(bh4) :-
	issues(osteoprosis1), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).
rule((problems(bh41) :-
	issues(osteoprosis11), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).
rule((problems(bh42) :-
	issues(osteoprosis12), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).



rule((problems(bh5) :-
	issues(osteoprosis1), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),80).
rule((problems(bh51) :-
	issues(osteoprosis11), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),80).
rule((problems(bh52) :-
	issues(osteoprosis12), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),80).


rule((problems(bh6) :-
	issues(osteoprosis1), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),90).
rule((problems(bh61) :-
	issues(osteoprosis11), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),90).
rule((problems(bh62) :-
	issues(osteoprosis12), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),90).


rule((problems(bh7) :-
	issues(osteoprosis1), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),95).
rule((problems(bh71) :-
	issues(osteoprosis11), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),95).
rule((problems(bh72) :-
	issues(osteoprosis12), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),95).


rule((problems(bh8) :-
	issues(osteoprosis1), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),90).
rule((problems(bh81) :-
	issues(osteoprosis11), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),90).
rule((problems(bh82) :-
	issues(osteoprosis12), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),90).


rule((problems(bh9) :-
	issues(osteoprosis2), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),80).
rule((problems(bh91) :-
	issues(osteoprosis21), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),80).
rule((problems(bh92) :-
	issues(osteoprosis22), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),80).



rule((problems(bh10) :-
	issues(osteoprosis2), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),95).
rule((problems(bh101) :-
	issues(osteoprosis21), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),95).
rule((problems(bh1012) :-
	issues(osteoprosis22), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, above_40_yearsOld),95).

rule((problems(bh11) :-
	issues(osteoprosis2), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),95).
rule((problems(bh111) :-
	issues(osteoprosis21), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),95).
rule((problems(bh1112) :-
	issues(osteoprosis22), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),95).


rule((problems(bh12) :-
	issues(osteoprosis2), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).
rule((problems(bh121) :-
	issues(osteoprosis21), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).
rule((problems(bh1212) :-
	issues(osteoprosis22), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).



rule((problems(bh13) :-
	issues(osteoprosis2), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),85).
rule((problems(bh131) :-
	issues(osteoprosis21), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),85).
rule((problems(bh1312) :-
	issues(osteoprosis22), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, above_40_yearsOld),85).



rule((problems(bh14) :-
	issues(osteoprosis2), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).
rule((problems(bh141) :-
	issues(osteoprosis21), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).
rule((problems(bh1412) :-
	issues(osteoprosis22), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), above_40_yearsOld),80).


rule((problems(bh15) :-
	issues(osteoprosis2), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),90).
rule((problems(bh151) :-
	issues(osteoprosis21), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),90).
rule((problems(bh1512) :-
	issues(osteoprosis22), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),90).



rule((problems(bh16) :-
	issues(osteoprosis2), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),95).
rule((problems(bh161) :-
	issues(osteoprosis2), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),95).
rule((problems(bh1612) :-
	issues(osteoprosis2), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), above_40_yearsOld),95).




rule((problems(bh17) :-
	issues(osteoprosis3), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh171) :-
	issues(osteoprosis31), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh1712) :-
	issues(osteoprosis32), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).


rule((problems(bh18) :-
	issues(osteoprosis3), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh181) :-
	issues(osteoprosis31), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh1812) :-
	issues(osteoprosis32), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).


rule((problems(bh19) :-
	issues(osteoprosis3), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),95).
rule((problems(bh191) :-
	issues(osteoprosis31), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),95).
rule((problems(bh1912) :-
	issues(osteoprosis32), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),95).


rule((problems(bh20) :-
	issues(osteoprosis3), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),95).
rule((problems(bh201) :-
	issues(osteoprosis31), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),95).
rule((problems(bh2012) :-
	issues(osteoprosis32), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),95).


rule((problems(bh21) :-
	issues(osteoprosis3), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),90).
rule((problems(bh211) :-
	issues(osteoprosis31), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),90).
rule((problems(bh2112) :-
	issues(osteoprosis32), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),90).


rule((problems(bh22) :-
	issues(osteoprosis3), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).
rule((problems(bh221) :-
	issues(osteoprosis31), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).
rule((problems(bh2212) :-
	issues(osteoprosis32), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).

rule((problems(bh23) :-
	issues(osteoprosis3), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).
rule((problems(bh231) :-
	issues(osteoprosis31), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).
rule((problems(bh2312) :-
	issues(osteoprosis32), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).

rule((problems(bh24) :-
	issues(osteoprosis3), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).
rule((problems(bh241) :-
	issues(osteoprosis31), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).
rule((problems(bh2412) :-
	issues(osteoprosis32), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).



rule((problems(bh25) :-
	issues(osteoprosis4), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),90).
rule((problems(bh251) :-
	issues(osteoprosis41), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),90).
rule((problems(bh2512) :-
	issues(osteoprosis42), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),90).


rule((problems(bh26) :-
	issues(osteoprosis4), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh26) :-
	issues(osteoprosis41), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh26) :-
	issues(osteoprosis42), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, resistancetraining_2times_aweek, not(above_40_yearsOld)),80).

rule((problems(bh27) :-
	issues(osteoprosis4), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh27) :-
	issues(osteoprosis41), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh27) :-
	issues(osteoprosis42), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),80).

rule((problems(bh28) :-
	issues(osteoprosis4), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),90).
rule((problems(bh281) :-
	issues(osteoprosis41), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),90).
rule((problems(bh2812) :-
	issues(osteoprosis42), consuming_dairyproducts_regularly, taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),90).

rule((problems(bh29) :-
	issues(osteoprosis4), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh291) :-
	issues(osteoprosis41), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),80).
rule((problems(bh2912) :-
	issues(osteoprosis42), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), resistancetraining_2times_aweek, not(above_40_yearsOld)),80).


rule((problems(bh30) :-
	issues(osteoprosis4), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).
rule((problems(bh301) :-
	issues(osteoprosis41), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).
rule((problems(bh3012) :-
	issues(osteoprosis42), not(consuming_dairyproducts_regularly), taking_vitD_600IU_suppliment, not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).

rule((problems(bh31) :-
	issues(osteoprosis4), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).
rule((problems(bh311) :-
	issues(osteoprosis41), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).
rule((problems(bh3112) :-
	issues(osteoprosis42), consuming_dairyproducts_regularly, not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),85).

rule((problems(bh32) :-
	issues(osteoprosis4), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).
rule((problems(bh321) :-
	issues(osteoprosis41), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).
rule((problems(bh3212) :-
	issues(osteoprosis42), not(consuming_dairyproducts_regularly), not(taking_vitD_600IU_suppliment), not(resistancetraining_2times_aweek), not(above_40_yearsOld)),80).

rule((problems(none) :-
    not(weight_increased_morethan_15kg_than_prepreg_weight), not(diabetic), not(high_blood_pressure), not(cholesterol_problem), not(osteoporosis_problem)),80).


rule((problems(none1) :-
    not(trimester1), not(trimester2), not(trimester3)),80).

% Rules to infer basic diagnostic.

rule((issues(not_interested) :-
    not(interested_in_change_of_diet)),90).

rule((issues(overweight) :- trimester1,
	weight_increased_morethan_15kg_than_prepreg_weight, (bmi(greater_than_25)), not(exercise_more_than_3Hours_aWeek)),70).
rule((issues(overweight11) :- not(trimester1),trimester2,
	weight_increased_morethan_15kg_than_prepreg_weight, (bmi(greater_than_25)), not(exercise_more_than_3Hours_aWeek)),70).
rule((issues(overweight12) :- not(trimester1),not(trimester2),trimester3,
	weight_increased_morethan_15kg_than_prepreg_weight, (bmi(greater_than_25)), not(exercise_more_than_3Hours_aWeek)),70).


rule((issues(overweight1) :- trimester1,
	weight_increased_morethan_15kg_than_prepreg_weight, (bmi(greater_than_25)), (exercise_more_than_3Hours_aWeek)),90).
rule((issues(overweight21) :- not(trimester1),trimester2,
	weight_increased_morethan_15kg_than_prepreg_weight, (bmi(greater_than_25)), (exercise_more_than_3Hours_aWeek)),90).
rule((issues(overweight22) :- not(trimester1),not(trimester2),trimester3,
	weight_increased_morethan_15kg_than_prepreg_weight, (bmi(greater_than_25)), (exercise_more_than_3Hours_aWeek)),90).


rule((issues(cholesterol_problem) :- trimester1,
	cholesterol_problem),80).
rule((issues(cholesterol_problem1) :- not(trimester1),trimester2,
	cholesterol_problem),80).
rule((issues(cholesterol_problem2) :- not(trimester1),not(trimester2),trimester3,
	cholesterol_problem),80).




rule((issues(high_blood_pressure) :- trimester1,
	high_blood_pressure, (add_salt_to_meals_at_table) ),80).
rule((issues(high_blood_pressure1) :- not(trimester1),trimester2,
	high_blood_pressure, (add_salt_to_meals_at_table) ),80).
rule((issues(high_blood_pressure2) :- not(trimester1),not(trimester2),trimester3,
	high_blood_pressure, (add_salt_to_meals_at_table) ),80).

rule((issues(diabetes) :- trimester1,
	diabetic, bloodsugar_level_above_160mg/dL),90).
rule((issues(diabetes11) :- not(trimester1),trimester2,
	diabetic, bloodsugar_level_above_160mg/dL),90).
rule((issues(diabetes12) :- not(trimester1),not(trimester2),trimester3,
	diabetic, bloodsugar_level_above_160mg/dL),90).

rule((issues(diabetes1) :- trimester1,
	diabetic, not(prediabetic)),90).
rule((issues(diabetes21) :- not(trimester1),trimester2,
	diabetic, not(prediabetic)),90).
rule((issues(diabetes22) :- not(trimester1),not(trimester2),trimester3,
	diabetic, not(prediabetic)),90).

rule((issues(osteoprosis1) :- trimester1,
	osteoporosis_problem, prediabetic),85).
rule((issues(osteoprosis11) :- not(trimester1),trimester2,
	osteoporosis_problem, prediabetic),85).
rule((issues(osteoprosis12) :- not(trimester1),not(trimester2),trimester3,
	osteoporosis_problem, prediabetic),85).

rule((issues(osteoprosis2) :-trimester1,
	osteoporosis_problem, not(prediabetic)),90).
rule((issues(osteoprosis21) :- not(trimester1),trimester2,
	osteoporosis_problem, not(prediabetic)),90).
rule((issues(osteoprosis22) :- not(trimester1),not(trimester2),trimester3,
	osteoporosis_problem, not(prediabetic)),90).

rule((issues(osteoprosis3) :- trimester1,
	osteoporosis_problem, prediabetic),85).
rule((issues(osteoprosis31) :- not(trimester1),trimester2,
	osteoporosis_problem, prediabetic),85).
rule((issues(osteoprosis32) :- not(trimester1),not(trimester2),trimester3,
	osteoporosis_problem, prediabetic),85).

rule((issues(osteoprosis4) :-
	osteoporosis_problem, not(prediabetic)),90).
rule((issues(osteoprosis41) :-
	osteoporosis_problem, not(prediabetic)),90).
rule((issues(osteoprosis42) :-
	osteoporosis_problem, not(prediabetic)),90).


% Rules to make reccommendation for patients.

rule(resolve(obesity,'given you are in trimester1, you need to try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables. '),100).
rule(resolve(obesity11,'given you are in trimester2, you need not worry about inncreased weight but try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables. '),100).
rule(resolve(obesity12,'given you are in trimester3, you need  not to worry about increase weight and only do less intensity excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: nfruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables. '),100).


rule(resolve(obesity1,'given you are in trimester1, you need to try not to increase weight anymore by continuing the  excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables.'),100).
rule(resolve(obesity21,'given you are in trimester2, you need not worry about inncreased weight but try not to increase weight anymore by continuing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables.'),100).
rule(resolve(obesity22,'given you are in trimester3, you need  not to worry about increase weight and only do less intensity excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: nfruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables.'),100).

rule(resolve(obesity2,'given you are in trimester1, you need to try not to increase weight anymore by continuing the  excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains and reducing sweets only once per week is strictly advised since you are at high risk of getting diabetes. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables. '), 100).
rule(resolve(obesity23,'given you are in trimester2, you need to try not to increase weight anymore by continuing the  excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains and reducing sweets only once per week is strictly advised since you are at high risk of getting diabetes. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables. '), 100).
rule(resolve(obesity24,'given you are in trimester3, you need  not to worry about increase weight and only do less intensity excercise and following a diet with protein, high fibre content and reducing sweets only once per week is strictly advised since you are at high risk of getting diabetes. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains. sample diet you can consider following:
breakfast: eggs or oatmeal with fruits
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: nfruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables.'),100).

rule(resolve(emotional_obesity,'during pregnancy, moodswings are common which leads you to eat more than usual, however if the condition is worsening and if it effects your health I recommend you to see a psychologist to get checkup for how your moodswings are affecting your eating habits.'),100).
rule(resolve(emotional_obesity1,'during pregnancy, moodswings are common which leads you to eat more than usual, however if the condition is worsening and if it effects your health I recommend you to see a psychologist to get checkup for how your moodswings are affecting your eating habits.'),100).
rule(resolve(emotional_obesity2,'during pregnancy, moodswings are common which leads you to eat more than usual, however if the condition is worsening and if it effects your health I recommend you to see a psychologist to get checkup for how your moodswings are affecting your eating habits.'),100).


rule(resolve(triglycerides,' you can reduce triglycerides by reducing sugar and carbohydrate intake. your should include diet with more protein and very less carbs and you shoould also consider eating food with less fat.
sample diet is as follows:
breakfast: oatmeal or egg whites
snack: protein bars or greek yoghurt
lunch: green leafy vegetables and lean meat with brown rice
dinner: grilled chicken or vegetable soup.
'),100).

rule(resolve(triglycerides1,'you can reduce triglycerides by reducing sugar and carbohydrate intake. your should include diet with more protein and very less carbs and you shoould also consider eating food with less fat.
sample diet is as follows:
breakfast: oatmeal or egg whites
snack: protein bars or greek yoghurt
lunch: green leafy vegetables and lean meat with brown rice
dinner: grilled chicken or vegetable soup. '),100).

rule(resolve(triglycerides2,'you can reduce triglycerides by reducing sugar and carbohydrate intake. your should include diet with more protein and very less carbs and you should also consider eating food with less fat.
sample diet is as follows:
breakfast: oatmeal or egg whites
snack: protein bars or greek yoghurt
lunch: green leafy vegetables and lean meat with brown rice
dinner: grilled chicken or vegetable soup. '),100).

rule(resolve(ldl, ' since you have very high bad cholestral level you should avoid eating saturated fat like butter or high fat dairy products and  packaged  or high processed foods like chocklates or cookies.
 sample diet is as follows:
breakfast: oatmeal or egg whites
snack:  handful of nuts
lunch: green leafy vegetables and lean meat with brown rice
snack: fruits with high fiber like gauva or apples
dinner: grilled chicken or vegetable soup.
 '),100).
rule(resolve(ldl1, ' since you have very high bad cholestral level you should avoid eating saturated fat like butter or high fat dairy products and  packaged  or high processed foods like chocklates or cookies.
 sample diet is as follows:
breakfast: oatmeal or egg whites
snack:  handful of nuts
lunch: green leafy vegetables and lean meat with brown rice
snack: fruits with high fiber like gauva or apples
dinner: grilled chicken or vegetable soup. '),100).
rule(resolve(ldl2, ' since you have very high bad cholestral level you should avoid eating saturated fat like butter or high fat dairy products and  packaged  or high processed foods like chocklates or cookies.
 sample diet is as follows:
breakfast: oatmeal or egg whites
snack:  handful of nuts
lunch: green leafy vegetables and lean meat with brown rice
snack: fruits with high fiber like gauva or apples
dinner: grilled chicken or vegetable soup. '),100).

rule(resolve(bp, 'since you have high blood pressure, avoid eating high sodium content food. try to reduce the salt intake as much as possible and also avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour.'),100).
rule(resolve(bp11, 'since you have high blood pressure, avoid eating high sodium content food. try to reduce the salt intake as much as possible and also avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour.'),100).
rule(resolve(bp12, 'since you have high blood pressure, avoid eating high sodium content food. try to reduce the salt intake as much as possible and also avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour.'),100).


rule(resolve(bp1, 'since you have high blood pressure, avoid eating high sodium content food.  avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour.'),100).
rule(resolve(bp21, 'since you have high blood pressure, avoid eating high sodium content food.  avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour. '),100).
rule(resolve(bp22, 'since you have high blood pressure, avoid eating high sodium content food.  avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour. '),100).


rule(resolve(bp2, 'since you have high blood pressure, avoid eating high sodium content food.  avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. try to reduce sugar intake, as fructose sugar can actually elevate uric acid  levels which inturn can increase blood presuure by forming  nitric acid in blood vessels. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour.'),100).
rule(resolve(bp23, 'since you have high blood pressure, avoid eating high sodium content food.  avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. try to reduce sugar intake, as fructose sugar can actually elevate uric acid  levels which inturn can increase blood presuure by forming  nitric acid in blood vessels. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour.'),100).
rule(resolve(bp33, 'since you have high blood pressure, avoid eating high sodium content food.  avoid eating out since the food is stored with preservaties and most common preservative used in food is made of sodium which can effect the blood  pressure. try to reduce sugar intake, as fructose sugar can actually elevate uric acid  levels which inturn can increase blood presuure by forming  nitric acid in blood vessels. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups cooked with spices for flavour.'),100).



rule(resolve(diabetic1, 'since you are in trimester1, and also prediabetic means  your sugar levels are high in blood and during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes..' ),100).
rule(resolve(diabetic11, 'since you are in trimester2, and also prediabetic means  your sugar levels are high in blood and during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
reakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes..'),100).
rule(resolve(diabetic12, 'since you are in trimester3, and also prediabetic means  your sugar levels are high in blood and during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
reakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes..'),100).



rule(resolve(diabetic2, 'since you are in trimester1, during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
reakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes..'),100).
rule(resolve(diabetic21, 'since you are in trimester2, during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
reakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).
rule(resolve(diabetic22, 'since you are in trimester3, during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
reakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes..'),100).


rule(resolve(diabetic3, 'since you are in trimester1, even though your blood sugar level is not more during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
reakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes...'),100).
rule(resolve(diabetic31, 'since you are in trimester2, even though your blood sugar level is not more during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
reakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).
rule(resolve(diabetic32, 'since you are in trimester3, even though your blood sugar level is not more during pregnancy due to hormonal imbalances your blood sugar levels can spike up easily so your diet should not include simple carbs and high sugar contents. you need to maintain minimum of 3.5 hours between each meal. your diet should include complex carbs and protein.
sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes...'),100).


rule(resolve(bh1, '  bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).
rule(resolve(bh11, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).
rule(resolve(bh12,' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).



rule(resolve(bh2, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).
rule(resolve(bh21, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).
rule(resolve(bh22, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).


rule(resolve(bh3, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).
rule(resolve(bh31, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).
rule(resolve(bh32, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).


rule(resolve(bh4, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh41, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.   '),100).
rule(resolve(bh42, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).



rule(resolve(bh5, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh5, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh5, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.   '),100).


rule(resolve(bh6, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).
rule(resolve(bh61, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).
rule(resolve(bh62, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).


rule(resolve(bh7, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.   '),100).
rule(resolve(bh71, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh72, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).

rule(resolve(bh8, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh81, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh82, ' bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).


rule(resolve(bh9, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.   '),100).
rule(resolve(bh91, '  bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).
rule(resolve(bh92, '  bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.    '),100).



rule(resolve(bh10, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh101, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).
rule(resolve(bh1012, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast: steel cut oats or egg whites with greens
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.'),100).


rule(resolve(bh11, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast:steel cut oats or egg whites with greens followed by a glass of milk to as to increase your vitamin D.
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk  .'),100).
rule(resolve(bh111, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast:steel cut oats or egg whites with greens followed by a glass of milk to as to increase your vitamin D.
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.'),100).
rule(resolve(bh1112, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. you should also do some kind of body weight training to have stronger bones. sample diet is as follows:
breakfast:steel cut oats or egg whites with greens followed by a glass of milk to as to increase your vitamin D.
snack: handful of nuts
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.'),100).

rule(resolve(bh12, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. YOu do not do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. It is recomended that you work out at least for an hour.sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes. '),100).
rule(resolve(bh121, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. YOu do not do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. It is recomended that you work out at least for an hour.sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.  '),100).
rule(resolve(bh1212, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. YOu do not do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. It is recomended that you work out at least for an hour.sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes.   '),100).


rule(resolve(bh13, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk. '),100).
rule(resolve(bh131, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk. '),100).
rule(resolve(bh1312, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk. '),100).


rule(resolve(bh14, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. it is suggested that you excersie at least for an hour in order to increase you physical strength sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.. '),100).
rule(resolve(bh141, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.'),100).
rule(resolve(bh1412, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk. '),100).

rule(resolve(bh15, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.   '),100).
rule(resolve(bh151, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk. '),100).
rule(resolve(bh1512, 'bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy . it is advisable to take calcium suppliment. it is recommended to consult the physician about intake of suppliment. Do any kind of body resistance training so you should also do some kind of body weight training to have stronger bones and also to increse your physical health and also help you maintain a perfectly functing body. sample diet is as follows:
breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.    '),100).

rule(resolve(bh16,'Bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy. Given you are in trimester1, you need to try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains with atleast an hour of daily physical excersie or atleast yoga. sample diet you can consider following and try including as much dairy products in your diet as possible:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables.'),100).
rule(resolve(bh161, 'Bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy. Given you are in trimester2, you need to try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains with atleast an hour of daily physical excersie or atleast yoga. sample diet you can consider following and try including as much dairy products in your diet as possible:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables.  '),100).
rule(resolve(bh1612, 'Bone density decreases as age nummber increases since you are above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy. Given you are in trimester3, you need to try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains with atleast an hour of daily physical excersie or atleast yoga. sample diet you can consider following and try including as much dairy products in your diet as possible:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables.  '),100).

rule(resolve(bh17, ' Given you are in trimester1, you need to try not to increase weight anymore by doing excercise like yoga and maintaining your physical health. have constant intake for your daily vitamins and calcium though you are not above 40 years out during during pregency generally tend to have bone problems so it is always better to have a meal that has a lot od vitamin D suppliments like dairy products:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts, greek yougurt.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple, greek yogurt.
dinner: egg whites and grilled vegetables.  '),100).
rule(resolve(bh171, ' Given you are in trimester2, you need to try not to increase weight anymore by doing excercise like yoga and maintaining your physical health. have constant intake for your daily vitamins and calcium though you are not above 40 years out during during pregency generally tend to have bone problems so it is always better to have a meal that has a lot od vitamin D suppliments like dairy products:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts, greek yougurt.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple, greek yogurt.
dinner: egg whites and grilled vegetables. '),100).
rule(resolve(bh1712, ' Given you are in trimester3, you need to try not to increase weight anymore by doing excercise like yoga and maintaining your physical health. have constant intake for your daily vitamins and calcium though you are not above 40 years out during during pregency generally tend to have bone problems so it is always better to have a meal that has a lot od vitamin D suppliments like dairy products:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts, greek yougurt.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple, greek yogurt.
dinner: egg whites and grilled vegetables.  '),100).


rule(resolve(bh18, ' Given you are in trimester1, you need to try not to increase weight anymore by doing excercise like yoga and maintaining your physical health. have constant intake for your daily vitamins and calcium though you are not above 40 years out during during pregency generally tend to have bone problems so it is always better to have a meal that has a lot od vitamin D suppliments like dairy products since you do not consume a lot of dairy products every day, try including a lot of them into your diet. the diet is as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups .'),100).
rule(resolve(bh181, 'Given you are in trimester2, you need to try not to increase weight anymore by doing excercise like yoga and maintaining your physical health. have constant intake for your daily vitamins and calcium though you are not above 40 years out during during pregency generally tend to have bone problems so it is always better to have a meal that has a lot od vitamin D suppliments like dairy products since you do not consume a lot of dairy products every day, try including a lot of them into your diet. the diet is as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups. '),100).
rule(resolve(bh1812, ' Given you are in trimester3, you need to try not to increase weight anymore by doing excercise like yoga and maintaining your physical health. have constant intake for your daily vitamins and calcium though you are not above 40 years out during during pregency generally tend to have bone problems so it is always better to have a meal that has a lot od vitamin D suppliments like dairy products since you do not consume a lot of dairy products every day, try including a lot of them into your diet. the diet is as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).

rule(resolve(bh19, ' Since you are in your trimester 1,You definatly need to increase your Vitamin D intake and at the same time you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long. the diet is as follows:
 breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups'),100).
rule(resolve(bh191, ' Since you are in your trimester 2, You definatly need to increase your Vitamin D intake and at the same time you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long. the diet is as follows:
 breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).
rule(resolve(bh1912, 'Since you are in your trimester 3, You definatly need to increase your Vitamin D intake and at the same time you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long. the diet is as follows:
 breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups'),100).


rule(resolve(bh20, ' Since you are in your trimester 1, You definatly need to increase your Vitamin D intake and at the same time you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long which ypu also be over come with the help of a lot of physical excersise and also at the same time with some yoga. the diet is as follows:
 breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).
rule(resolve(bh201, 'Since you are in your trimester 2, You definatly need to increase your Vitamin D intake and at the same time you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long which ypu also be over come with the help of a lot of physical excersise and also at the same time with some yoga. the diet is as follows:
 breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).
rule(resolve(bh2012, 'Since you are in your trimester 3, You definatly need to increase your Vitamin D intake and at the same time you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long which you also be over come with the help of a lot of physical excersise and also at the same time with some yoga. the diet is as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).



rule(resolve(bh21, ' Since you are in your trimester 1, you need to focus more on your diary product intake, you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long,. diet as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk.'),100).
rule(resolve(bh211, 'Since you are in your trimester 2, you need to focus more on your diary product intake, you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long,. diet as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk.'),100).
rule(resolve(bh2112, 'Since you are in your trimester 3, you need to focus more on your diary product intake, you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long,. diet as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk. '),100).



rule(resolve(bh22, 'Since you are in your trimester1, you need to focus more on your diary product intake, you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long. Try including at least an hours physical training in your daily routine.  diet as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk.'),100).
rule(resolve(bh221, 'Since you are in your trimester1, you need to focus more on your diary product intake, you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long. Try including at least an hours physical training in your daily routine.  diet as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk.'),100).
rule(resolve(bh2212, 'Since you are in your trimester1, you need to focus more on your diary product intake, you also need to increase the intake of calcium as women during pregnency tend to develop a lot of probelm related to their bond density and have face effects life long. Try including at least an hours physical training in your daily routine.  diet as follows:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk.'),100).


rule(resolve(bh23, ' Since you are in your trimester 1, you need to focus more on your dairy product intake beside that focus on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products  '),100).
rule(resolve(bh231, ' Since you are in your trimester 2, you need to focus more on your dairy product intake beside that focus on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products   '),100).
rule(resolve(bh2312, ' Since you are in your trimester 3, you need to focus more on your dairy product intake beside that focus on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products   '),100).

rule(resolve(bh24, '  Since you are in your trimester 1, you need to focus more on your dairy product intake beside that focus on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk. '),100).
rule(resolve(bh241, ' Since you are in your trimester 2, you need to focus more on your dairy product intake beside that focus on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk.  '),100).
rule(resolve(bh2412, ' Since you are in your trimester 3, you need to focus more on your dairy product intake beside that focus on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: multigrain crackers or handful of nuts.
lunch: lean meat like chickenbreast or grilled fish with brown rice
snack: fruits with more fibre like gauva or apple
dinner: egg whites and grilled vegetables with a glass of milk.'),100).




rule(resolve(bh25, ' You have a good health condition. you can mainain this with the help of focusing on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products  '),100).
rule(resolve(bh251, '  You have a good health condition. you can mainain this with the help of focusing on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products  '),100).
rule(resolve(bh2512, ' You have a good health condition. you can mainain this with the help of focusing on your suppliment intake like your vitamins and calcuim aslo with an hour of physical excersise.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. Three servings of milk products  '),100).


rule(resolve(bh26, '  You have a good health condition you can make it much better with the intake of lot of milk products with regular excersie.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. five servings of milk products  '),100).
rule(resolve(bh261, ' You have a good health condition you can make it much better with the intake of lot of milk products with regular excersie.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. five servings of milk products  '),100).
rule(resolve(bh2612, ' You have a good health condition you can make it much better with the intake of lot of milk products with regular excersie.
Five servings of fresh fruits and vegetables
Six servings whole-grain breads and cereals. five servings of milk products  '),100).

rule(resolve(bh27, 'you need to focus the intake on your vitamins followed by  bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice. '),100).
rule(resolve(bh271, 'you need to focus the intake on your vitamins followed by  bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice.  '),100).
rule(resolve(bh2712, 'you need to focus the intake on your vitamins followed by  bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice. '),100).

rule(resolve(bh28, ' Physical excersise is very important part of your pregnency and please try to fitthat into your schedule at least for an hour.
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).
rule(resolve(bh281, ' Physical excersise is very important part of your pregnency and please try to fitthat into your schedule at least for an hour.
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).
rule(resolve(bh2812, ' Physical excersise is very important part of your pregnency and please try to fitthat into your schedule at least for an hour.
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts, greek yougurt.
lunch: grilled fish with brown rice or lentels.
snack: fruits with  greek yogurt.
dinner: grilled vegetables or soups '),100).


rule(resolve(bh29, ' Bone density decreases as age nummber increases since you are not above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy. Given you are in trimester3, you need to try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains with atleast an hour of daily physical excersie or atleast yoga. sample diet you can consider following and try including as much dairy products in your diet as possible:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts.
lunch: meat like chickenbreast with brown rice
snack: fruits with yougurt
dinner: grilled vegetables and lentels.'),100).
rule(resolve(bh291, 'Bone density decreases as age nummber increases since you are not above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy. Given you are in trimester3, you need to try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains with atleast an hour of daily physical excersie or atleast yoga. sample diet you can consider following and try including as much dairy products in your diet as possible:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts.
lunch: meat like chickenbreast with brown rice
snack: fruits with yougurt
dinner: grilled vegetables and lentels'),100).
rule(resolve(bh2912, ' Bone density decreases as age nummber increases since you are not above 40 it is recommended to take high calcium foods like dairy though that you do not have any bone density problem and also being pregnant and even though you are not prediabetic you need to balance diet with protein, good fats,high fibre and less dairy. Given you are in trimester3, you need to try not to increase weight anymore by doing excercise and following a diet with protein and high fibre content is necesary. you need to include healthy plate model for all meals which includes more protein filled with lean meat and vegetables and  complexcarbs like whole grains with atleast an hour of daily physical excersie or atleast yoga. sample diet you can consider following and try including as much dairy products in your diet as possible:
breakfast: eggs or oatmeal with fruits with a glass of milk
snack: handful of nuts.
lunch: meat like chickenbreast with brown rice
snack: fruits with yougurt
dinner: grilled vegetables and lentels.'),100).


rule(resolve(bh30, 'Since you are not above 30,but there is still a potential risk that you still have low bone density. You also need to consume a lot of dairy products with a constant intake of vitamins and regular excersise. bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice.'),100).
rule(resolve(bh301, 'Since you are not above 30,but there is still a potential risk that you still have low  bone density. You also need to consume a lot of dairy products with a constant intake of vitamins and regular excersise. bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice. .'),100).
rule(resolve(bh3012, 'Since you are not above 30,but there is still a potential risk that you still have low bone density. You also need to consume a lot of dairy products with a constant intake of vitamins and regular excersise. bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice .'),100).


rule(resolve(bh31, '  Since you are not above 30,but there is still a potential risk that you still have  low bone density. You also need to consume a lot of dairy products with a constant intake of vitamins and regular excersise. bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice. '),100).
rule(resolve(bh311, 'Since you are not above 30,but there is still a potential risk that you still have  low bone density. You also need to consume a lot of dairy products with a constant intake of vitamins and regular excersise. bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice.  '),100).
rule(resolve(bh3112, 'Since you are not above 30,but there is still a potential risk that you still have  low bone density. You also need to consume a lot of dairy products with a constant intake of vitamins and regular excersise. bowl of oatmeal with any kinds of fresh fruits pancakes made from whole grain flour. A slice of wheat toast with peanut butter unless you are allergic to nuts.a glass of low-fat milk. Aglass of any fruit juice.'),100).

rule(resolve(bh32, ' you need to take serious action in order to improve your health condition with proper consumprion of vitamin, minerals, foods like veggies with constant physical excersie.   breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.  '),100).
rule(resolve(bh321, 'you need to take serious action in order to improve your health condition with proper consumprion of vitamin, minerals, foods like veggies with constant physical excersie.   breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.   '),100).
rule(resolve(bh3212, 'you need to take serious action in order to improve your health condition with proper consumprion of vitamin, minerals, foods like veggies with constant physical excersie.   breakfast: egg whites with greens and a fruit; any of your choice, followed by a glass of milk to as to increase your vitamin D.
snack: greek yougurt with fruit salad
lunch: fill the plate with more home cooked lean meats and grilled vegetables or sauted vegetables in olive oil.
dinner: any vegetable soups and avoid vegetables with high carbs like potatoes and followed by a glass of milk.'),100).

rule(resolve(none, 'It appears you are on the right track. If you have any specific dietary questions or health concerns, visit your local dietician! '),100).

rule(resolve(no_interest, 'It seems that you are not ready to make changes to your diet just yet. Know that we are always here to help you achieve your goals when you feel that you are ready. Here are some nutrition tips should you be interested: Aim for 4-8 servings of fruits per day (serving = half a cup). Always pick real fruit over fruit juice.  Also, aim for 4-8 servings (serving = half a cup) of vegetables per day (raw, cooked, steamed, boiled) '),100).

rule(resolve(none1,' It seems that you are not ready to make changes to your diet just yet. Know that we are always here to help you achieve your goals'),100).

% askable descriptions
askable(diabetic).
askable(weight_increased_morethan_15kg_than_prepreg_weight).
askable(above_40_yearsOld).
askable(prediabetic).
askable(bmi(greater_than_25)).
askable(high_blood_pressure).
askable(interested_in_change_of_diet).
askable(exercise_more_than_3Hours_aWeek).
askable(sugaryjuices_more_than_1_per_day).
askable(eating_sweeets_more_than_3_per_week).
askable(emotional_eating).
askable(cholesterol_problem).
askable(cholesterol_problem_Triglycerides).
askable(cholesterol_problem_LDL).
askable(add_salt_to_meals_at_table).
askable(bloodsugar_level_above_160mg/dL).
askable(osteoporosis_problem).
askable(consuming_dairyproducts_regularly).
askable(taking_vitD_600IU_suppliment).
askable(resistancetraining_2times_aweek).
askable(trimester1).
askable(trimester2).
askable(trimester3).






