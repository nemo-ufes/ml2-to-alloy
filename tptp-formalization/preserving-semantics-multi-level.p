%
% Preserving Multi-Level Semantics in  Conventional Two-Level Modeling Techniques
%
% (formalization to accompany paper)
% (including a formalization of a fragment of MLT-star based on ER 2017 paper
%  https://doi.org/10.1007/978-3-319-69904-2_2 )
%
% João Paulo A. Almeida, 24-Apr-2019
%
% All conjectures proven with http://tptp.cs.miami.edu/cgi-bin/SystemOnTPTP
%

% Top fragment of MLT-star, section 3

% All elements in the domain of quantification are entities
fof(a1, axiom, (
	![X] : (entity(X))
	)).

% Individual definition
fof(a2, axiom, (
	![X] : (individual(X) <=> ~?[Y] : iof(Y,X))
	)).

% Type definition
fof(a3, axiom, (
	![X] : (type_(X) <=> ?[Y] : iof(Y,X))
	)).

% Auxiliary definitions to write a4 (without transitive iof')
% We need the notion of 'set of types' 
% We do not necessitate infinite sets, but all possible sets considering the existing types
% We do not necessitate the empty set

% A singleton set exists for every type
fof(singleton, axiom, (
	![X] : (type_(X) => (?[Y]: (set_(Y) & member(X,Y) & ![Z]:(member(Z,Y)=>(Z=X)))))
)).

% Unions exists for every pair of sets
fof(unions, axiom, (
	![X,Y] : ((set_(X)&set_(Y)) => 
		?[Z]: (set_(Z)& ![E]: (member(E,Z) <=> (member(E,X)|member(E,Y)))) )
)).

% Set identity (extensionality)
fof(setidentity, axiom, (
	![S1,S2] :
	( (set_(S1) & set_(S2)) => ((S1=S2) <=> ![X]:(member(X,S1)<=>member(X,S2))))
	)).

% We are only concerned with sets of types, membership is only meaningful for sets and types
fof(membershiptyping, axiom, (
	![X,Y] : (member(X,Y) => (set_(Y)&type_(X)))
)).

% Sets are individuals
fof(setsareindividuals, axiom, (
	![X] : (set_(X) => individual(X))
)).

% end of auxiliary definitions

% Types are ultimately grounded on individuals
% for all non-empty set of types
% there exists a member of the set that has an instance that is not the a member of the set
fof(a4, axiom, (
	![X]: ( (set_(X) & (?[Y]:(member(Y,X))) & (![Y]: (member(Y,X)=>type_(Y))) ) =>
		?[Y]: (member(Y,X) & ?[Z]: (iof(Z,Y)&~member(Z,X)))
	)
)).


% Specialization definition
fof(a5, axiom, (
	![T1,T2] :
	(specializes(T1,T2) <=> (type_(T1) & ![E]:(iof(E,T1) => iof(E,T2)))) 
	)).
	
% Proper specialization definition
fof(a6, axiom, (
	![T1,T2] :
	(properSpecializes(T1,T2) <=> (specializes(T1,T2) & ~(T1=T2))) 
	)).

% Type equality
fof(a7, axiom, (
	![T1,T2] :
	( (type_(T1) & type_(T2)) => ((T1=T2) <=> ![X]:(iof(X,T1)<=>iof(X,T2)))) 
	)).

% Cardelli powertype definition
fof(a8, axiom, (
	![T1,T2] :
	(isPowertypeOf(T1,T2) <=> (type_(T1) & ![T3]:(iof(T3,T1)<=>specializes(T3,T2)))) 
	)).

% Odell powertype definition
fof(a9, axiom, (
	![T1,T2] :
	(categorizes(T1,T2) <=> (type_(T1) & ![T3]:(iof(T3,T1)=>properSpecializes(T3,T2)))) 
	)).


% Section 4.2: The missing link

% Formula schema for linking instance and type facets
% fof(a14, axiom, (
%	![Y] : ((Y=reifiedClass) <=> ![X]: (class(X) <=> iof(X,Y)))
%	)).
	
% applying linking schema in example:
fof(a15, axiom, (
	![Y] : ((Y=lionReified) <=> ![X]: (lion(X) <=> iof(X,Y)))
	)).
	
fof(a16, axiom, (
	![Y] : ((Y=entityReified) <=> ![X]: (entity(X) <=> iof(X,Y)))
	)).
	
fof(a17, axiom, (
	![Y] : ((Y=typeReified) <=> ![X]: (type_(X) <=> iof(X,Y)))
)).	
	
fof(a18, axiom, (
	![Y] : ((Y=individualReified) <=> ![X]: (individual(X) <=> iof(X,Y)))
)).
	
fof(a19, axiom, (
	![Y] : ((Y=animalReified) <=> ![X]: (animal(X) <=> iof(X,Y)))
	)).
	
fof(a20, axiom, (
	![Y] : ((Y=animalSpeciesReified) <=> ![X]:(animalSpecies(X) <=> iof(X,Y)))
	)).


% Section 4.3, Consequences of the representation scheme

% the reified class is the only one linked to all its instances
% mirroring native instantiation
fof(t2, conjecture, (
	![T] : ((![X]: (lion(X) <=> iof(X,T)))=> (T=lionReified))
	)).

% properSpecializes mirrors native specialization 
% lion -> animal
fof(t4, conjecture, (
	![X,Y] : (((X=lionReified)&(Y=animalReified)) => properSpecializes(X,Y))
	<=>
	( ![X]: (lion(X) => animal(X)) & ?[Y]:(animal(Y) & ~lion(Y)) )
	)).
	
	
%%%% not in the paper due to space constraints

% native specialization follows from categorization and emulated instantiation
fof(t_notinpaper1, conjecture, (
	(![X,Y] : (((X=animalSpeciesReified)&(Y=animalReified)) => categorizes(X,Y))
	&
	![X,Y] : (((X=lionReified)&(Y=animalSpeciesReified)) => iof(X,Y))
	) 
	=>
	( ![X]: (lion(X) => animal(X)) & ?[Y]:(animal(Y) & ~lion(Y)) )
	)).
	
% native instantiation of the base class follows from Cardelli's powertype 
% for all instances of instances of the powertype
fof(t_notinpaper2, conjecture, (
	(![X,Y] : (((X=animalTypeReified)&(Y=animalReified)) => isPowertypeOf(X,Y)))
	=>
	![X,Y,Z] : ( ((Y=animalTypeReified)&iof(X,Y)&iof(Z,X)) => animal(Z)) 
	)).	

	
% suppose we introduce a dog class
fof(a14_dog, axiom, (
	![Y] : ((Y=dogReified) <=> ![X]: (dog(X) <=> iof(X,Y)))
	)).

% if dog and lion are not necessarily coextensional 
% then dogReified is different from lionReified
% the same can be said for all pairs of reified types, if we assume classes are 
% not necessarily coextensional 
% (the common unique name assumption for types in a conceptual model)
%
fof(reifiedAreDifferent, conjecture, (
	~![X]: (dog(X)<=>lion(X)) 
	=>
	![X,Y] : (((X=dogReified)&(Y=lionReified)) => ~(X=Y))
	)).

