/**
*	MLT*
*	
*	MLT* extends basic MLT. The domain of quantification is a superset of Basic MLT,
*	admitting types that are not stratified. This opens up the possibility of the types
*	"Entity" (the type of all entities, i.e., the universe), "Type" (the type of all
*	types), "OrderedType" (which is the type of all types in Basic MLT), etc.
*
*	Some known limitations of this specification are:
*	  - Static classification only;
*	  - No support for entity's features (attributes and domain relations).
*
*	Authors:
*	  Victorio Carvalho - Basic MLT
*	  João Paulo Almeida - Contributions to Basic MLT and initial developments of MLT*
*	  Claudenir Fonseca - Revision and refactoring of MLT* and further developments
*/

module MLTStar

/********************************************************************************************
* UTILS - PREDICATES AND FUNCTIONS
* The predicates below are used throughout the code improving its readability.
********************************************************************************************/

pred iof[x,y: Entity] 					{ x in iof.y }
pred specializes[x,y: Entity] 			{ x in specializes.y }
pred properSpecializes[ x,y: Entity] 	{ x in properSpecializes.y }
pred powertypeOf[x,y: Entity] 			{ x in powertypeOf.y }
pred categorizes[x,y: Entity] 			{ x in categorizes.y }
pred compCategorizes[x,y: Entity] 		{ x in compCategorizes.y }
pred disjCategorizes[x,y: Entity] 		{ x in disjCategorizes.y }
pred partitions[x,y: Entity] 			{ x in partitions.y }
pred isSubordinatedTo[x,y: Entity] 		{ x in isSubordinatedTo.y }
pred disjointExtentions[t,t': Type] 	{ no iof.t & iof.t' }
pred disjoint_[x,y: Entity] 			{ no x & y }

/********************************************************************************************
* MODEL SPECIFICATION
* Signatures and Constraints.
********************************************************************************************/

/**
*	Entity
*
*	Represents an entity, with all possible relations that may be established between
*	entities according to the theory.
*/
sig Entity { 
	iof: set Entity,
	directIof: set Entity
}

/**	Direct instantiations are used to simplify the visualization of	instantiations. */
fact {
	all e: Entity | e.directIof = (e.iof) - (e.iof).properSpecializes
}

/**
*	Individual
*
*	An individual is an entity that has no possible instances. The signature Individual
*	does not account for the entity Individual, which is going to be specified later
*	through the signature Individual_ (with an underscore at the end).
*/
sig Individual in Entity {
}

fact individualDef {
	all x: Entity | (x in Individual iff no iof.x)
}

/**
*	Type
*
*	A type is an entity that has instances. Also, types must be in an instantiation
*	chain that eventually leads to some individual. As Individual, Type does not
*	account for the entity type, which is specified later as Type_.
*/
sig Type in Entity {
 	specializes: set Type,
	properSpecializes: set Type,
	isSubordinatedTo: set Type,
	powertypeOf: set Type,
	categorizes: set Type,
	compCategorizes: set Type,
	disjCategorizes: set Type,
	partitions: set Type,
	directSpecializes: set Entity,
	isDirectSubordinateTo: set Type,
	directCategorizes: set Type
}

fact {
	all e: Entity | e in Type iff some (iof.e)
}

/** Types are ultimately founded upon individuals. */
fact typeWellFounded {
	all t: Type | t in Type iff some (^iof.t & Individual)
}

/**	Direct relations are used to improve visualization of runs and checkings. */
fact {
	all t: Type | t.directSpecializes = (t.properSpecializes) - (t.properSpecializes).properSpecializes
	all t: Type | t.isDirectSubordinateTo = (t.isSubordinatedTo) - (t.isSubordinatedTo).properSpecializes
	all t: Type | t.directCategorizes = ((t.categorizes) - (t.categorizes+t.powertypeOf).properSpecializes)
}

/**
*	BasicType
*
*	Basic types are the highest entities in their specialization chain of any instance
*	order. That is, for any given type order there is one entity that every ordered
*	type specializes. In other words, a basic type is a type at the top of the 
*	hierarchy of specializations of types that are "stratified" in Basic MLT.
*/
sig BasicType in Type {
}

fact {
	all b: Type | b in BasicType iff ((all e: Entity | iof[e,b] iff e in Individual) or (some lot: BasicType | powertypeOf[b,lot]))
}

/** Not necessary in Basic MLT but saves up to 15 seconds. */
fact noIofLoopForBasicTypes	{
	all x: BasicType | x not in x.^iof
}

/**
*	OrderedType
*
*	A type is a ordered type iff it is a specialization of a basic type.
*/
sig OrderedType in Type {
}

fact {
	all t: Type | t in OrderedType iff (some b: BasicType | specializes[t,b])
}

/**
*	OrderlessType
*
*	A type is a orderless type iff it is not an ordered one.
*/
sig OrderlessType in Type {
}

fact {
	all t: Type | t in OrderlessType iff (no b: BasicType | specializes[t,b])
}

/********************************************************************************************
* CONSTANT MODEL ENTITIES
* Signatures to reference the entities which instances are members of the sets defined above.
********************************************************************************************/

/** Defining the "Individual_" basic type. */
sig Individual_ in Type {
}

fact {
	all e: Entity | e in Individual_ iff (all e': Entity | iof[e',e] iff no iof.e')
}

/** Defining the type "Type", whose instances are all types. */
sig Type_ in Entity {
}

fact {
	all t: Entity | t in Type_ iff (all e: Entity | iof[e,t] iff e in Type)
}

/** Defining the universal type "Entity". */
sig Entity_ in Entity {
}

fact {
	all e: Entity | e in Entity_ iff (all e': Entity | iof[e',e] iff e' in Entity)
}

/** Defining the type "OrderedType", whose instances are all types whose instances
	are at the same order. These are the types in Basic MLT. */
sig OrderedType_ in Entity {
}

fact {
	all e: Entity | e in OrderedType_ iff (all e': Entity | iof[e',e] iff e' in OrderedType)
}

/** Defining the type "OrderlessType", whose instances are all types whose instances
	span through different orders. These are the types in Basic MLT. */
sig OrderlessType_ in Entity {
}

fact {
	all e: Entity | e in OrderlessType_ iff (e in Type and (all e': Entity | iof[e',e] iff e' in OrderlessType))
}

/********************************************************************************************
* DEFINITIONS
********************************************************************************************/

/** Axiom A7 - Two types are equal iff the set of all their possible instances is the 
	same */
fact typesEquivalence {
	all t1,t2: Type | (t1 = t2 iff iof.t1 = iof.t2)
}

/** Axiom A8 - Specialization Definition: t1 specializes t2 iff all instances of t1 are
	also instances of t2. */
fact specializationDefinition {
	all t1,t2: Type | specializes[t1,t2] iff (all e: iof.t1 | iof[e,t2])
}

/**	Axiom A9 - Proper Specialization Definition: t1 proper specializes t2 iff t1
	specializes t2 and is different from it. */
fact properSpecializationDefinition {
	all t1,t2: Type | properSpecializes[t1,t2] iff (specializes[t1,t2] and t1 != t2)
}

/**	Axiom A10 - Subordination Definition: t1 is subordinate to t2 iff every instance of
	t1 specializes an instance of t2. */
fact subordinationDefinition {
	all t1,t2: Type | isSubordinatedTo[t1,t2] iff (all t3: iof.t1 | some (t3.properSpecializes & iof.t2))
}

/**	Axiom A11 - Powertype Definition: a type t1 is powertype of a type t2 iff all
	instances of t1 are specializations of t2 and all possible specializations of t2
	are	instances of t1. */
fact powertypeOfDefinition {
	all pwt,t: Type | powertypeOf[pwt,t] iff (all t': Entity | (iof[t',pwt] iff specializes[t',t]))
}

/**	Axiom A12 - Categorization Definition: a type t1 categorizes a type t2 iff all
	instances of t1 are proper specializations of t2. */
fact categorizationDefinition {
	all t1,t2: Type | categorizes[t1,t2] iff iof.t1 in properSpecializes.t2
}

/**	Axiom A13 - Complete Categorization Definition: a type t1 completely categorizes
	a type t2 iff t1 categorizes t2 and for every instance of t2 there is some type
	that is instantiated by it and is instance of t1. */
fact completeCategorizationDefinition {
	all t1,t2: Type | compCategorizes[t1,t2] iff (categorizes[t1,t2] and (all e: iof.t2 | some e.iof & iof.t1))
}

/** Axiom A14 - Disjoint Categorization Definition: a type t1 disjointly categorizes
	a type t2 iff t1 categorizes t2 and for any pair of different types that are
	instances of t1 implies this pair has disjoint extensions. */
fact disjointCategorizationDefinition {
	all t1,t2: Type | disjCategorizes[t1,t2] iff (categorizes[t1,t2] and (all t3,t4: iof.t1 | t3 != t4 implies disjoint_[iof.t3,iof.t4]))
}

/**	Axiom A15 - Partitions Definition: a type t1 partitions a type t2 iff t1 disjointly
	categorizes t2 and t1 completely categorizes t2. */
fact partitionsDefinition {
	all t1,t2: Entity | partitions[t1,t2] iff (disjCategorizes[t1,t2] and compCategorizes[t1,t2])
}

/********************************************************************************************
* USEFUL CONSTRAINTS
* Some constraints for cutting out unwanted models.
********************************************************************************************/

fact allEntitiesConnectedByInstantiation {
	let navigableiof = iof + ~iof | all x,y: Entity | (x in y.*navigableiof)
}

fact someIndividuals {
	some e: Entity | no iof.e
}

fact someBasicTypes {
	some BasicType
}

/********************************************************************************************
* NOTABLE CONSTANTS
* Signatures to represent the most used Ordered Types.
********************************************************************************************/

sig Order1Type in OrderedType {
}

fact Order1TypeDefinition {
	all e: Entity | (e in Order1Type iff (some b: BasicType,f: Individual_ | iof[e,b] and powertypeOf[b,f]))
}

one sig Order1TypeReified in OrderedType {
}

fact Order1TypeReifiedDefinition {
	all e: Entity | e in Order1TypeReified iff (all e': Entity | iof[e',e] iff e' in Order1Type)
}

sig Order2Type in OrderedType {
}

fact Order2TypeDefinition {
	all e: Entity | (e in Order2Type iff (some b: BasicType,f: Order1TypeReified | iof[e,b] and powertypeOf[b,f]))
}

one sig Order2TypeReified in OrderedType {
}

fact Order2TypeReifiedDefinition {
	all e: Entity | e in Order2TypeReified iff (all e': Entity | iof[e',e] iff e' in Order2Type)
}

sig Order3Type in OrderedType {
}

fact Order3TypeDefinition {
	all e: Entity | (e in Order3Type iff (some b: BasicType,f: Order2TypeReified | iof[e,b] and powertypeOf[b,f]))
}

one sig Order3TypeReified in OrderedType {
}

fact Order3TypeReifiedDefinition {
	all e: Entity | e in Order3TypeReified iff (all e': Entity | iof[e',e] iff e' in Order3Type)
}

