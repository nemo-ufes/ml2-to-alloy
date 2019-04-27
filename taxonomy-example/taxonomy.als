module taxonomy
open MLTStar
open utils

sig TaxonomicRank in Order2Type {
}

one sig TaxonomicRankReified in Order3Type {
}

fact TaxonomicRankReifiedDefinition {
	all e: Entity | e in TaxonomicRankReified iff (all e': Entity | iof[e',e] iff e' in TaxonomicRank)
}

sig Taxon in Order1Type {
	taxonAuthor: Person
}

one sig TaxonReified in Order2Type {
}

fact TaxonReifiedDefinition {
	all e: Entity | e in TaxonReified iff (all e': Entity | iof[e',e] iff e' in Taxon)
}

sig Species in Taxon {
	population: Int,
	status: String
}

one sig SpeciesReified in TaxonomicRank {
}

fact SpeciesReifiedDefinition {
	all e: Entity | e in SpeciesReified iff (all e': Entity | iof[e',e] iff e' in Species)
}

sig AnimalSpecies in Species {
	instancesAreWarmblooded: Boolean
}

one sig AnimalSpeciesReified in Order2Type {
}

fact AnimalSpeciesCategorizesAnimal {
	categorizes[AnimalSpeciesReified,AnimalReified]
}

fact AnimalSpeciesReifiedDefinition {
	all e: Entity | e in AnimalSpeciesReified iff (all e': Entity | iof[e',e] iff e' in AnimalSpecies)
}

sig Organism in Individual {
	weight: Int
}

one sig OrganismReified in Order1Type {
}

fact OrganismReifiedDefinition {
	all e: Entity | e in OrganismReified iff (all e': Entity | iof[e',e] iff e' in Organism)
}

sig Person in Individual {
	name: String
}

one sig PersonReified in Order1Type {
}

fact PersonReifiedDefinition {
	all e: Entity | e in PersonReified iff (all e': Entity | iof[e',e] iff e' in Person)
}

sig Animal in Organism {
	isWarmblooded: Boolean
}

one sig AnimalReified in Species {
}

fact AnimalReifiedDefinition {
	all e: Entity | e in AnimalReified iff (all e': Entity | iof[e',e] iff e' in Animal)
}

sig Lion in Animal {
}

one sig LionReified in AnimalSpecies {
}{	instancesAreWarmblooded = true
	taxonAuthor = CarlLinnaeus
}

fact LionReifiedDefinition {
	all e: Entity | e in LionReified iff (all e': Entity | iof[e',e] iff e' in Lion)
}

fact instancesAreWarmbloodedRegulatesisWarmblooded {
	all x: Lion | x.isWarmblooded = LionReified.instancesAreWarmblooded
}

one sig Cecil in Lion {
}

one sig CarlLinnaeus in Person {
}{	name = "Carl Linnaeus"
}

fact disjointIndividuals {
	disjoint[Cecil,CarlLinnaeus]
}
