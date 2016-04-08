package DataStructure;

import java.util.Set;

import org.semanticweb.owlapi.model.OWLIndividual;

public class Tuple {
	
	Set<OWLIndividual> individuals; //the set of connected individuals
	int assertionCount; // count of ABox assertions corresponding to the individuals in the set of connected individuals
	
	public Tuple(Set<OWLIndividual> connIndSet, int count) {
		this.individuals = connIndSet;
		this.assertionCount = count;
	}
	
	public int getAssertionCount(){
		
		return this.assertionCount;
	}
	
	public Set<OWLIndividual> getconnectedIndividuals(){
		
		return this.individuals;
	}
	
	public void incAssertionCountByOne() {
		this.assertionCount+=1;
		
	}

}
