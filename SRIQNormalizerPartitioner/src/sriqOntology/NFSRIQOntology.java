package sriqOntology;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.io.FileOutputStream;
import java.io.FileNotFoundException;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLFunctionalSyntaxOntologyFormat;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLSubObjectPropertyOfAxiomImpl;
import center.Srd;

public class NFSRIQOntology {

	// A1 sqcap ... sqcap An sqs B, A sqs B1 sqcup ... sqcup Bn, A sqs forall R.B, A sqs leq n R.B, A sqs geq n R.B 
	private ArrayList<OWLSubClassOfAxiom> intDisjAxioms = new ArrayList<OWLSubClassOfAxiom>();;
	private ArrayList<OWLSubClassOfAxiom> univAxioms = new ArrayList<OWLSubClassOfAxiom>();;
	private ArrayList<OWLSubClassOfAxiom> minCardAxioms = new ArrayList<OWLSubClassOfAxiom>();;
	private ArrayList<OWLSubClassOfAxiom> maxCardAxioms = new ArrayList<OWLSubClassOfAxiom>();;

	// R sqs S, R o V sqs S
	private ArrayList<OWLSubObjectPropertyOfAxiom> roleInclusionAxioms = new ArrayList<OWLSubObjectPropertyOfAxiom>();
	private ArrayList<OWLSubPropertyChainOfAxiom> complexRoleInclusionAxioms = new ArrayList<OWLSubPropertyChainOfAxiom>();

	// C(a), R(a, b), {ai} = {aj}, {ai} != {aj}
	private ArrayList<OWLClassAssertionAxiom> conceptAssertionAxioms = new ArrayList<OWLClassAssertionAxiom>();
	private ArrayList<OWLObjectPropertyAssertionAxiom> roleAssertionAxioms = new ArrayList<OWLObjectPropertyAssertionAxiom>();
	private ArrayList<OWLSameIndividualAxiom> sameIndividualAxioms = new ArrayList<OWLSameIndividualAxiom>();
	private ArrayList<OWLDifferentIndividualsAxiom> differentIndividualAxioms = new ArrayList<OWLDifferentIndividualsAxiom>();

	public NFSRIQOntology(Set<OWLSubClassOfAxiom> normalizedAxioms, Collection<OWLObjectPropertyExpression[]> m_simpleObjectPropertyInclusions,
				Set<OWLSubPropertyChainOfAxiom> complexPropertyInclusions, Set<OWLIndividualAxiom> m_facts) {

		initializeTBoxAxioms(normalizedAxioms);

		for (OWLObjectPropertyExpression[] simpleRIA : m_simpleObjectPropertyInclusions)
			roleInclusionAxioms.add(new OWLSubObjectPropertyOfAxiomImpl(simpleRIA[0], simpleRIA[1], new HashSet<OWLAnnotation>()));
		complexRoleInclusionAxioms.addAll(complexPropertyInclusions);

		initializeABoxAxioms(m_facts);
	}

	private void initializeTBoxAxioms(Set<OWLSubClassOfAxiom> normalizedAxioms) {

		// A1 sqcap ... sqcap An sqs B,  A sqs B1 sqcup ... sqcup Bn, A sqs forall R.B, A sqs leq n R.B, A sqs geq n R.B
		for (OWLSubClassOfAxiom axiom : normalizedAxioms) {
			OWLClassExpression subClass = axiom.getSubClass();
			OWLClassExpression superClass = axiom.getSuperClass();

			if ((subClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_INTERSECTION_OF)
						|| subClass.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS) || subClass.isOWLThing())
						&& (superClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_UNION_OF)
									|| superClass.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS) || superClass.isOWLNothing())) {

				if (subClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_INTERSECTION_OF))
					for (OWLClassExpression conjunct : subClass.asConjunctSet())
						if (!conjunct.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS))
							System.out.println("WARNING!!! Unrecognized OBJECT_INTERSECTION_OF subclass at initializeTBoxAxioms at NFSRIQOntology.java" + "\n" + " -> " + axiom
										+ " -> " + subClass.getClassExpressionType() + "\n -> " + subClass + "\n");

				if (subClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_UNION_OF))
					for (OWLClassExpression disjunct : superClass.asDisjunctSet())
						if (!disjunct.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS))
							System.out.println("WARNING!!! Unrecognized OBJECT_UNION_OF subclass at initializeTBoxAxioms at NFSRIQOntology.java" + "\n" + " -> " + axiom + " -> "
										+ superClass.getClassExpressionType() + "\n -> " + superClass + "\n");

				intDisjAxioms.add(axiom);

			} else if (subClass.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)) {

				switch (Srd.conceptTypeToString(superClass)) {
				case Srd.allValuesFrom + Srd.className:
				case Srd.allValuesFrom + Srd.bottom:
					// A sqs forall R.B
					univAxioms.add(axiom);
					break;
				case Srd.maxCardinality + Srd.className:
				case Srd.maxCardinality + Srd.top:
					// A sqs < n R.B
					maxCardAxioms.add(axiom);
					break;
				case Srd.minCardinality + Srd.className:
				case Srd.minCardinality + Srd.top:
					// A sqs > n R.B
					minCardAxioms.add(axiom);
					break;
				default:
					System.out.println("WARNING!!! Unrecognized superClass ClassExpressionType at initializeAxioms at NFSRIQOntology.java" + "\n" + " -> " + axiom + "\n" + " -> "
								+ superClass.getClassExpressionType() + "\n -> " + superClass + "\n");
					break;
				}

			} else
				System.out.println("WARNING!!! Unrecognized type of axiom at initializeTBoxAxioms at NFSRIQOntology.java" + "\n" + " -> " + axiom + "\n");

		}
	}

	private void initializeABoxAxioms(Collection<OWLIndividualAxiom> m_facts) {

		// C(a), R(a, b), {a1} equiv ... equiv {an}, {ai} sqcap {aj} sqs \bot
		for (OWLIndividualAxiom fact : m_facts) {
			switch (fact.getAxiomType().toString()) {
			case "ClassAssertion":
				// C(a)
				OWLClassExpression classExpression = ((OWLClassAssertionAxiom) fact).getClassExpression();
				if (Srd.conceptTypeToString(classExpression) == Srd.className)
					//A(a)
					conceptAssertionAxioms.add((OWLClassAssertionAxiom) fact);
				else
					System.out.println("WARNING!!! Illegal assertion at NFSRIQOntology.java: " + fact.getAxiomType() + "\n" + fact);
				break;
			case "ObjectPropertyAssertion":
				// R(a, b)
				roleAssertionAxioms.add((OWLObjectPropertyAssertionAxiom) fact);
				break;
			case "SameIndividual":
				// {ai} = {aj}
				sameIndividualAxioms.add((OWLSameIndividualAxiom) fact);
				break;
			case "DifferentIndividuals":
				// {ai} != {aj}
				differentIndividualAxioms.add((OWLDifferentIndividualsAxiom) fact);
				break;
			default:
				System.out.println("WARNING!!! Unrecognized OWLIndividualAxiom type at NFSRIQOntology.java: " + fact.getAxiomType());
				break;
			}
		}
	}

	public void toFile(String filePath) throws OWLOntologyCreationException, FileNotFoundException, OWLOntologyStorageException {

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology normalizedOntology = manager.createOntology();

		// TBox
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(intDisjAxioms));
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(minCardAxioms));
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(univAxioms));
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(maxCardAxioms));

		// RBox
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(roleInclusionAxioms));
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(complexRoleInclusionAxioms));

		// ABox
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(conceptAssertionAxioms));
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(roleAssertionAxioms));
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(sameIndividualAxioms));
		manager.addAxioms(normalizedOntology, new HashSet<OWLAxiom>(differentIndividualAxioms));

		manager.saveOntology(normalizedOntology, new OWLFunctionalSyntaxOntologyFormat(), new FileOutputStream(filePath));
	}

	public int getTBoxSize() {
		return intDisjAxioms.size() + univAxioms.size() + minCardAxioms.size() + maxCardAxioms.size();
	}

	public int getRBoxSize() {
		return roleInclusionAxioms.size() + complexRoleInclusionAxioms.size();
	}

	public int getABoxSize() {
		return conceptAssertionAxioms.size() + roleAssertionAxioms.size() + sameIndividualAxioms.size() + differentIndividualAxioms.size();
	}
	
	//Added by Sambhawa
	public ArrayList<OWLSubObjectPropertyOfAxiom> getRoleInclusionAxioms(){
		
		return roleInclusionAxioms;
	}
	
	//Added by Sambhawa
	public ArrayList<OWLSubPropertyChainOfAxiom> getComplexRoleInclusionAxioms(){
		
		return complexRoleInclusionAxioms;
	}
	
	//Added by Sambhawa
	public ArrayList<OWLSubClassOfAxiom> getUnivAxioms(){
		return univAxioms;
	}
	
	//Added by Sambhawa
	public ArrayList<OWLSubClassOfAxiom> getMinCardAxioms(){
		return minCardAxioms;
	}

	//Added by Sambhawa
	public ArrayList<OWLSubClassOfAxiom> getMaxCardAxioms(){
		return maxCardAxioms;
	}

	
	//Added by Sambhawa
	public ArrayList<OWLObjectPropertyAssertionAxiom> getRoleAssertionAxioms(){
		return roleAssertionAxioms;
	}
	
	//Added by Sambhawa
	public ArrayList<OWLClassAssertionAxiom> getConceptAssertionAxioms(){
		return conceptAssertionAxioms;
	}
}
