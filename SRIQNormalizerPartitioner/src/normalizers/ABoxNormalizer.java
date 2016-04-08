package normalizers;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import center.Srd;

public class ABoxNormalizer {

	// private static OWLDataFactory factory = OWLManager.createOWLOntologyManager().getOWLDataFactory();

	static int newConceptCounter = 0;

	// private static String newConceptString = "intDefABox";

	public static Set<OWLIndividualAxiom> normalizeAssertions(Set<OWLSubClassOfAxiom> normalizedConceptInclusions, Collection<OWLIndividualAxiom> hermiTAssertions) {

		Set<OWLIndividualAxiom> normalizedAssertions = new HashSet<OWLIndividualAxiom>();

		// lnot A(a) -> X(a), X sqcap A sqs Bot
		for (OWLIndividualAxiom assertion : hermiTAssertions)
			switch (assertion.getAxiomType().toString()) {

			case "ClassAssertion":
				OWLClassAssertionAxiom classAssertion = (OWLClassAssertionAxiom) assertion;
				OWLClassExpression classExpression = classAssertion.getClassExpression();
				switch (Srd.conceptTypeToString(classExpression)) {
				case Srd.className:
					normalizedAssertions.add(assertion);
					break;
				case Srd.top:
					break;
				case Srd.complementOf + Srd.className:

					// OWLClass freshConceptX = factory.getOWLClass(IRI.create(newConceptString + Integer.toString(++newConceptCounter)));
					// Set<OWLClassExpression> conjuncts = new HashSet<OWLClassExpression>();

					// normalizedAssertions.add(new OWLClassAssertionAxiomImpl(classAssertion.getIndividual(), freshConceptX, new HashSet<OWLAnnotation>()));					
					// conjuncts.add(freshConceptX);
					// conjuncts.add(classExpression.getComplementNNF());
					// normalizedConceptInclusions.add(new OWLSubClassOfAxiomImpl(new OWLObjectIntersectionOfImpl(conjuncts), factory.getOWLNothing(), new HashSet<OWLAnnotation>()));
					break;
				default:
					System.out.println("Unrecognized type of Class Expression at ABoxNormalizer.java:" + "\t" + assertion.getAxiomType().toString() + "\n" + " -> "
								+ assertion.toString());
					break;
				}
				break;

			case "ObjectPropertyAssertion":
			case "SameIndividual":
			case "DifferentIndividuals":
				normalizedAssertions.add(assertion);
				break;
			default:
				System.out.println("WARNING!!! Unrecognized type of ABox Axiom at ABoxNormalizer.java:" + "\t" + assertion.getAxiomType().toString() + "\n" + " -> "
							+ assertion.toString());
			}

		return normalizedAssertions;
	}
}
