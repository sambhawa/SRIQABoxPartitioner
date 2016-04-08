package normalizers;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.HermiT.structural.OWLAxioms;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLObjectAllValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectMaxCardinalityImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectMinCardinalityImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectUnionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLSubClassOfAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;

import org.semanticweb.owlapi.model.OWLAnnotation;

import center.Srd;

public class TBoxNormalizer {

	private static OWLDataFactory factory = OWLManager.createOWLOntologyManager().getOWLDataFactory();

	private static int newConceptCounter = 0;
	private static String newConceptConjString = "intDefConj";
	private static String newConceptDisjString = "intDefDisj";
	private static String newConceptSplitString = "intDefSplit";
	private static String newConceptNormString = "intDefNorm";

	public static Set<OWLSubClassOfAxiom> normalizeConceptInclusions(OWLAxioms dataFilteredAxioms) {

		Set<OWLSubClassOfAxiom> owlAPIAxioms = hermitToOWLAPI(dataFilteredAxioms.m_conceptInclusions);

		Set<OWLSubClassOfAxiom> normalizedConjunctionAxioms = new HashSet<OWLSubClassOfAxiom>();
		for (OWLSubClassOfAxiom axiom : owlAPIAxioms) {
			// C1 sqcap ... sqcap Cn sqs D -> C1 sqs X1, ..., Cn sqs Xn, X1 sqcap ... sqcap Xn sqs D
			OWLClassExpression subClass = axiom.getSubClass();

			if (!subClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_INTERSECTION_OF))
				normalizedConjunctionAxioms.add(axiom);
			else {
				Set<OWLClassExpression> newSubClassConjuncts = new HashSet<OWLClassExpression>();

				for (OWLClassExpression originalSubClassConjunct : subClass.asConjunctSet())
					if (originalSubClassConjunct.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS))
						newSubClassConjuncts.add(originalSubClassConjunct);
					else {
						OWLClassExpression freshClassX = factory.getOWLClass(IRI.create(newConceptConjString + Integer.toString(++newConceptCounter)));
						normalizedConjunctionAxioms.add(new OWLSubClassOfAxiomImpl(originalSubClassConjunct, freshClassX, new HashSet<OWLAnnotation>()));
						newSubClassConjuncts.add(freshClassX);
					}
				normalizedConjunctionAxioms.add(new OWLSubClassOfAxiomImpl(new OWLObjectIntersectionOfImpl(newSubClassConjuncts), axiom.getSuperClass(),
							new HashSet<OWLAnnotation>()));
			}
		}
		owlAPIAxioms = null;

		Set<OWLSubClassOfAxiom> normalizedDisjunctionAxioms = new HashSet<OWLSubClassOfAxiom>();
		for (OWLSubClassOfAxiom axiom : normalizedConjunctionAxioms) {
			// C sqs D1 sqcup ... Dn -> C sqs X1 sqcup ... sqcup Xn, X1 sqs D1, ... Xn sqs Dn 
			OWLClassExpression superClass = axiom.getSuperClass();

			if (!superClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_UNION_OF))
				normalizedDisjunctionAxioms.add(axiom);
			else {
				Set<OWLClassExpression> newSuperClassDisjuncts = new HashSet<OWLClassExpression>();

				for (OWLClassExpression originalSuperClassDisjunct : superClass.asDisjunctSet())
					if (originalSuperClassDisjunct.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS))
						newSuperClassDisjuncts.add(originalSuperClassDisjunct);
					else {
						OWLClassExpression freshClassX = factory.getOWLClass(IRI.create(newConceptDisjString + Integer.toString(++newConceptCounter)));
						normalizedDisjunctionAxioms.add(new OWLSubClassOfAxiomImpl(freshClassX, originalSuperClassDisjunct, new HashSet<OWLAnnotation>()));
						newSuperClassDisjuncts.add(freshClassX);
					}
				normalizedDisjunctionAxioms.add(new OWLSubClassOfAxiomImpl(axiom.getSubClass(), new OWLObjectUnionOfImpl(newSuperClassDisjuncts), new HashSet<OWLAnnotation>()));
			}
		}
		normalizedConjunctionAxioms = null;

		Set<OWLSubClassOfAxiom> splitAxioms = new HashSet<OWLSubClassOfAxiom>();
		for (OWLSubClassOfAxiom owlAPIAxiom : normalizedDisjunctionAxioms) {
			// C sqs D -> C sqs X, X sqs D
			OWLClassExpression subClass = owlAPIAxiom.getSubClass();
			OWLClassExpression superClass = owlAPIAxiom.getSuperClass();

			if (subClass.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)
						|| superClass.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)
						|| (subClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_INTERSECTION_OF) && superClass.getClassExpressionType().equals(
									ClassExpressionType.OBJECT_UNION_OF)))
				splitAxioms.add(owlAPIAxiom);
			else {
				OWLClass freshClassX = factory.getOWLClass(IRI.create(newConceptSplitString + Integer.toString(++newConceptCounter)));
				splitAxioms.add(new OWLSubClassOfAxiomImpl(subClass, freshClassX, new HashSet<OWLAnnotation>()));
				splitAxioms.add(new OWLSubClassOfAxiomImpl(freshClassX, superClass, new HashSet<OWLAnnotation>()));
			}
		}
		normalizedDisjunctionAxioms = null;

		Set<OWLSubClassOfAxiom> normalizedConceptInclusions = new HashSet<OWLSubClassOfAxiom>();
		for (OWLSubClassOfAxiom axiom : splitAxioms) {
			OWLClassExpression subClass = axiom.getSubClass();
			OWLClassExpression superClass = axiom.getSuperClass();

			if (Srd.conceptTypeToString(superClass).equals(Srd.minCardinality + Srd.complementOf + Srd.className)) {
				// A sqs > n R. lnot B -> A sqs > n R.X, X sqcap B sqs Bot

				OWLObjectMinCardinality minCardSuperClassRnotB = (OWLObjectMinCardinality) superClass;
				OWLClassExpression freshClassX = factory.getOWLClass(IRI.create(newConceptNormString + Integer.toString(++newConceptCounter)));
				OWLObjectMinCardinality freshMinCardSuperClassRX = new OWLObjectMinCardinalityImpl(minCardSuperClassRnotB.getProperty(), minCardSuperClassRnotB.getCardinality(),
							freshClassX);

				Set<OWLClassExpression> newSubClassDisjointConjuncts = new HashSet<OWLClassExpression>();
				newSubClassDisjointConjuncts.add(freshClassX);
				newSubClassDisjointConjuncts.add(minCardSuperClassRnotB.getFiller().getComplementNNF());

				normalizedConceptInclusions.add(new OWLSubClassOfAxiomImpl(subClass, freshMinCardSuperClassRX, new HashSet<OWLAnnotation>()));
				normalizedConceptInclusions.add(new OWLSubClassOfAxiomImpl(new OWLObjectIntersectionOfImpl(newSubClassDisjointConjuncts), factory.getOWLNothing(),
							new HashSet<OWLAnnotation>()));

			} else if (Srd.conceptTypeToString(superClass).equals(Srd.maxCardinality + Srd.complementOf + Srd.className)) {
				// A sqs < n R. lnot B -> A sqs < n R.X, Top sqs B sqcup X

				OWLObjectMaxCardinality maxCardSuperClassRnotB = (OWLObjectMaxCardinality) superClass;
				OWLClassExpression freshClassX = factory.getOWLClass(IRI.create(newConceptNormString + Integer.toString(++newConceptCounter)));
				OWLObjectMaxCardinality freshMaxCardSuperClassRX = new OWLObjectMaxCardinalityImpl(maxCardSuperClassRnotB.getProperty(), maxCardSuperClassRnotB.getCardinality(),
							freshClassX);

				Set<OWLClassExpression> newSuperClassDisjuncts = new HashSet<OWLClassExpression>();
				newSuperClassDisjuncts.add(maxCardSuperClassRnotB.getFiller().getComplementNNF());
				newSuperClassDisjuncts.add(freshClassX);

				normalizedConceptInclusions.add(new OWLSubClassOfAxiomImpl(subClass, freshMaxCardSuperClassRX, new HashSet<OWLAnnotation>()));
				normalizedConceptInclusions
							.add(new OWLSubClassOfAxiomImpl(factory.getOWLThing(), new OWLObjectUnionOfImpl(newSuperClassDisjuncts), new HashSet<OWLAnnotation>()));

			} else if (Srd.conceptTypeToString(subClass).equals(Srd.minCardinality + Srd.className) || Srd.conceptTypeToString(subClass).equals(Srd.minCardinality + Srd.top)) {
				// > 1 R.A sqs B -> A sqs forall Inv(R).B

				OWLObjectMinCardinality minSubClassRA = (OWLObjectMinCardinality) subClass;

				if (minSubClassRA.getCardinality() == 1) {
					OWLObjectAllValuesFrom univSuperClassInvRB = new OWLObjectAllValuesFromImpl(Srd.invert(minSubClassRA.getProperty()), superClass);
					normalizedConceptInclusions.add(new OWLSubClassOfAxiomImpl(minSubClassRA.getFiller(), univSuperClassInvRB, new HashSet<OWLAnnotation>()));
				} else
					System.out.println("WARNING!!! Invalid Axiom at normalizeConceptInclusions at TBoxNormalizer: " + axiom);

			} else
				normalizedConceptInclusions.add(axiom);
		}
		splitAxioms = null;

		return normalizedConceptInclusions;
	}

	// Top sqs D1 sqcup ... sqcup Dn -> C1 sqcap ... sqcap Cn sqs D
	private static Set<OWLSubClassOfAxiom> hermitToOWLAPI(Collection<OWLClassExpression[]> m_conceptInclusions) {

		Set<OWLSubClassOfAxiom> owlAPIAxioms = new HashSet<OWLSubClassOfAxiom>();

		for (OWLClassExpression[] dataFilteredAxiom : m_conceptInclusions) {
			Set<OWLClassExpression> subClassConjuncts = new HashSet<OWLClassExpression>();
			Set<OWLClassExpression> superClassDisjuncts = new HashSet<OWLClassExpression>();
			boolean sriqAxiom = true;

			for (OWLClassExpression conceptExpression : dataFilteredAxiom)
				switch (Srd.conceptTypeToString(conceptExpression)) {

				case Srd.complementOf + Srd.className:
					// lnot A
					subClassConjuncts.add(conceptExpression.getComplementNNF());
					break;

				case Srd.allValuesFrom + Srd.bottom:
					// forall R.Bot
					OWLObjectAllValuesFrom univExperssion1 = (OWLObjectAllValuesFrom) conceptExpression;
					subClassConjuncts.add(new OWLObjectMinCardinalityImpl(univExperssion1.getProperty(), 1, factory.getOWLThing()));
					break;
				case Srd.allValuesFrom + Srd.complementOf + Srd.className:
					// forall R. lnot A
					OWLObjectAllValuesFrom univExperssion2 = (OWLObjectAllValuesFrom) conceptExpression;
					subClassConjuncts.add(new OWLObjectMinCardinalityImpl(univExperssion2.getProperty(), 1, univExperssion2.getFiller().getComplementNNF()));
					break;

				case Srd.className:
					// A
				case Srd.allValuesFrom + Srd.className:
					// forall R.A
				case Srd.minCardinality + Srd.top:
					// > n R.Top
				case Srd.minCardinality + Srd.className:
					// > n R.A
				case Srd.minCardinality + Srd.complementOf + Srd.className:
					// > n R. lnot A
				case Srd.maxCardinality + Srd.top:
					// < n R.Top
				case Srd.maxCardinality + Srd.className:
					// < n R.A
				case Srd.maxCardinality + Srd.complementOf + Srd.className:
					// < n R. lnot A
					superClassDisjuncts.add(conceptExpression);
					break;

				case Srd.someValuesFrom + Srd.className:
					// exists R.A
				case Srd.someValuesFrom + Srd.top:
					// exists R.Top
				case Srd.someValuesFrom + Srd.complementOf + Srd.className:
					// exists R. lnot A
					OWLObjectSomeValuesFrom existExpression = (OWLObjectSomeValuesFrom) conceptExpression;
					superClassDisjuncts.add(new OWLObjectMinCardinalityImpl(existExpression.getProperty(), 1, existExpression.getFiller()));
					break;

				case Srd.singleOneOf:
					// {a}
				case Srd.multipleObjectOneOf:
					// {a1} sqcup ... sqcup {an}
				case Srd.someValuesFrom + Srd.singleOneOf:
					// exists R.{a}
				case Srd.someValuesFrom + Srd.multipleObjectOneOf:
					// exists R.({a1} sqcup ... sqcup {an})
				case Srd.allValuesFrom + Srd.singleOneOf:
					// forall R.{a}
				case Srd.allValuesFrom + Srd.multipleObjectOneOf:
					// forall R.({a1} sqcup ... sqcup {an})
				case Srd.allValuesFrom + Srd.complementOf + Srd.singleOneOf:
					// forall R. lnot {a}
				case Srd.allValuesFrom + Srd.complementOf + Srd.multipleObjectOneOf:
					// forall R. lnot ({a1} sqcup ... sqcup {an})
				case Srd.hasSelf:
					// exists R.Self
				case Srd.complementOf + Srd.hasSelf:
					// lnot exists R.Self
					sriqAxiom = false;
					break;

				default:
					System.out.println("WARNING!!! Unrecognized concept expression at hermitToOWLAPI at TBoxNormalizer.java");
					System.out.println(" -> " + conceptExpression + "\n" + " -> " + conceptExpression.getClassExpressionType() + "\n");
					break;
				}

			// Top sqs D1 sqcup ... sqcup Dn
			if (subClassConjuncts.isEmpty())
				subClassConjuncts.add(OWLManager.createOWLOntologyManager().getOWLDataFactory().getOWLThing());

			// C1 sqcap ... sqcap Cn sqs Bot
			if (superClassDisjuncts.isEmpty())
				superClassDisjuncts.add(OWLManager.createOWLOntologyManager().getOWLDataFactory().getOWLNothing());

			OWLClassExpression subClassExpression;
			if (subClassConjuncts.size() == 1)
				subClassExpression = subClassConjuncts.iterator().next();
			else
				subClassExpression = new OWLObjectIntersectionOfImpl(subClassConjuncts);

			OWLClassExpression superClassExpression;
			if (superClassDisjuncts.size() == 1)
				superClassExpression = superClassDisjuncts.iterator().next();
			else
				superClassExpression = new OWLObjectUnionOfImpl(superClassDisjuncts);

			if (sriqAxiom)
				owlAPIAxioms.add(new OWLSubClassOfAxiomImpl(subClassExpression, superClassExpression, new HashSet<OWLAnnotation>()));
		}

		return owlAPIAxioms;
	}
}
