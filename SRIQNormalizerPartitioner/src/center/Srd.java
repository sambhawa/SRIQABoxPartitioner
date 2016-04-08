package center;

import java.io.File;

import org.semanticweb.HermiT.structural.OWLAxioms.ComplexObjectPropertyInclusion;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

public class Srd {

	public final static String top = "Top";
	public final static String bottom = "Bottom";
	public final static String className = "Class";
	public final static String singleOneOf = "OneOfSingle";
	public final static String multipleObjectOneOf = "ObjectOneOfSeveral";
	public final static String hasSelf = "HasSelf";
	public final static String complementOf = "ComplementOf";
	public final static String someValuesFrom = "SomeValuesFrom";
	public final static String allValuesFrom = "AllValuesFrom";
	public final static String minCardinality = "MinCardinality";
	public final static String maxCardinality = "MaxCardinality";
	public final static String intersectionOf = "IntersectionOf";
	public final static String unionOf = "UnionOf";

	// File I/O //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static OWLOntology loadOntology(String ontologyFilePath) {
		return loadOntology(new File(ontologyFilePath));
	}

	public static OWLOntology loadOntology(File ontologyFile) {
		OWLOntology ontology = null;
		try {
			ontology = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(ontologyFile);
		} catch (OWLOntologyCreationException e) {
			System.out.println("WARNING!!! Error loading ontology." + "\n" + " -> " + ontologyFile + "\n\n" + e);
		}
		return ontology;
	}

	public static void deleteDirectory(String path) {
		deleteDirectory(new File(path));
	}

	public static boolean deleteDirectory(File file) {
		if (file.exists()) {
			File[] files = file.listFiles();
			for (int i = 0; i < files.length; i++)
				if (files[i].isDirectory())
					deleteDirectory(files[i]);
				else
					files[i].delete();
		}
		return (file.delete());
	}

	// Concept and role expression types /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static String conceptTypeToString(OWLClassExpression conceptExpression) {

		switch (conceptExpression.getClassExpressionType().toString()) {

		case "Class":
			if (conceptExpression.isOWLThing())
				return top;
			else if (conceptExpression.isOWLNothing())
				return bottom;
			else
				return className;

		case "ObjectOneOf":
			OWLObjectOneOf nominalsConceptExpression = (OWLObjectOneOf) conceptExpression;
			if (nominalsConceptExpression.getIndividuals().size() == 1)
				return singleOneOf;
			else
				return multipleObjectOneOf;

		case "ObjectHasSelf":
			return hasSelf;

		case "ObjectComplementOf":
			OWLObjectComplementOf negatedConceptExpression = (OWLObjectComplementOf) conceptExpression;
			return complementOf + conceptTypeToString(negatedConceptExpression.getOperand());

		case "ObjectAllValuesFrom":
			OWLObjectAllValuesFrom univConceptExpression = (OWLObjectAllValuesFrom) conceptExpression;
			return allValuesFrom + conceptTypeToString(univConceptExpression.getFiller());

		case "ObjectSomeValuesFrom":
			OWLObjectSomeValuesFrom existsConceptExpression = (OWLObjectSomeValuesFrom) conceptExpression;
			return someValuesFrom + conceptTypeToString(existsConceptExpression.getFiller());

		case "ObjectMaxCardinality":
			OWLObjectMaxCardinality maxCardinalityConceptExpression = (OWLObjectMaxCardinality) conceptExpression;
			return maxCardinality + conceptTypeToString(maxCardinalityConceptExpression.getFiller());

		case "ObjectMinCardinality":
			OWLObjectMinCardinality minCardinalityConceptExpression = (OWLObjectMinCardinality) conceptExpression;
			return minCardinality + conceptTypeToString(minCardinalityConceptExpression.getFiller());

		case "ObjectIntersectionOf":
			return intersectionOf;

		case "ObjectUnionOf":
			return unionOf;

		}

		System.out.println("WARNING!!! Unrecognized concept expression type at Srd. java.");
		System.out.println("\n ->" + conceptExpression + "\n ->" + conceptExpression.getClassExpressionType() + "\n");
		return "UnrecognizedConcept";
	}

	public static int getABoxAxiomIndex(OWLIndividualAxiom fact) {

		// C(a)
		if (fact.isOfType(AxiomType.CLASS_ASSERTION))
			return 1;

		// R(a, b)
		if (fact.isOfType(AxiomType.OBJECT_PROPERTY_ASSERTION))
			return 2;

		return 1143;
	}

	public static boolean isInverse(String role) {
		return (role.contains("InverseOf"));
	}

	public static OWLObjectPropertyExpression invert(OWLObjectPropertyExpression role) {
		if (isInverse(role.toString()))
			return role.getNamedProperty();
		else
			return role.getInverseProperty();
	}

	public static String invert(String role) {
		if (role.contains("InverseOf"))
			return role.substring(10, role.length() - 1);
		else
			return "InverseOf(" + role + ")";
	}

	// String Formatting and Visualization	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static String filterNonAlphaNumericalSymbols(String name) {
		return "p"
					+ name.replace("<", "a").replace(">", "b").replace(":", "c").replace("/", "d").replace("-", "e").replace(".", "f").replace("?", "g").replace("#", "h")
								.replace("~", "i").replace("_", "j").replace("%", "k").replace("+", "l").replace("(", "m").replace(")", "n").replace(" ", "o");
	}

	public static String hermitGCIToString(OWLClassExpression[] conceptInclusion) {
		String formattedString = new String("Top sqsubseteq ");
		String operator = new String(" sqcup ");

		for (OWLClassExpression conceptExpression : conceptInclusion)
			formattedString += conceptExpression + operator;

		return formattedString.substring(0, formattedString.length() - operator.length());
	}

	public static String hermitComplexPropertyInclusionToString(ComplexObjectPropertyInclusion complexRoleInclusion) {
		String complexRoleInclusionString = new String();
		String operator = " o ";

		for (OWLObjectPropertyExpression subProperty : complexRoleInclusion.m_subObjectProperties)
			complexRoleInclusionString += subProperty.toString() + operator;

		return complexRoleInclusionString.substring(0, complexRoleInclusionString.length() - operator.length()) + " sqsubseteq "
					+ complexRoleInclusion.m_superObjectProperty.toString();
	}

}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////