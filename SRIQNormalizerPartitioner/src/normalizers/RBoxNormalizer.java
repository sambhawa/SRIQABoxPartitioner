package normalizers;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.HermiT.structural.OWLAxioms.ComplexObjectPropertyInclusion;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLSubPropertyChainAxiomImpl;

public class RBoxNormalizer {

	private static int newRoleCounter = 0;
	private static String newRoleString = "intDefRole";
	private static OWLDataFactory factory = OWLManager.createOWLOntologyManager().getOWLDataFactory();

	public static Set<OWLSubPropertyChainOfAxiom> normalizeComplexRIAs(Collection<ComplexObjectPropertyInclusion> originalComplexRIAs) {

		Set<OWLSubPropertyChainOfAxiom> normalizedRIAs = new HashSet<OWLSubPropertyChainOfAxiom>();

		for (ComplexObjectPropertyInclusion originalComplexRIA : originalComplexRIAs) {

			ArrayList<OWLObjectPropertyExpression> subObjectProperties = new ArrayList<OWLObjectPropertyExpression>();
			for (OWLObjectPropertyExpression role : originalComplexRIA.m_subObjectProperties)
				subObjectProperties.add(role);
			OWLObjectPropertyExpression superProperty = originalComplexRIA.m_superObjectProperty;

			while (subObjectProperties.size() > 2) {
				if (subObjectProperties.get(0).toString().equals(superProperty.toString())) {
					// R1 o ... o Rn sqs R1 -> {Rn-1 o Rn sqs RX, R1 o ... o Rn-2 o RX sqs R1} 
					OWLObjectProperty freshRoleX = factory.getOWLObjectProperty(IRI.create(newRoleString + Integer.toString(++newRoleCounter)));

					List<OWLObjectPropertyExpression> subPropertyChain = new ArrayList<OWLObjectPropertyExpression>();
					subPropertyChain.add(subObjectProperties.get(subObjectProperties.size() - 2));
					subPropertyChain.add(subObjectProperties.get(subObjectProperties.size() - 1));
					normalizedRIAs.add(new OWLSubPropertyChainAxiomImpl(subPropertyChain, freshRoleX, new HashSet<OWLAnnotation>()));
					subObjectProperties.remove(subPropertyChain.size() - 1);
					subObjectProperties.set(subObjectProperties.size() - 1, freshRoleX);
				} else {
					// R1 o ... o Rn sqs R -> {R1 o R2 sqs RX, RX o R3 o ... o Rn sqs R} 
					OWLObjectProperty freshRoleX = factory.getOWLObjectProperty(IRI.create(newRoleString + Integer.toString(++newRoleCounter)));

					List<OWLObjectPropertyExpression> subPropertyChain = new ArrayList<OWLObjectPropertyExpression>();
					subPropertyChain.add(subObjectProperties.get(0));
					subPropertyChain.add(subObjectProperties.get(1));
					normalizedRIAs.add(new OWLSubPropertyChainAxiomImpl(subPropertyChain, freshRoleX, new HashSet<OWLAnnotation>()));

					subObjectProperties.remove(0);
					subObjectProperties.set(0, freshRoleX);
				}
			}

			normalizedRIAs.add(new OWLSubPropertyChainAxiomImpl(subObjectProperties, superProperty, new HashSet<OWLAnnotation>()));
		}

		return normalizedRIAs;
	}
}
