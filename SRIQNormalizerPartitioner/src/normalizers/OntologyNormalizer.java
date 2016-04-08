package normalizers;

import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.structural.OWLAxioms;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;

import sriqOntology.NFSRIQOntology;

public class OntologyNormalizer {

	public static NFSRIQOntology normalize(OWLOntology originalOntology) throws OWLOntologyCreationException {

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology logicalAxiomsOntology = manager.createOntology(new HashSet<OWLAxiom>(originalOntology.getLogicalAxioms()));
		originalOntology = null;

		HermitNormalizer hermitNormalizer = (new HermitNormalizer(manager.getOWLDataFactory(), new OWLAxioms(), 0));
		hermitNormalizer.processOntology(logicalAxiomsOntology);
		originalOntology = null;
	

		OWLAxioms hermitDataFilteredAxioms = filterOutDataAxioms(hermitNormalizer.m_axioms);
		hermitNormalizer = null;

		Set<OWLSubClassOfAxiom> normalizedConceptInclusions = TBoxNormalizer.normalizeConceptInclusions(hermitDataFilteredAxioms);

		Set<OWLSubPropertyChainOfAxiom> normalizedComplexRIAs = RBoxNormalizer.normalizeComplexRIAs(hermitDataFilteredAxioms.m_complexObjectPropertyInclusions);

		Set<OWLIndividualAxiom> normalizedAssertions = ABoxNormalizer.normalizeAssertions(normalizedConceptInclusions, hermitDataFilteredAxioms.m_facts);

		return new NFSRIQOntology(normalizedConceptInclusions, hermitDataFilteredAxioms.m_simpleObjectPropertyInclusions, normalizedComplexRIAs, normalizedAssertions);

	}

	public static OWLAxioms filterOutDataAxioms(OWLAxioms hermitAxioms) {

		OWLAxioms filteredAxioms = new OWLAxioms();

		// Top sqsubseteq D1 sqcup ... sqcup Dn
		for (OWLClassExpression[] conceptInclusion : hermitAxioms.m_conceptInclusions) {
			boolean containsDataPropertiesOrDatatypes = false;
			for (OWLClassExpression conceptExpression : conceptInclusion)
				if (!conceptExpression.getDataPropertiesInSignature().isEmpty() || !conceptExpression.getDatatypesInSignature().isEmpty())
					containsDataPropertiesOrDatatypes = true;

			if (!containsDataPropertiesOrDatatypes)
				filteredAxioms.m_conceptInclusions.add(conceptInclusion);
		}

		// R sqsubseteq S
		filteredAxioms.m_simpleObjectPropertyInclusions.addAll(hermitAxioms.m_simpleObjectPropertyInclusions);

		// R1 o ... o Rn sqsubseteq S
		filteredAxioms.m_complexObjectPropertyInclusions.addAll(hermitAxioms.m_complexObjectPropertyInclusions);

		// C(a), R(a, b), {ai} = {aj}, {ai} != {aj}
		for (OWLIndividualAxiom fact : hermitAxioms.m_facts)
			if (fact.getDataPropertiesInSignature().isEmpty() && fact.getDatatypesInSignature().isEmpty())
				filteredAxioms.m_facts.add(fact);

		return filteredAxioms;
	}
}
