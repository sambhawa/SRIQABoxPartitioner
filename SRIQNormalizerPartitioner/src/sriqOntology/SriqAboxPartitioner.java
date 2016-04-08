package sriqOntology;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;

import DataStructure.Tuple;

import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

import center.Srd;
import normalizers.OntologyNormalizer;

public class SriqAboxPartitioner {

	static String aboxFilePath = "ABox";
	static String inputDirPath = "Input";
	static String outputDirPath = "Output";
	static boolean rewriteOutputDir = true;

	public static void main(String[] emptyArgs)
			throws OWLOntologyCreationException, OWLOntologyStorageException, IOException {

		System.out.println("SRIQ ontology partitioner");
		System.out.println(" * Input Directory" + "\t" + "\"" + inputDirPath + "\"");
		String[] inputFileNames = (new File(inputDirPath)).list();
		System.out.println(" * Output Directory" + "\t" + "\"" + outputDirPath + "\"");
		File outputDirFile = new File(outputDirPath);
		if (rewriteOutputDir)
			Srd.deleteDirectory(outputDirFile);
		outputDirFile.mkdir();
		System.out.println("\n\n");

		for (int i = 0; i < inputFileNames.length; i++) {
			System.out.println("Evaluating file: " + inputFileNames[i]);

			if (!inputFileNames[i].equals(".DS_Store")) {
				String ontologyPath = inputDirPath + File.separator + inputFileNames[i];
				OWLOntology ontology = Srd.loadOntology(ontologyPath);
				if (ontology != null) {
					NFSRIQOntology sriqOntology = OntologyNormalizer.normalize(ontology);

					// TODO: check if sriqOntology has ObjectPropertyAssertions
					// for this algorithm to be valid
					// If so, proceed with partitioning

					HashSet<Set<OWLAxiom>> aboxPartitions = partition(sriqOntology, ontology);

				}
			}
			System.out.println();
		}

		System.out.println("\n\n" + "Program terminated: SRIQ ontology partitioner.");
	}

	private static HashSet<Set<OWLAxiom>> partition(NFSRIQOntology sriqOntology, OWLOntology ontology) {

		// Step 0. Find the set of all object properties (including inverse of
		// each property)
		Set<OWLObjectPropertyExpression> roles = getAllRolesFromOntology(sriqOntology);

		// Step 1. Compute minimal transitive and reflexive relation over roles
		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> SRMap = computeSRMap(roles,
				sriqOntology.getRoleInclusionAxioms());
		
		//TODO: Step 2. Compute the precedes relation over roles. 

		
		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> simpleRoleSubsumption = findSimpleRoleSubsumption(
				sriqOntology);
		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> complexRoleSubsumption = findComplexRoleSubsumption(
				sriqOntology);

		
		// Step 2. find connector roles: Analyze TBox to find such roles which,
		// either themselves appear in forall axioms, or their superclasses do
		// (note, a role is a superclass of itself)
		HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>> connectorSimpleRolesMap = findConnectorRoles(
				sriqOntology, simpleRoleSubsumption, true);
		HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>> connectorComplexRolesMap = findConnectorRoles(
				sriqOntology, complexRoleSubsumption, false);
		HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>> combinedConnectorRolesMap = new HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>>();
		combinedConnectorRolesMap.putAll(connectorSimpleRolesMap);
		combinedConnectorRolesMap.putAll(connectorComplexRolesMap);

		// Debug: Print out intermediate stats
		// 1. print out all connector roles
		System.out.println("size of the map of all connector roles: " + combinedConnectorRolesMap.size());

		// Step 3. find connected individuals - individuals appearing in
		// ObjectPropertyAssertions for the connector properties identified
		// above.
		// If R is a connector property s.t. A \sqs \forall S. B and R precedes
		// S, and R(a,b) \ele ABox, then a and b are connected individuals if b
		// \notele
		// b \notele B.
		// HashMap<OWLIndividual, Tuple> connectedIndividuals =
		// getConnectedIndividualsStats(sriqOntology, ontology,
		// combinedConnectorRolesMap);
		HashMap<OWLIndividual, Tuple> connectedIndividuals = processABoxToFindConnectedIndividuals(
				combinedConnectorRolesMap);

		// Debug
		System.out.println("size of connectedIndv maps: " + connectedIndividuals.size());

		// Step 4. Find ABox assertions containing the above connected
		// individuals
		HashSet<Set<OWLAxiom>> aboxPartitions = findAboxPartition(sriqOntology, connectedIndividuals);

		return aboxPartitions;

	}

	private static HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> computeSRMap(
			Set<OWLObjectPropertyExpression> roles, ArrayList<OWLSubObjectPropertyOfAxiom> roleIncAxioms) {

		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> SRMap = new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();

		// step 1. Initialize the map with each role in the roles
		for (OWLObjectPropertyExpression role : roles) {
			Set<OWLObjectPropertyExpression> superRoles = new HashSet<OWLObjectPropertyExpression>();
			superRoles.add(role);
			SRMap.put(role, superRoles);
		}

		// Step 2. For each simple RIA, update the map
		// for each (R sqs S in TBox), add R -> S, Inv(R) -> Inv(S)
		for (OWLSubObjectPropertyOfAxiom axiom : roleIncAxioms) {

			OWLObjectPropertyExpression subRole = axiom.getSubProperty();
			OWLObjectPropertyExpression superRole = axiom.getSuperProperty();

			SRMap.get(subRole).add(superRole); // R -> S
			SRMap.get(Srd.invert(subRole)).add(Srd.invert(superRole)); // Inv(R)
																		// ->
																		// Inv(S)
		}

		// Step 3. Compute transitive closure		
		SRMap = computeSubsumption(SRMap);

		return SRMap;
	}

	private static Set<OWLObjectPropertyExpression> getAllRolesFromOntology(NFSRIQOntology sriqOntology) {

		Set<OWLObjectPropertyExpression> roles = new HashSet<OWLObjectPropertyExpression>();

		// get all roles from univAxioms and add them and their inverses to the
		// roles set
		ArrayList<OWLSubClassOfAxiom> allValuesFromAxioms = sriqOntology.getUnivAxioms();
		for (OWLSubClassOfAxiom axiom : allValuesFromAxioms) {

			OWLClassExpression superClass = axiom.getSuperClass();
			OWLObjectAllValuesFrom univConceptExpression = (OWLObjectAllValuesFrom) superClass;
			roles.add(univConceptExpression.getProperty());
			roles.add(Srd.invert(univConceptExpression.getProperty()));
		}

		// get all roles from minCardinality and add them and their inverses to
		// the roles set
		ArrayList<OWLSubClassOfAxiom> minCardAxioms = sriqOntology.getMinCardAxioms();
		for (OWLSubClassOfAxiom axiom : minCardAxioms) {

			OWLClassExpression superClass = axiom.getSuperClass();
			OWLObjectMinCardinality minConceptExpression = (OWLObjectMinCardinality) superClass;
			roles.add(minConceptExpression.getProperty());
			roles.add(Srd.invert(minConceptExpression.getProperty()));
		}

		// get all roles from maxCardinality and add them and their inverses to
		// the roles set
		ArrayList<OWLSubClassOfAxiom> maxCardAxioms = sriqOntology.getMaxCardAxioms();
		for (OWLSubClassOfAxiom axiom : maxCardAxioms) {

			OWLClassExpression superClass = axiom.getSuperClass();
			OWLObjectMaxCardinality maxConceptExpression = (OWLObjectMaxCardinality) superClass;
			roles.add(maxConceptExpression.getProperty());
			roles.add(Srd.invert(maxConceptExpression.getProperty()));
		}

		// get all roles from simple RIA and add them and their inverses to the
		// roles set
		ArrayList<OWLSubObjectPropertyOfAxiom> roleInclusionAxioms = sriqOntology.getRoleInclusionAxioms();
		for (OWLSubObjectPropertyOfAxiom axiom : roleInclusionAxioms) {
			roles.add(axiom.getSubProperty());
			roles.add(Srd.invert(axiom.getSubProperty()));
			roles.add(axiom.getSuperProperty());
			roles.add(Srd.invert(axiom.getSuperProperty()));

		}

		// get all roles from complex RIA and add them and their inverses to the
		// roles set
		ArrayList<OWLSubPropertyChainOfAxiom> complexRoleInclusionAxioms = sriqOntology.getComplexRoleInclusionAxioms();
		for (OWLSubPropertyChainOfAxiom axiom : complexRoleInclusionAxioms) {

			roles.add(axiom.getSuperProperty());
			roles.add(Srd.invert(axiom.getSuperProperty()));

			List<OWLObjectPropertyExpression> subRoleList = axiom.getPropertyChain();

			// add the subRoles found in the property chain and their inverses
			for (OWLObjectPropertyExpression subRole : subRoleList) {
				roles.add(subRole);
				roles.add(Srd.invert(subRole));

			}

		}

		return roles;
	}

	private static HashMap<OWLIndividual, Tuple> processABoxToFindConnectedIndividuals(
			HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>> combinedConnectorRolesMap) {

		// Step 1. Create and initialize a map HashMap<OWLIndividual, Tuple> for
		// each named-individual in the ontology
		HashMap<OWLIndividual, Tuple> connIndividualMap = new HashMap<OWLIndividual, Tuple>();

		// Process each ABox file, load the ontology and find roleAssertions and
		// concepAssertions in the current file, pass them to the
		// getConnectedIndividualsStats to update connectedIndividuals map
		File folder = new File(aboxFilePath);
		for (File fileEntry : folder.listFiles()) {

			// ABox asscertions in this file: C(a), R(a,b)
			// Initialize new arraylist everytime
			ArrayList<OWLClassAssertionAxiom> conceptAssertionAxioms = new ArrayList<OWLClassAssertionAxiom>();
			ArrayList<OWLObjectPropertyAssertionAxiom> roleAssertionAxioms = new ArrayList<OWLObjectPropertyAssertionAxiom>();

			OWLOntology ontology = Srd.loadOntology(fileEntry); // ABox
			Set<OWLAxiom> aboxAxioms = ontology.getABoxAxioms(false);

			// Go through each ABox axiom in this file and figure out if it is a
			// role or a concept assertion

			// An alternate way to get all concept assertions or class
			// assertions
			// ontology.getAxioms(AxiomType.CLASS_ASSERTION, false);

			for (OWLAxiom fact : aboxAxioms) {
				switch (fact.getAxiomType().toString()) {
				case "ClassAssertion":
					// C(a)
					OWLClassExpression classExpression = ((OWLClassAssertionAxiom) fact).getClassExpression();
					if (Srd.conceptTypeToString(classExpression) == Srd.className)
						// A(a)
						conceptAssertionAxioms.add((OWLClassAssertionAxiom) fact);
					else
						System.out.println("WARNING!!! Illegal assertion at SriqAboxPartitioner.java: "
								+ fact.getAxiomType() + "\n" + fact);
					break;
				case "ObjectPropertyAssertion":
					// R(a, b)
					roleAssertionAxioms.add((OWLObjectPropertyAssertionAxiom) fact);
					break;

				// Ignore owl:sameAs and owl:differentFrom axioms for now

				default:
					System.out.println("WARNING!!! Unrecognized OWLIndividualAxiom type at NFSRIQOntology.java: "
							+ fact.getAxiomType());
					break;
				}

			}

			// update the connIndividual map based on the instance assertions
			// for this ontology
			getConnectedIndividualsStats(ontology.getIndividualsInSignature(), connIndividualMap,
					conceptAssertionAxioms, roleAssertionAxioms, combinedConnectorRolesMap);
		}

		return connIndividualMap;

	}

	private static void getConnectedIndividualsStats(Set<OWLNamedIndividual> namedIndividuals,
			HashMap<OWLIndividual, Tuple> connIndividualMap, ArrayList<OWLClassAssertionAxiom> conceptAssertionAxioms,
			ArrayList<OWLObjectPropertyAssertionAxiom> roleAssertionAxioms,
			HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>> combinedConnectorRolesMap) {

		// get all named-individuals from the ontology
		// Set<OWLNamedIndividual> namedIndividuals =
		// ontology.getIndividualsInSignature();

		// initialize the hashmap
		for (OWLNamedIndividual ind : namedIndividuals) {

			Set<OWLIndividual> connIndSet = new HashSet<OWLIndividual>();
			connIndSet.add(ind);

			Tuple t = new Tuple(connIndSet, 0);
			connIndividualMap.put(ind, t);
		}

		// Step 2. Go through each role-assertion, R(a,b) in the ontology and
		// build the connectedIndividual map.
		// ArrayList<OWLObjectPropertyAssertionAxiom> roleAssertionAxioms =
		// sriqOntology.getRoleAssertionAxioms();

		for (OWLObjectPropertyAssertionAxiom roleAssertion : roleAssertionAxioms) {
			OWLObjectPropertyExpression role = roleAssertion.getProperty();
			OWLIndividual subject = roleAssertion.getSubject();
			OWLIndividual object = roleAssertion.getObject();

			// Step 2.1. If R is not a connector role, increment assertion-count
			// for a and b by 1.
			if (!combinedConnectorRolesMap.containsKey(role)) {

				connIndividualMap.get(subject).incAssertionCountByOne();
				connIndividualMap.get(object).incAssertionCountByOne();

			} else {
				// Step 2.2. Else if R is a connector role in the role-assertion
				// R(a,b)
				// a) Create a new object Tuple whose set is union of sets for
				// both the individuals; and update the assertion-count =
				// (sum of counts for entry for each individual +1)
				// b) Traverse the individuals in the 'unioned' set and update
				// the value pointer for each individual's key
				// to the new Tuple object created above.

				Set<OWLIndividual> set1 = connIndividualMap.get(subject).getconnectedIndividuals();
				Set<OWLIndividual> set2 = connIndividualMap.get(object).getconnectedIndividuals();
				set1.addAll(set2);

				int newAssertionCount = connIndividualMap.get(subject).getAssertionCount()
						+ connIndividualMap.get(object).getAssertionCount() + 1;

				Tuple newTuple = new Tuple(set1, newAssertionCount);

				connIndividualMap.put(subject, newTuple); // overwrites the
															// value for this
															// key (subject)
				connIndividualMap.put(object, newTuple); // overwrites the value
															// for this key
															// (object)

			}
		}

		// Step 3. Go through each concept-assertion in the ontology and
		// increment the assertion count
		// corresponding to the individual by 1.
		// ArrayList<OWLClassAssertionAxiom> conceptAssertionAxioms =
		// sriqOntology.getConceptAssertionAxioms();
		for (OWLClassAssertionAxiom conceptAssertion : conceptAssertionAxioms) {
			OWLIndividual indv = conceptAssertion.getIndividual();
			connIndividualMap.get(indv).incAssertionCountByOne();
		}

		// return connIndividualMap;
	}

	private static HashSet<Set<OWLAxiom>> findAboxPartition(NFSRIQOntology sriqOntology,
			HashMap<OWLIndividual, Tuple> connectedIndividuals) {
		HashSet<Set<OWLAxiom>> aboxPartitions = new HashSet<Set<OWLAxiom>>();

		// Go through each type of ABox assertions (C(a), R(a, b), {ai} = {aj},
		// {ai} != {aj}),
		// and look through each connectedindividual set and identify
		// corresponding assertions

		return aboxPartitions;
	}

	private static HashSet<Set<OWLIndividual>> findConnectedIndividuals(NFSRIQOntology sriqOntology,
			OWLOntology ontology, HashMap<OWLObjectPropertyExpression, OWLClassExpression> connectorRolesMap) {

		HashSet<Set<OWLIndividual>> connectedIndividuals = new HashSet<Set<OWLIndividual>>();

		ArrayList<OWLObjectPropertyAssertionAxiom> objectPropertyAssertionsAxioms = sriqOntology
				.getRoleAssertionAxioms();
		// ArrayList<OWLClassAssertionAxiom> classAssertionAxioms =
		// sriqOntology.getConceptAssertionAxioms();

		for (OWLObjectPropertyAssertionAxiom psoAxiom : objectPropertyAssertionsAxioms) {
			// get property
			OWLObjectPropertyExpression role = psoAxiom.getProperty();

			// check if role is a connector role
			if (connectorRolesMap.keySet().contains(role)) {
				// find the corresponding class to the role in the
				// connectorRolesMap
				OWLClassExpression classToMatch = connectorRolesMap.get(role);

				// Now check if the object o in the psoAxiom is a member of the
				// class
				// which is the class associated with the connector role, i.e.
				// classToMatch above
				OWLIndividual objectInPSOAxiom = psoAxiom.getObject();
				OWLIndividual subjectInPSOAxiom = psoAxiom.getSubject();

				// Alternative solution -
				// go thru each classassertions and check if the class of o
				// matches with class corresponding to role in connectorRolesMap

				Set<OWLClassExpression> assertedClassAssertions = objectInPSOAxiom.getTypes(ontology); // get
																										// asserted
																										// classes
																										// for
																										// this
																										// individual

				if (!assertedClassAssertions.contains(classToMatch)) {

					// if all the above conditions are satisfied, add the (s,o)
					// pair to the set

					Set<OWLIndividual> newSet = new HashSet<OWLIndividual>();
					newSet.add(objectInPSOAxiom);
					newSet.add(subjectInPSOAxiom);

					connectedIndividuals.add(newSet);

				}

				// Compute transitive closure on the initial set of connected
				// individuals.
				// Build minimum spanning tree?
				// Use union-find algorithm
				// TODO!!

			}

		}

		return connectedIndividuals;
	}

	private static HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>> findConnectorRoles(
			NFSRIQOntology sriqOntology,
			HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleSubsumption,
			boolean isSimpleRole) {

		HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>> connectorRolesMap = new HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>>();

		// find all properties appearing in the univAxioms
		ArrayList<OWLSubClassOfAxiom> allValuesFromAxioms = sriqOntology.getUnivAxioms();

		// find the superclass and subclass expression in univAxioms
		for (OWLSubClassOfAxiom axiom : allValuesFromAxioms) {

			OWLClassExpression superClass = axiom.getSuperClass();
			OWLClassExpression subClass = axiom.getSubClass();

			if (isSimpleRole == true) {
				if (subClass.equals(Srd.top))
					continue; // skip this axiom if it is a range axiom for a
								// simple role.
			}

			// since we know these are allValuesFrom axioms, we know that the
			// ClassExpressionType of superClass is ObjectAllValuesFrom
			// So we can simply cast the superClass as ObjectAllValuesFrom
			if ((Srd.conceptTypeToString(superClass)).equals(Srd.allValuesFrom + Srd.className)) {
				OWLObjectAllValuesFrom univConceptExpression = (OWLObjectAllValuesFrom) superClass;
				// connectorRolesMap.add(univConceptExpression.getProperty());
				if (!connectorRolesMap.containsKey(univConceptExpression.getProperty())) {
					connectorRolesMap.put(univConceptExpression.getProperty(), new HashSet<OWLClassExpression>());

				}
				connectorRolesMap.get(univConceptExpression.getProperty()).add(univConceptExpression.getFiller());

			}

		}

		// Find subroles of the connectorRoles - All the sub-properties of the
		// connector roles are also connector roles.
		// Check if any of these roles appear in the values in the
		// roleSubsumption Map and add their key to the connectorRoles set
		// loop through each entry in map
		Set<OWLObjectPropertyExpression> connectorRoles = connectorRolesMap.keySet();
		for (Entry<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> entry : roleSubsumption.entrySet()) {
			OWLObjectPropertyExpression subRole = entry.getKey();
			Set<OWLObjectPropertyExpression> setOfSuperRoles = entry.getValue();

			// find intersection between connectorRoles set and superRolesSet
			Set<OWLObjectPropertyExpression> intersectionSet = new HashSet<OWLObjectPropertyExpression>(
					setOfSuperRoles);
			intersectionSet.retainAll(connectorRoles);

			// If intersection found, then add the subRole to connectorRolesMap
			// with the same value list as the super role in the
			// connectorRoleMap
			if (intersectionSet != null && intersectionSet.size() > 0) {
				// connectorRoles.add(subRole);
				for (OWLObjectPropertyExpression commonRole : intersectionSet) {
					connectorRolesMap.put(subRole, connectorRolesMap.get(commonRole));
				}
			}
		}

		return connectorRolesMap;
	}

	private static HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> findComplexRoleSubsumption(
			NFSRIQOntology sriqOntology) {

		ArrayList<OWLSubPropertyChainOfAxiom> roleInclusionAxioms = sriqOntology.getComplexRoleInclusionAxioms();

		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleToSuperRolesMap = new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();

		// Step 1. Build a map of subrole to superrole based on complex
		// roleinclusion axioms found in ontology
		for (OWLSubPropertyChainOfAxiom roleAxiom : roleInclusionAxioms) {

			List<OWLObjectPropertyExpression> subRoleList = roleAxiom.getPropertyChain();
			OWLObjectPropertyExpression superRole = roleAxiom.getSuperProperty();

			// create entry for each subRole in the property chain
			for (OWLObjectPropertyExpression subRole : subRoleList) {

				if (roleToSuperRolesMap.get(subRole) == null) {
					// create new entry in map for the subrole and it's inverse
					roleToSuperRolesMap.put(subRole, new HashSet<OWLObjectPropertyExpression>());
					roleToSuperRolesMap.put(subRole.getInverseProperty(), new HashSet<OWLObjectPropertyExpression>());

					// add the subrole and inverse subrole in values list for
					// this subrole
					roleToSuperRolesMap.get(subRole).add(subRole);
					roleToSuperRolesMap.get(subRole.getInverseProperty()).add(subRole.getInverseProperty());
				}
				// add super-role to value set
				roleToSuperRolesMap.get(subRole).add(superRole);
				roleToSuperRolesMap.get(subRole).add(superRole.getInverseProperty()); // ??
																						// correct?
				roleToSuperRolesMap.get(subRole.getInverseProperty()).add(superRole); // ??correct?
				roleToSuperRolesMap.get(subRole.getInverseProperty()).add(superRole.getInverseProperty());
			}

		}

		// Step 2. Iteratively compute the transitive super-roles
		// Since the ontology is normalized, there are no cycles; so the
		// iterative approach will halt at some point.

		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> rolesClosureMap = computeSubsumption(
				roleToSuperRolesMap);

		return rolesClosureMap;
	}

	private static HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> findSimpleRoleSubsumption(
			NFSRIQOntology sriqOntology) {

		ArrayList<OWLSubObjectPropertyOfAxiom> roleInclusionAxioms = sriqOntology.getRoleInclusionAxioms();

		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleToSuperRolesMap = new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();

		// Step 1. Build a map of subrole to superrole based on roleinclusion
		// axioms found in ontology
		for (OWLSubObjectPropertyOfAxiom roleAxiom : roleInclusionAxioms) {

			OWLObjectPropertyExpression subRole = roleAxiom.getSubProperty();
			OWLObjectPropertyExpression superRole = roleAxiom.getSuperProperty();

			if (roleToSuperRolesMap.get(subRole) == null) {
				// create new entry in map for the subrole and it's inverse
				roleToSuperRolesMap.put(subRole, new HashSet<OWLObjectPropertyExpression>());
				roleToSuperRolesMap.put(subRole.getInverseProperty(), new HashSet<OWLObjectPropertyExpression>());
				// System.out.println(subRole.getInverseProperty());

			}

			// add the subrole and inverse subrole in values list
			roleToSuperRolesMap.get(subRole).add(subRole);
			if (roleToSuperRolesMap.get(subRole.getInverseProperty()) != null)
				roleToSuperRolesMap.get(subRole.getInverseProperty()).add(subRole.getInverseProperty());
			else
				System.out.println("Map entry null for subRole.getInverseProperty() ");

			// add super-role to value set
			roleToSuperRolesMap.get(subRole).add(superRole);
			roleToSuperRolesMap.get(subRole).add(superRole.getInverseProperty()); // ??
																					// correct?
			roleToSuperRolesMap.get(subRole.getInverseProperty()).add(superRole); // ??correct?
			roleToSuperRolesMap.get(subRole.getInverseProperty()).add(superRole.getInverseProperty());

		}

		// Step 2. Iteratively compute the transitive super-roles
		// Since the ontology is normalized, there are no cycles; so the
		// iterative approach will halt at some point.

		HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> rolesClosureMap = computeSubsumption(
				roleToSuperRolesMap);

		return rolesClosureMap;
	}

	private static HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> computeSubsumption(
			HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleToSuperRolesMap) {
		boolean modified = true;

		while (modified = true) { // Iterate until any list corresponding to a
									// key in the map is modified.

			modified = false; // reset it to false for every new iteration of
								// closure computation

			// loop through each entry in map
			for (Entry<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> entry : roleToSuperRolesMap
					.entrySet()) {
				OWLObjectPropertyExpression subRole = entry.getKey();
				Set<OWLObjectPropertyExpression> superRolesSet = entry.getValue();

				// super roles to append to this key's value list
				Set<OWLObjectPropertyExpression> superRolesToAppend = new HashSet<OWLObjectPropertyExpression>();

				// Loop through each key's values. For each role in
				// superRolesSet, find if there are matching
				// keys in the map and if match is found, union the matched
				// key's value set (set
				// of superroles) with the current role's value set.
				for (OWLObjectPropertyExpression superRole : superRolesSet) {

					// do not check for the same superrole for a
					// given entry

					if (roleToSuperRolesMap.get(superRole) != null) // match
																	// found
					{
						// check if it has more super-roles than just itself
						if (roleToSuperRolesMap.get(superRole).size() > 1) {
							// collect this role's superrole set to be added to
							// the key at the end of this loop
							superRolesToAppend.addAll(roleToSuperRolesMap.get(superRole));

						}

					}

				}
				// append to the value list
				modified = modified || roleToSuperRolesMap.get(subRole).addAll(superRolesToAppend);
			}

		} // end of while

		return roleToSuperRolesMap;
	}

}
