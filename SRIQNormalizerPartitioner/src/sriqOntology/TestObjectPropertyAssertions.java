package sriqOntology;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import center.Srd;
import normalizers.OntologyNormalizer;

/*
 * This class is to figure out if a given ontology contains object property assertions
 * 
 */
public class TestObjectPropertyAssertions {

	static String inputDirPath = "C:\\myProject\\Oxford Ontology Repository\\Oxford Ontology Repository\\Ontologies-1-500\\";
	static String outputFilePath = "C:\\myProject\\Oxford Ontology Repository\\Oxford Ontology Repository\\validOntologies.txt";
	//static boolean rewriteOutputDir = true;
	
	public static void main(String[] args) throws IOException{
		
		System.out.println("Find max heap size");
		long maxBytes = Runtime.getRuntime().maxMemory();
		System.out.println("Max memory: " + maxBytes / 1024 / 1024 + "M");
		
		System.out.println(" * Check if this ontology has object property assertions");
		System.out.println(" * Input Directory" + "\t" + "\"" + inputDirPath + "\"");
		String[] inputFileNames = (new File(inputDirPath)).list();
		
		System.out.println("\n");

		ArrayList<String> filesWithObjPropAssertions = new ArrayList<String>();
		
		BufferedWriter bw = new BufferedWriter(new FileWriter(outputFilePath, true));
		
		for (int i = 0; i < inputFileNames.length; i++) {
			System.out.println("Evaluating file: " + i+"/"+inputFileNames.length);

			if (!inputFileNames[i].equals(".DS_Store")) {
				String ontologyPath = inputDirPath + File.separator + inputFileNames[i];
				OWLOntology ontology = Srd.loadOntology(ontologyPath);
				if (ontology != null) {					
					
					//TODO: check if sriqOntology has ObjectPropertyAssertions to be eligible for Abox partitioning 					
					//NFSRIQOntology sriqOntology = OntologyNormalizer.normalize(ontology);
					Set<OWLObjectPropertyAssertionAxiom> objectPropertyAxioms = ontology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION);
					if(!objectPropertyAxioms.isEmpty())
						{
							
							filesWithObjPropAssertions.add(inputFileNames[i]);
							
							bw.write(inputFileNames[i]+"\n");						     
						    bw.flush();
						      					    
						}
				
				}
				//OWLManager.createOWLOntologyManager().removeOntology(ontology);
				
			}
			//System.out.println();
			if(i % 100 == 0) System.out.println("# of valid files until now: "+ filesWithObjPropAssertions.size());
		}
		
		bw.close();
		System.out.println("Total count of valid files: "+filesWithObjPropAssertions.size());
		for(String fileName: filesWithObjPropAssertions){
			System.out.println(fileName);
		}

		System.out.println("\n\n" + "Program terminated: Horn Ontologies Normalizer.");
		
		
		
	}
}
