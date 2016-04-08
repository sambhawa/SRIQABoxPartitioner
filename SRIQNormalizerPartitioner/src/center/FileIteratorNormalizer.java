package center;

import java.io.File;
import java.io.IOException;

import normalizers.OntologyNormalizer;

import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

import sriqOntology.NFSRIQOntology;

public class FileIteratorNormalizer {

	static String inputDirPath = "Input";
	static String outputDirPath = "Output";
	static boolean rewriteOutputDir = true;

	public static void main(String[] emptyArgs) throws OWLOntologyCreationException, OWLOntologyStorageException, IOException {

		System.out.println("\n");
		System.out.println("Program Started: Horn Ontologies Normalizer.");
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
					sriqOntology.toFile(outputDirPath + File.separator + "NF" + inputFileNames[i]);

					if (sriqOntology.getABoxSize() > 5000) {
						System.out.println(" - NF TBox:" + "\t" + sriqOntology.getTBoxSize());
						System.out.println(" - NF RBox:" + "\t" + sriqOntology.getRBoxSize());
						System.out.println(" - NF ABox:" + "\t" + sriqOntology.getABoxSize());
					}

				}
			}
			System.out.println();
		}

		System.out.println("\n\n" + "Program terminated: Horn Ontologies Normalizer.");
	}
}
