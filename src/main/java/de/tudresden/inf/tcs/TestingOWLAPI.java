/**
 *
 */
package de.tudresden.inf.tcs;


import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.util.SimpleIRIMapper;

/**
 * @author Anas
 *
 */
public class TestingOWLAPI {


        /**
         * @param args
         */
        public static void main(String[] args) throws Exception {
                OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
                IRI groIRI = IRI.create("http://www.bootstrep.eu/ontology/GRO");
                IRI fileIRI = IRI.create(new File("C:\\Users\\Anas\\Desktop\\GRO_latest.xml"));
                SimpleIRIMapper mapper = new SimpleIRIMapper(groIRI, fileIRI);
                manager.addIRIMapper(mapper);
                //IRI iri = IRI.create("http://protege.stanford.edu/ontologies/pizza/pizza.owl");
                OWLOntology gro = manager.loadOntology(groIRI);
                //String s = readFile("C:\\Users\\Anas\\Desktop\\GRO_latest.xml", StandardCharsets.UTF_8);
                //System.out.println(f);
                //StringDocumentSource doc = new StringDocumentSource(s);
                //OWLOntology gro = manager.createOntology(groIRI);

                Set<OWLAxiom> axioms = gro.getAxioms();

                for (OWLAxiom a: axioms){
                        System.out.println(a);
                }

                Set<OWLClassAxiom> caxioms = gro.getGeneralClassAxioms();

                System.out.println("NOW THE CLASS AXIOMS: ");
                for (OWLClassAxiom ca: caxioms) {
                        System.out.print(ca);
                }

                System.out.println("NOW THE CLASSES: ");
                for (OWLClass oc: gro.getClassesInSignature()) {
                        System.out.println(oc);
                }



                 OWLDataFactory factory = manager.getOWLDataFactory();
                 OWLClass clsA = factory.getOWLClass(IRI.create(groIRI + "#ANAS"));
                 OWLClass clsB = factory.getOWLClass(IRI.create(groIRI + "#ELGHAFARI"));
                 // Now create the axiom
                 OWLAxiom axiom = factory.getOWLSubClassOfAxiom(clsA, clsB);
                 AddAxiom addAxiom = new AddAxiom(gro, axiom);
                 // We now use the manager to apply the change
                 manager.applyChange(addAxiom);
                 System.out.println("NOW THE UPDATED CLASSES: ");
                 for (OWLClass oc: gro.getClassesInSignature()) {
                                System.out.println(oc);
                 }

        }



        /**
         * FROM AN ANSWER ON STACKOVERFLOW
         * @param path
         * @param encoding
         * @return
         * @throws IOException
         */

        static String readFile(String path, Charset encoding)  throws IOException {
                byte[] encoded = Files.readAllBytes(Paths.get(path));
                return new String(encoded, encoding);
        }

}
