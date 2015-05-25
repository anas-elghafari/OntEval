/**
 *
 */

package de.tudresden.inf.tcs;

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.OWLOntologyChangeVetoException;
import org.semanticweb.owlapi.model.OWLOntologyChangesVetoedListener;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.util.SimpleIRIMapper;

import uk.ac.manchester.cs.owl.owlapi.OWLEquivalentClassesAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;

import de.tudresden.inf.tcs.OWLVetoesListener;

/** @author Anas Elghafari
 *
 */


public class EvaluatingGCIs {

        //LOGLEVEL = 0  --> turn off most of the output.
        //LOGLEVEL = 1 --> only the interesting results.
        //LOGLEVEL = 2 --> output that allows deeper look into the process... and so on.

        public static final int LOGLEVEL = 3;
        public static final String INPUTFILE = "gcis-with-role-depth-1";
        public static final Level reasonerLogLevel = Level.ERROR;


        private static OWLOntology gro;
        private static OWLOntologyManager manager;
        private static OWLDataFactory factory;
        private static IRI groIRI;
    private static OWLReasoner reasoner;
        private static HashMap<String,String> AxiomToGci;
        private static HashSet<OWLAxiom> unsatClassesGCIs;
        private static HashSet<OWLAxiom> unsatClassesGCIs2;
        private static HashSet<String> extractedClassNames;
        private static HashSet<String> extractedPropertyNames;
        private static String inputFileAsString;









        static void loadGRO() throws OWLOntologyCreationException {
                manager = OWLManager.createOWLOntologyManager();
                groIRI = IRI.create("http://www.bootstrep.eu/ontology/GRO");
                IRI fileIRI = IRI.create(new File("gro-latest"));
                SimpleIRIMapper mapper = new SimpleIRIMapper(groIRI, fileIRI);
                manager.addIRIMapper(mapper);
                gro = manager.loadOntology(groIRI);
                factory = manager.getOWLDataFactory();
                OWLReasonerFactory reasonerFactory = new ElkReasonerFactory();
                reasoner = reasonerFactory.createReasoner(gro);
                Logger.getLogger("org.semanticweb.elk").setLevel(reasonerLogLevel);
        }





        static void initializeRecords() {
                AxiomToGci = new HashMap<String, String>();
                unsatClassesGCIs = new HashSet<OWLAxiom>();
                unsatClassesGCIs2 = new HashSet<OWLAxiom>();
                extractedClassNames = new HashSet<String>();
                extractedPropertyNames = new HashSet<String>();
        }
















        //a method to create an inconsistency in the ontology, for testing purposes-
        private static void addInconsistency() {
                OWLClass awake = factory.getOWLClass(IRI.create(groIRI + "#awake"));
                OWLClass asleep = factory.getOWLClass(IRI.create(groIRI + "#asleep"));
                OWLNamedIndividual john = factory.getOWLNamedIndividual(IRI.create(groIRI + "#John"));
                OWLClassAssertionAxiom johnAwake = factory.getOWLClassAssertionAxiom(awake, john);
                OWLClassAssertionAxiom johnAsleep = factory.getOWLClassAssertionAxiom(asleep, john);
                OWLDisjointClassesAxiom disjointness = factory.getOWLDisjointClassesAxiom(awake, asleep);
                manager.addAxiom(gro, johnAwake);
                manager.addAxiom(gro, johnAsleep);
                manager.addAxiom(gro, disjointness);
        }



        //a method to create an unsatisfiable calss in the ontology, for testing purposes-
    private static void addUnsatisfiableClassAsGCI() {
            System.out.println("adding an unsatisfiable class as a GCI");
                        OWLClass dead = factory.getOWLClass(IRI.create(groIRI + "#dead"));
                        OWLClass alive = factory.getOWLClass(IRI.create(groIRI + "#alive"));
                        OWLClass zombies = factory.getOWLClass(IRI.create(groIRI + "#zombies"));
                        OWLSubClassOfAxiom zombiesDead = factory.getOWLSubClassOfAxiom(zombies, alive);
                        OWLSubClassOfAxiom zombiesAlive = factory.getOWLSubClassOfAxiom(zombies, dead);
                        OWLClassExpression intersectionDeadAlive = factory.getOWLObjectIntersectionOf(dead, alive);
                        OWLSubClassOfAxiom intersectionSubclassBottom = factory.getOWLSubClassOfAxiom(intersectionDeadAlive,
                                        factory.getOWLNothing());
                        manager.addAxiom(gro, zombiesAlive);
                        manager.addAxiom(gro, zombiesDead);
                        manager.addAxiom(gro, intersectionSubclassBottom);
                        reasoner.flush();
                        NodeSet<OWLClass> zombiesSuperclass = reasoner.getSuperClasses(zombies, false);
                        Node<OWLClass> zombiesEquivalent = reasoner.getEquivalentClasses(zombies);
                        NodeSet<OWLClass> deadAndAliveSuperclasses = reasoner.getSuperClasses(intersectionDeadAlive, false);
                        Node<OWLClass> deadAndAliveEquivalent = reasoner.getEquivalentClasses(intersectionDeadAlive);
                        System.out.println("zombies superclass:" + zombiesSuperclass);
                        System.out.println("zombies equivalentclasses:" + zombiesEquivalent);
                        System.out.println("DeadAndAlive superclasses: " + deadAndAliveSuperclasses);
                        System.out.println("DeadAndAlive equivalent classes: " + deadAndAliveEquivalent);
                        if(deadAndAliveEquivalent.contains(factory.getOWLNothing())) {
                                System.out.println("Bottom found as an equivalent class to deadAndAlive");
                        }


                }




    private static void addUnsatisfiableClass() {
                OWLClass dead = factory.getOWLClass(IRI.create(groIRI + "#dead"));
                OWLClass alive = factory.getOWLClass(IRI.create(groIRI + "#alive"));
                OWLClass zombies = factory.getOWLClass(IRI.create(groIRI + "#zombies"));
                OWLSubClassOfAxiom zombiesDead = factory.getOWLSubClassOfAxiom(zombies, alive);
                OWLSubClassOfAxiom zombiesAlive = factory.getOWLSubClassOfAxiom(zombies, dead);
                OWLDisjointClassesAxiom disjointness = factory.getOWLDisjointClassesAxiom(dead, alive);
                manager.addAxiom(gro, zombiesAlive);
                manager.addAxiom(gro, zombiesDead);
                manager.addAxiom(gro, disjointness);
        }



        static ArrayList<OWLAxiom> getRedundantAxioms(ArrayList<OWLAxiom> axioms) {
                ArrayList<OWLAxiom> redundant = new ArrayList<OWLAxiom>();
                for(OWLAxiom a:axioms) {
                        if(reasoner.isEntailed(a)) {
                                redundant.add(a);
                        }
                }
                return redundant;
        }




        static ArrayList<OWLAxiom> getRedundantAxiomsDETAILED(ArrayList<OWLAxiom> axioms) {
                ArrayList<OWLAxiom> redundant = new ArrayList<OWLAxiom>();
                int disjointnessAxioms = 0;
            int dummyClassIndex = 0;

                for(OWLAxiom a: axioms){
                        OWLSubClassOfAxiom axiom = (OWLSubClassOfAxiom) a;

                        //the case of disjointness axioms:
                        if (axiom.getSuperClass().equals(factory.getOWLNothing())) {
                                disjointnessAxioms++;
                            OWLClassExpression subclass = axiom.getSubClass();
                            Node<OWLClass> inferredEquivalentclasses = reasoner.getEquivalentClasses(subclass);


                            if (inferredEquivalentclasses.contains(factory.getOWLNothing())) {
                                //System.out.println("Bottom found as an equivalent class!!");
                                    //System.out.println("superclasses of the subclass: "+ inferredSuperclasses);
                                    //System.out.println("equivalent classes: " + inferredEquivalentclasses);
                                redundant.add(axiom);
                            }else {
                                //System.out.println("\nBOTTOM NOT FOUND AS EQUIVALENT CLASS");
                                //System.out.println("The disjointness Axiom: " + a.toString());
                                    //System.out.println("GCI operand1: " + subclass);

                            }

                            /*
                            List<OWLClassExpression> operandsList =  intersection.getOperandsAsList();
                            NodeSet<OWLClass> disjointClasses = reasoner.getDisjointClasses(operandsList.get(0));
                            for (int i= 1; i<operandsList.size(); i++) {
                                if (disjointClasses.containsEntity((OWLClass) operandsList.get(i))) {
                                        System.out.println("redundancy found!!!");
                                }
                            }*/
                        }


                        //the case of subclass axioms:
                        else {
                                OWLClassExpression subclass = axiom.getSubClass();
                                OWLClassExpression superclass = axiom.getSuperClass();
                            dummyClassIndex++;
                            Set<OWLClassExpression> equivSet = new HashSet<OWLClassExpression>();
                            equivSet.add(superclass);
                            OWLClass equivClass = factory.
                                        getOWLClass(IRI.create(groIRI + "#" + "DUMMY_CLASS" + dummyClassIndex));
                            equivSet.add(equivClass);
                            OWLEquivalentClassesAxiomImpl equiv = new OWLEquivalentClassesAxiomImpl(equivSet,
                                        new HashSet<OWLAnnotation>());
                            manager.addAxiom(gro, equiv);
                            reasoner.flush();
                            NodeSet<OWLClass> inferredSuperclasses = reasoner.getSuperClasses(subclass, false);
                            Node<OWLClass> inferredEquivalentclasses = reasoner.getEquivalentClasses(subclass);

                            if (inferredSuperclasses.containsEntity(equivClass) ||
                                inferredEquivalentclasses.contains(equivClass)) {
                                //System.out.println("Redundant subclass axiom found." );
                                redundant.add(axiom);
                            }
                            //System.out.println("\nSubclass Axiom: " + a.toString());
                            //System.out.println("superclasses of the subclass: "+ inferredSuperclasses);
                            //System.out.println("equivalent classes to the subclass:" + inferredEquivalentclasses);

                        }
                }


                //System.out.println("Total number of axioms: " + axioms.size());
        //System.out.println("number of disjointness axioms: " + disjointnessAxioms);
                //System.out.println("number of redundant suclassof axioms:" +  redundant.size());
                //System.out.println("number of axioms where the superclass is an expression:" + dummyClassIndex);
                return redundant;
    }




        static ArrayList<OWLAxiom> getAxiomsEntailedByOthers(ArrayList<OWLAxiom> axioms) throws Exception {
                ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
                for(OWLAxiom a: axioms) {
                        loadGRO();
                        addAllAxiomsExceptOne(axioms, a);
                        reasoner.flush();
                        ArrayList<OWLAxiom> excludedAxiom = new ArrayList<OWLAxiom>();
                        excludedAxiom.add(a);
                        ArrayList<OWLAxiom> redundant = getRedundantAxiomsDETAILED(excludedAxiom);
                        if (!redundant.isEmpty()) {
                                //System.out.println("found an axiom entailed by others: " + a);
                                result.add(a);
                        }
                }
                return result;

        }


    private static void addAllAxiomsExceptOne(ArrayList<OWLAxiom> axioms, OWLAxiom excludedAxiom) {
        //adding the axioms:
        for(OWLAxiom a: axioms) {
            if (a.equals(excludedAxiom)) {
                //System.out.println("encountered the excluded axiom: " + a);
                continue;
            }

            manager.addAxiom(gro, a);
        }
    }




    private static void mapGCIsToUnsatClasses(ArrayList<OWLAxiom> axioms) throws Exception {
        HashMap<String, HashSet<String>> m = new HashMap<String, HashSet<String>>();
        HashSet<String> allUnsatClasses = new HashSet<String>();
        for(OWLAxiom a: axioms) {
            loadGRO();
            manager.addAxiom(gro, a);
            reasoner.flush();
            Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
            Set<OWLClass> unsat = bottomNode.getEntitiesMinusBottom();
            HashSet<String> unsatClassNames = new HashSet<String>();
            for(OWLClass cl: unsat) {
                unsatClassNames.add(cl.getIRI().getFragment());
            }
            if (!unsatClassNames.isEmpty()) {
                unsatClassesGCIs2.add(a);
                System.out.println("\n\nOWL axiom: " +a);
                System.out.println("adding it caused (" + unsatClassNames.size()  +
                                   ") classes to become unsatisfiable:\n " +
                                   unsatClassNames);
            }
            allUnsatClasses.addAll(unsatClassNames);
            m.put(a.toString(), unsatClassNames);

        }
        System.out.println("Number of problematic GCIs causing some classes to become unsat.: " +  unsatClassesGCIs2.size());
        System.out.println("Total number of unsat classes accounted for by individual axioms: " + allUnsatClasses.size());

    }



        private static HashSet<OWLAxiom> getGCIsCausingUnsatClassesCUMULATIVE(ArrayList<OWLAxiom> axioms) throws Exception {
                HashSet<String> unsatBeforeAddition = new HashSet<String>();
                HashSet<String> unsatAfterAddition = new HashSet<String>();
                HashSet<String> difference = new HashSet<String>();
                HashSet<OWLAxiom> problematicGCIs = new HashSet<OWLAxiom>();

                for(int i=0; i<axioms.size(); i++) {
                        OWLAxiom a = axioms.get(i);
                        manager.addAxiom(gro, a);
                reasoner.flush();
            reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
                Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
            Set<OWLClass> unsat = bottomNode.getEntitiesMinusBottom();
            unsatAfterAddition= new HashSet<String>();
            difference = new HashSet<String>();
                        for(OWLClass cl: unsat) {
                                unsatAfterAddition.add(cl.getIRI().getFragment());
                        }
                        for (String cl: unsatAfterAddition) {
                                if (!unsatBeforeAddition.contains(cl)) {
                                        difference.add(cl);
                                }
                        }


                        if (!difference.isEmpty()) {
                                problematicGCIs.add(a);
                                System.out.println("\n\ninput axiom no." + (i+1) + ": "  +a);
                                System.out.println("adding it caused (" +  difference.size() +
                                                ") classes to become unsatisfiable:\n " + difference);
                        }
                        unsatBeforeAddition = unsatAfterAddition;

                }

                System.out.println("Total number of unsat classes by the end: " + unsatAfterAddition.size());
                return problematicGCIs;
        }



        public static HashSet<OWLAxiom> getProblematicGCIs(ArrayList<OWLAxiom> axioms) throws Exception {
                loadGRO();
                HashSet<OWLAxiom> allProblematicGCIs = new HashSet<OWLAxiom>();
                HashSet<OWLAxiom> lastRoundProblematic;
                ArrayList<OWLAxiom> newAxioms = axioms;
                do {
                        loadGRO();
                        lastRoundProblematic = getGCIsCausingUnsatClassesCUMULATIVE(newAxioms);
                        allProblematicGCIs.addAll(lastRoundProblematic);
                        newAxioms = new ArrayList<OWLAxiom>();
                        for (OWLAxiom a: axioms) {
                                if(!allProblematicGCIs.contains(a)) {
                                        newAxioms.add(a);
                                }
                        }

                } while(!lastRoundProblematic.isEmpty());
                unsatClassesGCIs = allProblematicGCIs;
                return allProblematicGCIs;
        }




        /**
         * @param axioms
         * @return List of axioms that equals the input list minus the axioms causing unsat classes.
         * @throws Exception
         */
        public static ArrayList<OWLAxiom> filterOutAxiomsCausingUnsatClasses(ArrayList<OWLAxiom> axioms) throws Exception {
                Set<OWLAxiom> problematicGCIs = getProblematicGCIs(axioms);
                ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
                for (OWLAxiom a: axioms) {
                        if (!problematicGCIs.contains(a)) {
                                result.add(a);
                        }
                }
                return result;
        }



        public static ArrayList<OWLAxiom> filterOutAxiomsEntailedByOntology(ArrayList<OWLAxiom> axioms) throws OWLOntologyCreationException {
                loadGRO();
                ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
                ArrayList<OWLAxiom> entailed = getRedundantAxiomsDETAILED(axioms);
                for (OWLAxiom a: axioms) {
                        if (!entailed.contains(a)) {
                                result.add(a);
                        }
                }

                System.out.println("Number of axioms entailed by ontology:  "+ entailed.size());
                return result;
        }





        /**
         *
         * @param axioms
         * @param badRelNames
         * @return list of OWLAxioms that do not contain any of the bad relation names.
         * @throws OWLOntologyCreationException in case there was a problem loading the ontology.
         * @throws Exception
         */
        public static ArrayList<OWLAxiom> filterOutAxiomsWithBadRelName(ArrayList<OWLAxiom> axioms) throws OWLOntologyCreationException {
                Set<String> badRelNames = getBadRelationNames(axioms);
                ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
                int filteredOut = 0;
                outerloop: for (OWLAxiom a: axioms) {
                        String axStr = a.toString().toLowerCase();
                        for (String badRelName: badRelNames) {
                                if (axStr.indexOf(badRelName.toLowerCase()) > -1) {
                                        filteredOut++;
                                        continue outerloop;
                                }
                        }
                        result.add(a);
                }
                System.out.println(filteredOut + " axioms filtered out for containing bad relation names.");
                return result;
        }



        /**
         * Finds the bad relation names occuring the passed list of axioms. A relation name is bad if  it
         * does not occur in the ontology.
         *
         * @param axioms
         * @return A set containing the bad relations names.
         * @throws OWLOntologyCreationException
         * @throws Exception
         */

        public static HashSet<String> getBadRelationNames(ArrayList<OWLAxiom> axioms) throws OWLOntologyCreationException {
                loadGRO();
                HashSet<String> badRelNames = new HashSet<String>();
                Set<OWLObjectProperty> propertiesBefore = gro.getObjectPropertiesInSignature();
                for (OWLAxiom a: axioms) {
                        manager.addAxiom(gro, a);
                }
                Set<OWLObjectProperty> propertiesAfter = gro.getObjectPropertiesInSignature();
                for (OWLObjectProperty p: propertiesAfter) {
                        if (!propertiesBefore.contains(p)) {
                                badRelNames.add(p.toString());
                        }
                }
                return badRelNames;

        }





        public static ArrayList<OWLAxiom> getEntailedAxiomsContainingBadRelNames(ArrayList<OWLAxiom> axioms)
                        throws OWLOntologyCreationException {
             ArrayList<OWLAxiom> entailed = getRedundantAxiomsDETAILED(axioms);
             ArrayList<OWLAxiom> entailedWithoutBadRelNames = filterOutAxiomsWithBadRelName(entailed);
             ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
             for (OWLAxiom a:entailed) {
                 if (!entailedWithoutBadRelNames.contains(a)) {
                         result.add(a);
                 }
             }
             return result;
        }

        static ArrayList<OWLAxiom> getAxiomsViolatingSubClassRels(ArrayList<OWLAxiom> axioms,
			boolean considerOnlyDirectSubclasses) throws OWLException {
		loadGRO();
		helpers.print("in getAxiomsViolatingSubclassRels()....", 2);
		ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
		int disjointnessAxiomsForTwoClasses = 0;
		for (OWLAxiom ax: axioms) {
			OWLSubClassOfAxiom a = ((OWLSubClassOfAxiom) ax);
			//we're only looking at disjointness axioms:
			if(!a.getSuperClass().isBottomEntity()) {
				continue;
			}
			OWLClassExpression exp = a.getSubClass();
			Set<OWLClassExpression> conjuncts = exp.asConjunctSet();
			//helpers.print("number of conjuncts: " + conjuncts.size(), 3);
			Set<OWLClass> classConjuncts = new HashSet<OWLClass>();
			for (OWLClassExpression clsexp: conjuncts) {
				if (clsexp instanceof OWLClass) {
					classConjuncts.add((OWLClass) clsexp);
				}
			}
			if (classConjuncts.size()<2) {
				//if there are less than 2 class conjuncts in the 1st GCI operand, that GCIs cannot be in
				//violation of SubClass relation. we go to the next one.
				continue;
			}
			if (classConjuncts.size()>2) {
				helpers.print("Warning: The following axiom will not considered as it "
						+ "has more than 2 class conjuncts: " + a , 2);
				continue;
			}
			disjointnessAxiomsForTwoClasses++;
			Iterator<OWLClass> setIter = classConjuncts.iterator();
			OWLClass cl1 = setIter.next();
			OWLClass cl2 = setIter.next();
			Node<OWLClass> class1EquivalentClasses = reasoner.getEquivalentClasses(cl1);
			NodeSet<OWLClass> class1SuperClasses = reasoner.getSuperClasses(cl1, considerOnlyDirectSubclasses);
			NodeSet<OWLClass> class1SubClasses = reasoner.getSubClasses(cl1, considerOnlyDirectSubclasses);
			if (class1EquivalentClasses.getEntities().contains(cl2)) {
			   	//found one of the axioms fulfilling our criteria.
			   	result.add(a);
			    continue;
			}
		    if (class1SuperClasses.containsEntity(cl2)) {
		    	result.add(a);
		    	continue;
		    }
		    if (class1SubClasses.containsEntity(cl2)) {
		    	result.add(a);
		    	continue;
		    }
		 }
		helpers.print("number of binary class disjointness axioms considered: " +disjointnessAxiomsForTwoClasses, 2);
		return result;
	}



        public static void main(String[] args) throws Exception{

                initializeRecords();
                loadGRO();
                String exampleGCI = "(gci (and (exists HasPart (and)) (exists PerformsBindingToProtein (and))) "
                                + "(and (exists HasPart Protein_cncpt) "
                                + "(exists PerformsBindingToProtein (and Protein_cncpt Gene_cncpt)) (exists PerformsPositiveRegulation "
                                + "Transcription_cncpt) Protein_cncpt))";


                String example2 = "(gci (and Gene_cncpt Nucleus_cncpt) (bottom))";
                String example3 = "(gci (and (exists PerformsRegulatoryProcess (and)) Sequence_cncpt) (bottom))";
                String example4 = "(gci (and (exists HasPart (and)) "
                                + "(exists PerformsPositiveRegulation (and))) (and (exists HasPart Protein_cncpt) "
                                + "(exists PerformsBindingToProtein (and Protein_cncpt Gene_cncpt)) "
                                + "(exists PerformsPositiveRegulation Transcription_cncpt) Protein_cncpt))";

                String example5 = "(and (exists HasPart Protein_cncpt)"
                                + " (exists PerformsBindingToProtein (and Protein_cncpt Gene_cncpt)) "
                                + "(exists PerformsPositiveRegulation Transcription_cncpt) Protein_cncpt)";
                String example6 = "(gci (and (exists Encodes (and)) (exists PerformsPositiveRegulation (and))) (bottom))";
                String example7 = "(exists PerformsBinding Protein_cncpt)";

                String example8 = "(gci (and (exists FromSpecies Virus_cncpt) "
                                + "(exists PerformsPositiveRegulationOfGeneExpression (and))) (bottom))";

                ParserGCIs parser = new ParserGCIs(manager, factory, groIRI, INPUTFILE);

                ArrayList<String> parts = (ArrayList<String>) parser.getGciOperands(example8);
                System.out.println("GCI operands: ");
                System.out.println(parts);
                System.out.println("parsing GCI:");
                System.out.println(parser.parseGCI(example8));
                //System.out.println(gro);
                //System.out.println("PRINTING GRO:" + gro);
                //System.out.println(factory);


                //System.out.println("TESTING PARSE METHOD:");
                //System.out.println(parse(example3));


                //System.out.println("TESTING makeSubclassAxiom: ");
                //System.out.println(makeSubclassAxiom("Anas", "Elghafari"));


                /*System.out.println("TESTING parseExists");
                parseExists("(exists Encodes Chemical_cncpt)");
                parseExists("(exists PerformsPositiveRegulation (and))");*/

                /*
                System.out.println("parsing a GCI:");
                OWLAxiom oa1 = parseGCI("(gci (and Gene_cncpt Nucleus_cncpt) (bottom))");
                manager.addAxiom(gro, oa1);
                //System.out.println("PRINTING GRO:" + gro);


                OWLAxiom oa2 = parseGCI("(gci (and (exists PerformsRegulatoryProcess (and)) "
                                + "CellComponent_cncpt) (bottom))");
                manager.addAxiom(gro, oa2);

                OWLAxiom oa3= parseGCI("(gci (and (exists PerformsRegulatoryProcess (and)) ProteinComplex_cncpt)"
                                + " (exists PerformsRegulatoryProcess Gene_cncpt))");
                manager.addAxiom(gro, oa3);

                OWLAxiom oa4 = parseGCI("(gci (exists PerformsBinding (and)) (exists PerformsBinding Protein_cncpt))");
                manager.addAxiom(gro, oa4);

                */
        //System.out.println("reasoner:" + reasoner);


                reasoner.flush();
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
                boolean consistency = reasoner.isConsistent();
        System.out.println("\nconsistency (before adding any axioms): " + consistency);


        /*
        addInconsistency();
        reasoner.flush();
        consistency = reasoner.isConsistent();
        System.out.println("consistency: " + consistency);
        */




        /*
        System.out.println("testing fileToAxioms");
        ArrayList<OWLAxiom> axioms = fileToAxioms("C:\\Users\\Anas\\Desktop\\axiomsTest1.txt");
        System.out.println("number of axioms parsed: " + axioms.size());
        for(OWLAxiom a: axioms) {
                System.out.println(a);
        }*/




        //parsing the axioms from the file:
        //ArrayList<OWLAxiom> axioms = fileToAxioms("C:\\Users\\Anas\\Desktop\\GCIs-filtered.txt");
        ArrayList<OWLAxiom> axioms = parser.parseFile();
        System.out.println("number of GCIs parsed from file:" + axioms.size());
        OWLOntologyChangesVetoedListener vetoesListener = new OWLVetoesListener();
        manager.addOntologyChangesVetoedListener(vetoesListener);





        //testing which GCI causes which unsatisfiable classes:
        System.out.println("The following GCIs have caused the following classes to become unsat");
        //mapGCIsToUnsatClasses(axioms);
        //System.out.println(mapGCIsToUnsatClassesCUMULATIVE(axioms));

        /*
        HashSet<OWLAxiom> problematicAxioms = getProblematicGCIs(axioms);
        System.out.println("The following GCIs have caused unsat classes. " + problematicAxioms.size() + " GCIs:" );
        for(OWLAxiom a: problematicAxioms) {
                System.out.println("\nGCI: " + AxiomToGci.get(a.toString()));
                System.out.println("OWLAxiom: " + a);
        }

        System.out.println("Axioms that are found by cumulative function, not by the simple one");
        for (OWLAxiom a: unsatClassesGCIs) {
                if (!unsatClassesGCIs2.contains(a)) {
                        System.out.println(a);
                }
        }*/





        /*
        //adding the axioms:
        loadGRO();
        System.out.println("Axioms count in the ontology before adding GCIs: " + gro.getAxiomCount());
        //Set<OWLLogicalAxiom> groLogicalAxioms = gro.getLogicalAxioms();
        //System.out.println("\n\nLogical axioms already in GRO:\n");
        for (OWLLogicalAxiom la: groLogicalAxioms) {
                //System.out.println(la);
        }

        Set<OWLObjectProperty> propertiesBeforeAddition = new HashSet<OWLObjectProperty>();
        propertiesBeforeAddition = gro.getObjectPropertiesInSignature();
        Set<OWLClass> classesBeforeAddition = new HashSet<OWLClass>();
        classesBeforeAddition = gro.getClassesInSignature();
        for(OWLAxiom a: axioms) {
                if (unsatClassesGCIs2.contains(a)) {
                        continue;
                }
                ChangeApplied c = manager.addAxiom(gro, a);
                if(c == ChangeApplied.UNSUCCESSFULLY) {
                        System.out.println("This Axiom couldn't be added to the ontology:\n" + a);
                        System.out.println("original text form: " + AxiomToGci.get(a.toString()));
                        //OWLOntologyChangeVetoException reason =
                        //		((OWLVetoesListener) vetoesListener).getLastVeto();
                        //System.out.println("reason:" + reason);

                }
        }
        System.out.println("Axioms count after adding GCIs: " + gro.getAxiomCount());
        reasoner.flush();
        Set<OWLObjectProperty> propertiesAfterAddition = new HashSet<OWLObjectProperty>();
        propertiesAfterAddition = gro.getObjectPropertiesInSignature();
        Set<OWLClass> classesAfterAddition = new HashSet<OWLClass>();
        classesAfterAddition = gro.getClassesInSignature();
        System.out.println("\nNumber of new relations added to signature:" +
                 (propertiesAfterAddition.size()-propertiesBeforeAddition.size()) + "\n");
        for(OWLObjectProperty p: propertiesAfterAddition) {
                if (!propertiesBeforeAddition.contains(p)) {
                        System.out.println(p);
                }
        }

        System.out.println("\nNumber of new classes added to signature:" +
                   (classesAfterAddition.size() - classesBeforeAddition.size()) + "\n");
        for(OWLClass c: classesAfterAddition) {
                if (!classesBeforeAddition.contains(c)) {
                        System.out.println(c);
                }
        }
        */


        ArrayList<OWLAxiom> axioms2 = filterOutAxiomsWithBadRelName(axioms);
        ArrayList<OWLAxiom> axioms3 = filterOutAxiomsCausingUnsatClasses(axioms2);
        ArrayList<OWLAxiom> axioms4 = filterOutAxiomsEntailedByOntology(axioms3);
        helpers.print("Num of input axioms:" + axioms.size(),0);
        helpers.print("Num of axioms after removing those containing invalid names: " + axioms2.size(), 0);
        helpers.print("Num of axioms after removing those causing unsat classes: " + axioms3.size(), 0);
        helpers.print("Num of axioms after removing those entailed by GRO: " +  + axioms4.size(),0);
        helpers.print("Surviving axioms (Not containing bad rel name, not causing unsat classes, "
                        + "not entailed by GRO): \n\n", 0);
        for (OWLAxiom a: axioms4) {
                helpers.print("\n\nGCI: "+ AxiomToGci.get(a.toString()), 0);
                helpers.print(a,0);
        }



        /*
        //ArrayList<OWLAxiom> re = getRedundantAxioms(axioms);
        ArrayList<OWLAxiom> re = getRedundantAxiomsDETAILED(axioms);
        System.out.println("redundant axioms:");
        for (OWLAxiom a: re) {
                //System.out.println(a);
        }
        System.out.println("Number of redundant axioms:" + re.size());



        ArrayList<OWLAxiom> entailedByOthers = getAxiomsEntailedByOthers(axioms);
        //System.out.println("GCIs entailed by other GCIs: " + entailedByOthers);
        System.out.println("Count  of GCIs entailed by other GCIs in the input file: " + entailedByOthers.size());
        System.out.println("GCIs that follow only from other GCIs in the file (not from ontology):");
        for(OWLAxiom a: entailedByOthers) {
                if (!re.contains(a)) {
                        System.out.println(a);
                }
        }
        System.out.println("GCIs that follow only from other GCIs in the input file:" +
        (entailedByOthers.size()- re.size()));
        */







        //testing the reasoner, comment out as needed. only 1 of those 2 can be tested at one time
        //addInconsistency();
        //addUnsatisfiableClass();
        //addUnsatisfiableClassAsGCI();
        reasoner.flush();
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        consistency = reasoner.isConsistent();
        System.out.println("consistency:" + consistency);


        //following is copy-pasted from OWL examples:
        Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
        // This node contains owl:Nothing and all the classes that are
        // equivalent to owl:Nothing - i.e. the unsatisfiable classes. We just
        // want to print out the unsatisfiable classes excluding owl:Nothing,
        // and we can used a convenience method on the node to get these
        Set<OWLClass> unsatisfiable = bottomNode.getEntitiesMinusBottom();
        System.out.println("Count of unsat. classes: " + unsatisfiable.size());
        if (!unsatisfiable.isEmpty()) {
             System.out.println("The following classes are unsatisfiable: ");
             for (OWLClass cls : unsatisfiable) {
                 System.out.println(" " + cls);
             }
        }else {
                System.out.println("There are no unsatisfiable classes (after adding the axioms)");
        }







        /*
       //inspecting the GRO and comparing content to the GCI file
       Set<OWLObjectProperty> objectPropertiesLongForm = gro.getObjectPropertiesInSignature();
       Set<String> objectProperties = new HashSet<String>();
       System.out.println("\n\n\nObject properties in the GRO:");
       for(OWLObjectProperty p: objectPropertiesLongForm) {
           objectProperties.add(p.getIRI().getShortForm());
           System.out.println(p.getIRI().getShortForm());
       }

       System.out.println("\n\n\nObject properties extracted from file:");
       for(String propName: extractedPropertyNames) {
           System.out.println(propName);
       }

       for(String op: extractedPropertyNames) {
           if (objectProperties.contains(op)) {
                   System.out.println("The following GCI objectProperty is in  GRO:" + op);
           }
       }


       Set<String> gciClassNames = new HashSet<String>();
       Set<String> groClassNames = new HashSet<String>();
       for(OWLAxiom a: axioms) {
           OWLSubClassOfAxiom sca = (OWLSubClassOfAxiom) a;
           OWLClassExpression subclass = sca.getSubClass();
           OWLClassExpression superclass = sca.getSuperClass();
           //System.out.println(subclass.getClass());
           if(subclass instanceof OWLClass) {
                   //System.out.println("Proper subclass found: " + subclass);
                   gciClassNames.add(((OWLClass) subclass).getIRI().getShortForm());
           }

           else {
                   Set<OWLClassExpression> conjuncts = subclass.asConjunctSet();
                   for (OWLClassExpression e: conjuncts) {
                           if(e instanceof OWLClass) {
                                   //System.out.println("proper class found in conjunction: " + e);
                                   gciClassNames.add(((OWLClass) e).getIRI().getShortForm());
                           }
                   }
           }
           if(superclass instanceof OWLClass && !superclass.equals(factory.getOWLNothing())) {
                   //System.out.println("Proper superclass found: " + superclass);
                   gciClassNames.add(((OWLClass) superclass).getIRI().getShortForm());
           }

       }
       */




       /*
       System.out.println("\n\n\nAll class names found in the GCI file: ");
       for(String gciClassName: gciClassNames) {
           System.out.println(gciClassName);
       }
       System.out.println("count of proper class names in GCI file: " + gciClassNames.size());
       System.out.println("\n\n\nNames of classes occuring in GRO:");
       for(OWLClass c: gro.getClassesInSignature()) {
           String name = c.getIRI().getShortForm();
           System.out.println(name);
           groClassNames.add(name);
       }


       System.out.println("count of class names in GRO ontology: " + gro.getClassesInSignature().size());
       int classesNotInGRO = 0;
       for (String gciClassName: gciClassNames) {
           if (!groClassNames.contains(gciClassName)) {
                   System.out.println("GCI class not in GRO: " + gciClassName);
                   classesNotInGRO++;
           }
       }

       System.out.println("classes in GCI but not in GRO: " + classesNotInGRO);
       */
       ArrayList<OWLAxiom> axiomsViolatingSubclassness = getAxiomsViolatingSubClassRels(axioms, false);
       helpers.print("Number of axioms violating subclass relations: " + axiomsViolatingSubclassness.size(), 0);
       helpers.print(axiomsViolatingSubclassness, 0);

       System.out.println("REACHED END OF MAIN.");
     }


}
