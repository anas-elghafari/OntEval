/**
 * 
 */


import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.parameters.ChangeApplied;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.util.SimpleIRIMapper;

import uk.ac.manchester.cs.owl.owlapi.OWLEquivalentClassesAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;

/** @author Anas Elghafari
 * This is an object-oriented version of EvaluatingGCIs. 
 * So instead of calling the static methods of EvaluatingGCIs.java, the user creates a GCIEvaluator object
 * (creating the object requires specifying IRI String, reference ontology file, GCI input file, initial log level)
 * 
 * This allows the user to have multiple GCIEvaluator objects, each with a different reference ontology and/or input
 * file. And allows concurrent testing on these different inputs.
 */


public class GCIEvaluator {
	
	//LOGLEVEL = 0  --> turn off most of the output. 
	//LOGLEVEL = 1 --> only the interesting results.
	//LOGLEVEL = 2 --> output that allows deeper look into the process... and so on.
	private int logLevel = 1;
	private String refOntFile;
	private String refOntIRIString;
	private String inputFile;
	public Level reasonerLogLevel = Level.ERROR;
	
	private OWLOntology refOnt;
	private OWLOntologyManager manager;
	private OWLDataFactory factory;
	private IRI referenceOntIRI;
    private OWLReasoner reasoner;
	private HashMap<String,String> axiomsToGcis;
	private HashSet<String> extractedClassNames;
	private HashSet<String> extractedPropertyNames;
	
	
	
	
	
	GCIEvaluator(String iriString, String refFile, String gciFile, int loglev) 
			throws OWLOntologyCreationException {
		this.refOntIRIString = iriString;
		this.refOntFile = refFile;
		this.inputFile = gciFile;
	    this.logLevel = loglev;
		initializeRecords();
		loadReferenceOntolgoy();
	}

	
	
	
	//if a different ontology is desired, change this method.
	//if a different reasoner is desired, change this method  (however, not everything is guaranteed to work 
	//in that case, as different reasoners may have different requirements in terms of flushing).
	void loadReferenceOntolgoy() throws OWLOntologyCreationException {
		manager = OWLManager.createOWLOntologyManager();
		referenceOntIRI = IRI.create(refOntIRIString);
		IRI fileIRI = IRI.create(new File(refOntFile));
		SimpleIRIMapper mapper = new SimpleIRIMapper(referenceOntIRI, fileIRI);
		manager.getIRIMappers().add(mapper);
		refOnt = manager.loadOntology(referenceOntIRI);
		factory = manager.getOWLDataFactory();
		OWLReasonerFactory reasonerFactory = new ElkReasonerFactory();
		reasoner = reasonerFactory.createReasoner(refOnt);
		Logger.getLogger("org.semanticweb.elk").setLevel(reasonerLogLevel);
	}
	
	
	
	
	
	void initializeRecords() {
		axiomsToGcis = new HashMap<String, String>();
		extractedClassNames = new HashSet<String>();
		extractedPropertyNames = new HashSet<String>();
	}
	
	
	
	public void setLogLevel(int newLogLevel) {
		this.logLevel = newLogLevel;
	}
	
	public int getLogLevel() {
		return this.logLevel;
	}
	
	
	public void setInputFile(String newInputFile) {
		inputFile = newInputFile;
	}
	
	public String getInputFile() {
		return inputFile;
	}
	
	
	
	//a method to create an inconsistency in the ontology, for testing purposes-
	private void addInconsistency() {
		OWLClass awake = factory.getOWLClass(IRI.create(referenceOntIRI + "#awake"));
		OWLClass asleep = factory.getOWLClass(IRI.create(referenceOntIRI + "#asleep"));
		OWLNamedIndividual john = factory.getOWLNamedIndividual(IRI.create(referenceOntIRI + "#John"));
		OWLClassAssertionAxiom johnAwake = factory.getOWLClassAssertionAxiom(awake, john);
		OWLClassAssertionAxiom johnAsleep = factory.getOWLClassAssertionAxiom(asleep, john);
		OWLDisjointClassesAxiom disjointness = factory.getOWLDisjointClassesAxiom(awake, asleep);
		manager.addAxiom(refOnt, johnAwake);
		manager.addAxiom(refOnt, johnAsleep);
		manager.addAxiom(refOnt, disjointness);
	}
	
	
	
	//a method to create an unsatisfiable calss in the ontology, for testing purposes-
    private void addUnsatisfiableClassAsGCI() {
    	    System.out.println("adding an unsatisfiable class as a GCI");
			OWLClass dead = factory.getOWLClass(IRI.create(referenceOntIRI + "#dead"));
			OWLClass alive = factory.getOWLClass(IRI.create(referenceOntIRI + "#alive"));
			OWLClass zombies = factory.getOWLClass(IRI.create(referenceOntIRI + "#zombies"));
			OWLSubClassOfAxiom zombiesDead = factory.getOWLSubClassOfAxiom(zombies, alive);
			OWLSubClassOfAxiom zombiesAlive = factory.getOWLSubClassOfAxiom(zombies, dead);
			OWLClassExpression intersectionDeadAlive = factory.getOWLObjectIntersectionOf(dead, alive);
			OWLSubClassOfAxiom intersectionSubclassBottom = factory.getOWLSubClassOfAxiom(intersectionDeadAlive, 
					factory.getOWLNothing());
			manager.addAxiom(refOnt, zombiesAlive);
			manager.addAxiom(refOnt, zombiesDead);
			manager.addAxiom(refOnt, intersectionSubclassBottom);
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
	
	
    
    
    private void addUnsatisfiableClass() {
		OWLClass dead = factory.getOWLClass(IRI.create(referenceOntIRI + "#dead"));
		OWLClass alive = factory.getOWLClass(IRI.create(referenceOntIRI + "#alive"));
		OWLClass zombies = factory.getOWLClass(IRI.create(referenceOntIRI + "#zombies"));
		OWLSubClassOfAxiom zombiesDead = factory.getOWLSubClassOfAxiom(zombies, alive);
		OWLSubClassOfAxiom zombiesAlive = factory.getOWLSubClassOfAxiom(zombies, dead);
		OWLDisjointClassesAxiom disjointness = factory.getOWLDisjointClassesAxiom(dead, alive);
		manager.addAxiom(refOnt, zombiesAlive);
		manager.addAxiom(refOnt, zombiesDead);
		manager.addAxiom(refOnt, disjointness);
	}

    
	
    OWLClass getClassFromName(String className) {
    	OWLClass c = factory.getOWLClass(IRI.create(referenceOntIRI + "#" + className));
    	return c;
    }
    
    
    /**
     * Method to identify axioms that are entailed by the reference ontology.
     * NOTE: this method does not work with the ELK reasoner, as that reasoner does not implement the  "isEntailed()" 
     * method. 
     * @param axioms: input GCIs
     * @return list of GCIs (as OWLAxiom objects) that are redundant with respects to the ontology (i.e. are entailed 
     * by the reference ontology).
     */
	public ArrayList<OWLAxiom> getEntailedGCIs(ArrayList<OWLAxiom> axioms) {
		ArrayList<OWLAxiom> redundant = new ArrayList<OWLAxiom>();
		for(OWLAxiom a:axioms) {
			if(reasoner.isEntailed(a)) {
				redundant.add(a);
			}
		}
		return redundant;
	}
	
	
	
	/**
	 * Method to identify axioms that are entailed by the reference ontology. It is called manual evaluation because 
	 * it does not use the reasoner method ".isEntailed" but rather parses the GCI and evaluates 
	 * whether or not it follows the ontology. Intended for use with reasoners like ELK which does not implement the
	 * isEntailed method.
	 * @param axioms: input GCIs.
	 * @return list of subclass axioms, disjointness axioms that follow from the reference ontology.
	 */
	
	ArrayList<OWLAxiom> getEntailedGCIsManualEval(ArrayList<OWLAxiom> axioms) {
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
			    		getOWLClass(IRI.create(referenceOntIRI + "#" + "DUMMY_CLASS" + dummyClassIndex));
			    equivSet.add(equivClass);
			    OWLEquivalentClassesAxiomImpl equiv = new OWLEquivalentClassesAxiomImpl(equivSet, 
			    		new HashSet<OWLAnnotation>());
			    manager.addAxiom(refOnt, equiv);
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
	
	
	
	
	ArrayList<OWLAxiom> getAxiomsEntailedByOthers(ArrayList<OWLAxiom> axioms) throws Exception {
		ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
		for(OWLAxiom a: axioms) {
			loadReferenceOntolgoy();
			addAllAxiomsExceptOne(axioms, a);
			reasoner.flush();
			ArrayList<OWLAxiom> excludedAxiom = new ArrayList<OWLAxiom>();
			excludedAxiom.add(a);
			ArrayList<OWLAxiom> redundant = getEntailedGCIsManualEval(excludedAxiom);
			if (!redundant.isEmpty()) {
				//System.out.println("found an axiom entailed by others: " + a);
				result.add(a);
			}
		}
		return result;
		
	}
	
	
	private void addAllAxiomsExceptOne(ArrayList<OWLAxiom> axioms, OWLAxiom excludedAxiom) {
		//adding the axioms:
        for(OWLAxiom a: axioms) {
        	if (a.equals(excludedAxiom)) {
        		//System.out.println("encountered the excluded axiom: " + a);
        		continue;
        	}
        	
        	ChangeApplied c = manager.addAxiom(refOnt, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		System.out.println("This Axiom couldn't be added to the ontology:\n" + a);
   		
        	}
        }
   }
	
	
	
	
	private HashSet<OWLAxiom> getIndividuallyProblematicGCIs(ArrayList<OWLAxiom> axioms, Set<OWLClass> excludedClasses) 
			throws OWLException {
		HashSet<OWLAxiom> problematicGCIs = new HashSet<OWLAxiom>();
		HashMap<OWLAxiom, HashSet<String>> m = new HashMap<OWLAxiom, HashSet<String>>();
		HashSet<String> allUnsatClasses = new HashSet<String>();
		for(OWLAxiom a: axioms) {
			loadReferenceOntolgoy();
			removeConceptsFromReferenceOntology(excludedClasses);
			ChangeApplied c = manager.addAxiom(refOnt, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		helpers.print("This Axiom couldn't be added to the ontology:\n" + a, 0);	
        	}
        	reasoner.flush();
        	Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
            Set<OWLClass> unsat = bottomNode.getEntitiesMinusBottom();
			HashSet<String> unsatClassNames = new HashSet<String>();
			for(OWLClass cl: unsat) {
				unsatClassNames.add(cl.getIRI().getShortForm());
			}
			if (!unsatClassNames.isEmpty()) {
				problematicGCIs.add(a);
				helpers.print("\n\nOWL axiom: " +a, 1);
				helpers.print("adding it caused (" + unsatClassNames.size()  + 
						") classes to become unsatisfiable:\n " + 
				unsatClassNames, 1);
			}
			allUnsatClasses.addAll(unsatClassNames);
			m.put(a, unsatClassNames);
			
		}
		System.out.println("Number of problematic GCIs causing unsat. classes: " +  problematicGCIs.size());
		System.out.println("Total number of unsat classes accounted for by individual axioms: " + allUnsatClasses.size());
		return problematicGCIs;
	}
	
	
	
	//private helper method.
	private HashSet<OWLAxiom> getGCIsCausingUnsatClassesCUMULATIVE(ArrayList<OWLAxiom> axioms, Set<OWLClass> excludedClasses) throws Exception {
		loadReferenceOntolgoy();
		removeConceptsFromReferenceOntology(excludedClasses);
		HashSet<String> unsatBeforeAddition = new HashSet<String>();
		HashSet<String> unsatAfterAddition = new HashSet<String>();
		HashSet<String> difference = new HashSet<String>();
		HashSet<OWLAxiom> problematicGCIs = new HashSet<OWLAxiom>();
		
		for(int i=0; i<axioms.size(); i++) {
			OWLAxiom a = axioms.get(i);
			ChangeApplied c = manager.addAxiom(refOnt, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		helpers.print("In function mapGCI: This Axiom couldn't be added to the ontology:\n" + a, 0);	
        	}
        	reasoner.flush();
            reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        	Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
            Set<OWLClass> unsat = bottomNode.getEntitiesMinusBottom(); 
            unsatAfterAddition= new HashSet<String>();
            difference = new HashSet<String>();
			for(OWLClass cl: unsat) {
				unsatAfterAddition.add(cl.getIRI().getShortForm());
			}
			for (String cl: unsatAfterAddition) {
				if (!unsatBeforeAddition.contains(cl)) {
					difference.add(cl);
				}
			}
			
						
			if (!difference.isEmpty()) {
				problematicGCIs.add(a);
				helpers.print("\n\ninput axiom no." + (i+1) + ": "  +a, 3);
				helpers.print("adding it caused (" +  difference.size() +
						") classes to become unsatisfiable:\n " + difference, 3);
			}
			unsatBeforeAddition = unsatAfterAddition;
			
		}
		
		helpers.print(problematicGCIs, 3);
		return problematicGCIs;
	}
	
	
	
	
	/**
	 * Method to identify the set of GCIs that are collcetively respobsible for unsatisfiable classes.
	 * The result is a set of OWLAxiom, if that set is removed the input GCIs, the input will no longer cause any 
	 * unsat. classes.
	 * 
	 * @param axioms: list of GCIs.
	 * @param classesToBeRemoved: set of classes to be removed from the ontology before identifying collcetively 
	 * problematic GCIs
	 * @return Set of OWLAxiom. That set is the non-minimal set responsible for unsat classes.
	 * @throws Exception: if the ontology cannot be loaded correctly.
	 */
	public HashSet<OWLAxiom> getCollectivelyProblematicGCIs(ArrayList<OWLAxiom> axioms, Set<OWLClass> classesToBeRemoved) throws Exception {
		loadReferenceOntolgoy();
		HashSet<OWLAxiom> problematicGCIs = new HashSet<OWLAxiom>();
		HashSet<OWLAxiom> lastRoundProblematic;
		ArrayList<OWLAxiom> newAxioms = axioms;
		do {
			lastRoundProblematic = getGCIsCausingUnsatClassesCUMULATIVE(newAxioms, classesToBeRemoved);
			problematicGCIs.addAll(lastRoundProblematic);
			newAxioms = new ArrayList<OWLAxiom>();
			for (OWLAxiom a: axioms) {
				if(!problematicGCIs.contains(a)) {
					newAxioms.add(a);
				}
			}
			
		} while(!lastRoundProblematic.isEmpty());
		return problematicGCIs;
	}
	
	
	
	
	/**
	 * @param axioms
	 * @return List of axioms that equals the input list minus the axioms causing unsat classes. 
	 * @throws Exception
	 */
	public ArrayList<OWLAxiom> filterOutAxiomsCausingUnsatClasses(ArrayList<OWLAxiom> axioms) throws Exception {
		Set<OWLAxiom> problematicGCIs = getCollectivelyProblematicGCIs(axioms, null);
		ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
		for (OWLAxiom a: axioms) {
			if (!problematicGCIs.contains(a)) {
				result.add(a);
			}
		}
		return result;
	}
	
	
	
	public ArrayList<OWLAxiom> filterOutAxiomsEntailedByOntology(ArrayList<OWLAxiom> axioms) throws OWLOntologyCreationException {
		loadReferenceOntolgoy();
		ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
		ArrayList<OWLAxiom> entailed = getEntailedGCIsManualEval(axioms);
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
	public ArrayList<OWLAxiom> filterOutAxiomsWithBadRelName(ArrayList<OWLAxiom> axioms) throws OWLOntologyCreationException {
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
	public HashSet<String> getBadRelationNames(ArrayList<OWLAxiom> axioms) throws OWLOntologyCreationException {
		loadReferenceOntolgoy();
		HashSet<String> badRelNames = new HashSet<String>();
		Set<OWLObjectProperty> propertiesBefore = refOnt.getObjectPropertiesInSignature();
		for (OWLAxiom a: axioms) {
			ChangeApplied c = manager.addAxiom(refOnt, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		throw new IllegalArgumentException("This Axiom could not be added to the ontology: " + a);
        		
        	}
		}
		Set<OWLObjectProperty> propertiesAfter = refOnt.getObjectPropertiesInSignature();
		for (OWLObjectProperty p: propertiesAfter) {
			if (!propertiesBefore.contains(p)) {
				badRelNames.add(p.toString());
			}
		}
		return badRelNames;
		
	}
	
	
	
	
	
	public ArrayList<OWLAxiom> getEntailedAxiomsContainingBadRelNames(ArrayList<OWLAxiom> axioms) 
			throws OWLOntologyCreationException {
	     ArrayList<OWLAxiom> entailed = getEntailedGCIsManualEval(axioms);
	     ArrayList<OWLAxiom> entailedWithoutBadRelNames = filterOutAxiomsWithBadRelName(entailed);
	     ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
	     for (OWLAxiom a:entailed) {
	    	 if (!entailedWithoutBadRelNames.contains(a)) {
	    		 result.add(a);
	    	 }
	     }
	     return result;
	}
	
	
	
	
	OWLOntology createOntologyWithGCIsAsAxioms(ArrayList<OWLAxiom> axioms) throws OWLOntologyCreationException{
		helpers.print("Creating an ontology containing only the GCIs as TBox", 2);
		helpers.print("Count of GCIs: " + axioms.size(), 2);
		OWLOntologyManager m = OWLManager.createOWLOntologyManager();
		OWLOntology gciOnt = m.createOntology(); 
		Set<OWLAxiom> axiomsSet = new HashSet<OWLAxiom>(axioms);
		m.addAxioms(gciOnt, axiomsSet);
		return gciOnt;
	}
	
	
	
	private OWLReasoner getELKReasonerForOntology(OWLOntology o) {
		OWLReasonerFactory rf = new ElkReasonerFactory();
		OWLReasoner r = rf.createNonBufferingReasoner(o);
		return r;
	}
	
	
	
	ArrayList<OWLAxiom> getGroAxiomsEntailedByGCIs(OWLOntology gciOnt) throws OWLException {
		loadReferenceOntolgoy();
		OWLReasoner r = getELKReasonerForOntology(gciOnt);
		ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
		int groAxioms = refOnt.getAxiomCount();
		int disjointnessAxioms = 0;
		int subclassAxioms = 0;
		int equivclassAxioms = 0;
		for (OWLAxiom ax: refOnt.getAxioms(AxiomType.DISJOINT_CLASSES))  {
			disjointnessAxioms++;
			OWLDisjointClassesAxiom a = (OWLDisjointClassesAxiom) ax;
			Set<OWLClassExpression> s = a.getClassExpressions();
			OWLObjectIntersectionOf intersection = factory.getOWLObjectIntersectionOf(s);
			if (r.getEquivalentClasses(intersection).contains(factory.getOWLNothing())) {
				helpers.print("Found a (disjointness) GRO axiom that follows from the GCIs: "  + a, 3);
				result.add(a);
			}
		}
		
		for (OWLAxiom ax:refOnt.getAxioms(AxiomType.EQUIVALENT_CLASSES)) {
			equivclassAxioms++;
			OWLEquivalentClassesAxiomImpl a = (OWLEquivalentClassesAxiomImpl) ax;
			Set<OWLClassExpression> equivClasses = a.getClassExpressions();
			//helpers.print("equivalent classes: " + equivClasses,0);
			Iterator<OWLClassExpression> t = equivClasses.iterator();
			OWLClassExpression ce1 = t.next();
			OWLClassExpression ce2 = t.next();
			OWLClass dummyEquivClass1 = factory.getOWLClass(IRI.create(referenceOntIRI + "#DUMMY-EQUIVClass1-" + equivclassAxioms ));
			OWLClass dummyEquivClass2 = factory.getOWLClass(IRI.create(referenceOntIRI + "#DUMMY-EQUIVClass2-" + equivclassAxioms));
			Set<OWLClassExpression> equivSet1 = new HashSet<OWLClassExpression>();
			equivSet1.add(ce1);
			equivSet1.add(dummyEquivClass1);
			OWLEquivalentClassesAxiomImpl equiv1 = new OWLEquivalentClassesAxiomImpl(equivSet1, 
		    		new HashSet<OWLAnnotation>());
			manager.addAxiom(gciOnt, equiv1);
			Set<OWLClassExpression> equivSet2 = new HashSet<OWLClassExpression>();
			equivSet2.add(ce2);
			equivSet2.add(dummyEquivClass2);
			OWLEquivalentClassesAxiomImpl equiv2 = new OWLEquivalentClassesAxiomImpl(equivSet2, 
					new HashSet<OWLAnnotation>());
			manager.addAxiom(gciOnt, equiv2);
			r.flush();
			if(r.getEquivalentClasses(dummyEquivClass1).contains(dummyEquivClass2)) {
				helpers.print("Found a (equivalence) GRO axiom that follows from the GCIs: "  + a, 3);
				result.add(a);
			}
		}
		
		for (OWLAxiom ax: refOnt.getAxioms(AxiomType.SUBCLASS_OF)) {
			subclassAxioms++;
			OWLSubClassOfAxiom a = (OWLSubClassOfAxiom) ax;
			OWLClassExpression superclass = a.getSuperClass();
			OWLClassExpression subclass = a.getSubClass();
			//we will create dummy super class and dummy subclass, and we'll add them as equivalent
			//classes to the sub- and super classexpressions we have. reason: in case the sub/super classexpressions
			//happen to be not proper classes. Because the reasoner getSubClasses does not return a classexpression as 
			// a subclass.
			
			//using "evaluatedGroAxioms" as kind of an index to differentiate different dummy classes.
			OWLClass dummySuper = factory.getOWLClass
					(IRI.create(referenceOntIRI + "#DUMMY-SUPERCLASS" + subclassAxioms));
			Set<OWLClassExpression> equivSetSuper = new HashSet<OWLClassExpression>();
			equivSetSuper.add(dummySuper);
			equivSetSuper.add(superclass);
			OWLEquivalentClassesAxiomImpl equivSuper = new OWLEquivalentClassesAxiomImpl(equivSetSuper, 
		    		new HashSet<OWLAnnotation>());
			OWLClass dummySub = factory.getOWLClass(IRI.create(referenceOntIRI + "#DUMMY-SUBCLASS" +subclassAxioms));
			Set<OWLClassExpression> equivSetSub = new HashSet<OWLClassExpression>();
			equivSetSub.add(dummySub);
			equivSetSub.add(subclass);
			OWLEquivalentClassesAxiomImpl equivSub = new OWLEquivalentClassesAxiomImpl(equivSetSub, 
		    		new HashSet<OWLAnnotation>());
			manager.addAxiom(gciOnt,  equivSuper);
		    manager.addAxiom(gciOnt, equivSub);
		    r.flush();
		    
			if(r.getSubClasses(dummySuper, false).containsEntity((OWLClass) dummySub)) {
				helpers.print("Found a (subclass) GRO axiom that follows from the GCIs: "  + a, 3);
				result.add(a);
			}
	    }
		
		
		int evaluatedGroAxioms = disjointnessAxioms + subclassAxioms + equivclassAxioms;
		helpers.print("Finished checking if GRO axioms follow from input GCIs.", 1);
		helpers.print("Total number of GRO axioms: " + groAxioms, 1);
		helpers.print("Number of GRO axioms that were evaluated  (disjointess axioms, subclassof axioms, equivalence axioms): " + evaluatedGroAxioms, 1);
		helpers.print("Number of GRO axioms found to follow from GCIs: " + result.size(), 1);
		return result;
		
	}
	
	
	
	
	void countRelevantGROAxioms(ArrayList<OWLAxiom> axioms) throws OWLException {
		loadReferenceOntolgoy();
		ArrayList<OWLAxiom> axiomsWithGCIconcpets = new ArrayList<OWLAxiom>();
		ArrayList<OWLAxiom> axiomsWithOnlyGCIconcepts = new ArrayList<OWLAxiom>();
		Set<OWLClass> conceptsInGCIs = new HashSet<OWLClass>();
		for(OWLAxiom a:axioms) {
			conceptsInGCIs.addAll(a.getClassesInSignature());
		}
		
		for (OWLAxiom a:refOnt.getAxioms()) {
			Set<OWLClass> classesInAxiomSig = a.getClassesInSignature();
			helpers.print("Classes in axiom signature: " + classesInAxiomSig, 3);
			boolean aConceptIsInCommon = false;
			boolean propersubset = true;
			for (OWLClass c: classesInAxiomSig) {
				aConceptIsInCommon = false;
				if (conceptsInGCIs.contains(c)) {
					aConceptIsInCommon = true;
				}else {
					//if one concept in the signature of an axiom does not occur in GCI concepts,
					//we flag this:
					propersubset = false;
					
				}
			}
			if(aConceptIsInCommon) {
				axiomsWithGCIconcpets.add(a);
			}
			//we need both conditionals, because if the axiom signature is empty or contains no classes, the
			//propersubset value will still be "true". 
			if(aConceptIsInCommon && propersubset) {
				axiomsWithOnlyGCIconcepts.add(a);
			}
		}
		helpers.print("Number of GRO axioms:" + refOnt.getAxiomCount(), 0);
		helpers.print("Number of GRO axioms containing a concpet that occurs in GCIs:" + axiomsWithGCIconcpets.size() , 0);
		helpers.print("Number of GRO axioms continains only "
				+ "concepts that occur in GCIs:" +  axiomsWithOnlyGCIconcepts.size(), 0);
		helpers.print("\n\nGRO axioms containing a GCI concept: ", 0);
		helpers.print(axiomsWithGCIconcpets, 0);
		helpers.print("\n\nGRO axioms containing only GCI concepts: ", 0);
		helpers.print(axiomsWithOnlyGCIconcepts, 0);
	}
	
	
	
	
	private void printEquivalentClasses(String classname) {
		OWLClass c = factory.getOWLClass(IRI.create(referenceOntIRI + "#" + classname));
		helpers.print("classes equivalent to " + classname, 0);
		helpers.print(reasoner.getEquivalentClasses(c), 0);
	}
	
	
	private void printSuperClasses(String classname) {
		OWLClass c = factory.getOWLClass(IRI.create(referenceOntIRI + "#" + classname));
		helpers.print("super classes of " + classname, 0);
		helpers.print(reasoner.getSuperClasses(c, false), 0);
	}

	private void printSubClasses(String classname) {
		OWLClass c = factory.getOWLClass(IRI.create(referenceOntIRI + "#" + classname));
		helpers.print("sub classes of "  + classname, 0);
		helpers.print(reasoner.getSubClasses(c, false), 0);
	}
	
	private void printDisjointClasses(String classname) {
		OWLClass c = factory.getOWLClass(IRI.create(referenceOntIRI + "#" + classname));
		helpers.print("classes disjoint with:  "  + classname, 0);
		for (OWLClass c2: refOnt.getClassesInSignature()) {
			OWLObjectIntersectionOf intersection = factory.getOWLObjectIntersectionOf(new HashSet<OWLClass>(Arrays.asList(c, c2)));
			if (reasoner.getEquivalentClasses(intersection).contains(factory.getOWLNothing())) {
				helpers.print(c2, 0);
			}
		}
		//helpers.print(reasoner.getDisjointClasses(c), 0);
	}
	
	
	ArrayList<OWLAxiom> getAxiomsViolatingSubClassRels(ArrayList<OWLAxiom> axioms,
			boolean considerOnlyDirectSubclasses) throws OWLException {
		loadReferenceOntolgoy();
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
		helpers.print("number of axioms in the input list: " + axioms.size(), 2);
		helpers.print("number of binary class disjointness axioms considered: " +disjointnessAxiomsForTwoClasses, 2);
		return result;
	}
	
	
	
	/**
	 * @param axioms
	 * @return list of axioms of the form ((and CLASS ROLE-Expression) (bottom)) that
	 * violate GRO.
	 */
	ArrayList<OWLAxiom> getAxiomsViolatingRoleRels(ArrayList<OWLAxiom> axioms) {
		ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
		int consideredAxioms = 0;
		for(OWLAxiom ax: axioms) {
			OWLSubClassOfAxiom a = ((OWLSubClassOfAxiom) ax);
			//we're only looking at disjointness axioms:
			if(!a.getSuperClass().isBottomEntity()) {
				continue;
			}
			OWLClassExpression exp = a.getSubClass();
			Set<OWLClassExpression> conjuncts = exp.asConjunctSet();
			if (conjuncts.size()!=2) {
				//we're only looking at axioms with 2 conjuncts.
				continue;
			}
			Iterator<OWLClassExpression> t = conjuncts.iterator();
			OWLClassExpression conj1 = t.next();
			OWLClassExpression conj2 = t.next();
			if((conj1 instanceof OWLClass && conj2 instanceof OWLClass) ||
				(!(conj1 instanceof OWLClass) && !(conj2 instanceof OWLClass))) {
				//if both conjuncts are classes, or neither is a class,
				//then the axiom is not the form we are looking for.
				continue;
			}
			
			helpers.print("axiom to be evaluated: ", 3);
			helpers.print(a, 3);
			consideredAxioms++;
			OWLClass cls;
			OWLClassExpression clexp;
			if(conj1 instanceof OWLClass) {
				cls = ((OWLClass) conj1);
				clexp = conj2;
			}
			else {//conj2 is OWLClass
				cls = ((OWLClass) conj2);
				clexp = conj1;
			}
			
			//addin a dummy class that is equivalent to the class expression
			OWLClass dummy = factory.getOWLClass(IRI.create(referenceOntIRI + "#" + "DUMMY" + consideredAxioms));
			Set<OWLClassExpression> equivSet = new HashSet<OWLClassExpression>();
		    equivSet.add(dummy);
		    equivSet.add(clexp);
		    OWLEquivalentClassesAxiomImpl equiv = new OWLEquivalentClassesAxiomImpl(equivSet, 
		    		new HashSet<OWLAnnotation>());
		    manager.addAxiom(refOnt, equiv);
		    reasoner.flush();
		    NodeSet<OWLClass> clsSuperclasses = reasoner.getSuperClasses(cls, false); 
		    NodeSet<OWLClass> clsSubclasses = reasoner.getSubClasses(cls, false);
		    Node<OWLClass> clsEquivclasses = reasoner.getEquivalentClasses(cls);
		    if(clsSuperclasses.containsEntity(dummy) || 
		    		clsSubclasses.containsEntity(dummy) ||
		    		clsEquivclasses.contains(dummy)) {
		    	helpers.print("Found a GCI that violates role relations: ", 3);
		    	helpers.print(a, 3);
		    	result.add(a);
		    }
		    
		}
		helpers.print("Number of axioms evaluated to see if they violate role relations: " + consideredAxioms, 2);
		return result;
	}
	
	
	void addAxiomsToOntology(List<OWLAxiom> axioms) {
		for(OWLAxiom a: axioms) {
        	ChangeApplied c = manager.addAxiom(refOnt, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		helpers.print("This Axiom couldn't be added to the ontology:\n" + a, 0);
        		helpers.print("input form: " + axiomsToGcis.get(a.toString()), 0);
        	}
        }
	}
	
	boolean checkOntologyConsistency() {
		reasoner.flush();
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        
		return reasoner.isConsistent();
	}

	
	/**
	 * calling this method causes re-loading the GRO ontology from file. So any added axioms are lost.
	 * @throws OWLException
	 */
	void compareGCIclassNamesWithGRO() throws OWLException {
		loadReferenceOntolgoy();
		helpers.print("number of classes appearing in input file: " + extractedClassNames.size(), 0);
		helpers.print("number of classes appearing in ontology: " + refOnt.getClassesInSignature().size(), 0);
		Set<String> invalidClassNames = new HashSet<String>();
		Set<String> groClassNames = new HashSet<String>();
		for (OWLClass c: refOnt.getClassesInSignature()) {
			groClassNames.add(c.getIRI().getShortForm());
		}
		for (String s: extractedClassNames) {
			if (!groClassNames.contains(s)) {
				invalidClassNames.add(s);
			}
		}
		helpers.print("classes appearing in input file but not in ontology: " + invalidClassNames, 0);
		
	}
	
	
	/**
	 * calling this method causes re-loading the GRO ontology from file. So any added axioms are lost.
	 * @throws OWLException
	 */
	void compareGCIPropertyNamesWithGRO() throws OWLException {
		loadReferenceOntolgoy();
		helpers.print("number of object properties appearing in input file: " + extractedPropertyNames.size(), 0);
		helpers.print("number of object proerties appearing in ontology: " + refOnt.getObjectPropertiesInSignature().size(), 0);
		Set<String> invalidPropNames = new HashSet<String>();
		Set<String> groPropertyNames = new HashSet<String>();
		for (OWLObjectProperty p: refOnt.getObjectPropertiesInSignature()) {
			groPropertyNames.add(p.getIRI().getShortForm());
		}
		for (String s: extractedPropertyNames) {
			if (!groPropertyNames.contains(s)) {
				invalidPropNames.add(s);
			}
		}
		helpers.print("obj properties appearing in input file but not in ontology: " + invalidPropNames, 0);
		
	}
	
	
	
	public void removeConceptsFromReferenceOntology(Set<OWLClass> classesToBeRemoved) throws OWLException {
		if(classesToBeRemoved == null || classesToBeRemoved.isEmpty()) {
			return;
		}
		
		loadReferenceOntolgoy();
		helpers.print("Number of classes in reference ontology BEFORE removal: " + refOnt.getClassesInSignature().size(), 2);
		helpers.print("Number of axioms in reference ontology BEFORE removal: " + refOnt.getAxiomCount(), 2);

		Set<OWLAxiom> referenceOntAxioms = refOnt.getAxioms();
		for (OWLAxiom a: referenceOntAxioms) {
			Set<OWLClass> classesInAxiom = a.getClassesInSignature();
			for (OWLClass c: classesInAxiom) {
				if (classesToBeRemoved.contains(c)) {
					//then the axiom is something we need to remove since it involves a disallowed concept.
					manager.removeAxiom(refOnt, a);
				}
			}
		}
		helpers.print("Number of classes in reference ontology AFTER removal: " + refOnt.getClassesInSignature().size(), 2);
		helpers.print("Number of axioms in reference ontology AFTER removal: " + refOnt.getAxiomCount(), 2);
	}
	
	
	
	
	public void runAllTests(int newLogLevel) throws Exception {
		setInputFile(inputFile);
		setLogLevel(newLogLevel);
		initializeRecords();
		loadReferenceOntolgoy();
		
		helpers.print("Running all tests:", 1);
		helpers.print("Log leve: " + logLevel, 0);
		helpers.print("input file: " + inputFile, 0);
		
		
		//parsing file:
		ParserGCIs parser = new ParserGCIs(manager, factory, referenceOntIRI, inputFile);
		ArrayList<OWLAxiom> axioms = parser.parseFile();
        helpers.print("number of GCIs parsed from input file:" + axioms.size(), 0);
        axiomsToGcis = parser.getMappingAxiomsToGcis();
        extractedClassNames = parser.getExtractedClassNames();
        extractedPropertyNames = parser.getExtractedPropertyNames();
        
        
        //comparing class and property names from the input file with those in the ontology:
        compareGCIclassNamesWithGRO();
        compareGCIPropertyNamesWithGRO();
        
        
        //checking consistency, before and after adding the axioms:
        helpers.print("NEXT TEST:", 0);
        boolean consistencyBefore = checkOntologyConsistency();
        helpers.print("\nConsistency (before adding any axioms): " + consistencyBefore, 0);
        addAxiomsToOntology(axioms);
		boolean consistencyAfter = checkOntologyConsistency();
        helpers.print("\nConsistency (after adding the axioms): " + consistencyAfter, 0);
        
        
        //checking for unsat classes:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
        Set<OWLClass> unsatisfiable = bottomNode.getEntitiesMinusBottom();
        helpers.print("Count of unsat. classes: " + unsatisfiable.size(), 0);
        if (!unsatisfiable.isEmpty()) {
             helpers.print("The following classes are unsatisfiable: ", 0);
             for (OWLClass cls : unsatisfiable) {
            	 helpers.print(" " + cls, 0);
             }
        }
        
        
        //locating the GCIs that, by themselves, cause unsat classes:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        helpers.print("Identifying the GCIs that -individually- cause unsat classes:", 0);
        getIndividuallyProblematicGCIs(axioms, null);
        
        
        //locating a set of GCIs whose removal prevents unsat classes from occuring:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        helpers.print("Identifying a set of GCIs that -collectively- cause unsat classes:", 0);
        Set<OWLAxiom> unsatClassGCIs = getCollectivelyProblematicGCIs(axioms, null);
        helpers.print("size of GCI set (non-minimal) that needs to be removed to get rid of unsat classes:_" + unsatClassGCIs.size() , 0);
        for(OWLAxiom a: unsatClassGCIs) {
        	helpers.print(a, 0);
        }
        
        
        //Checking UNSAT classes if the reference ontology was restricted to classes occuring in GCI file:
        helpers.print("\n\n\n\nNEXT TEST: ", 0);
        helpers.print("Restricting the reference ontology to only the classess appearing the GCI file, then checking unsat. classes again.", 0);
        Set<OWLClass> classesToRemove = helpers.subtractSets(refOnt.getClassesInSignature(), helpers.classNamesToClasses(extractedClassNames));
        removeConceptsFromReferenceOntology(classesToRemove);
        addAxiomsToOntology(axioms);
        reasoner.flush();
        Node<OWLClass> bottomNodeAfter = reasoner.getBottomClassNode();
        Set<OWLClass> unsatAfterRemoval = bottomNodeAfter.getEntitiesMinusBottom();
        helpers.print("Count of classes in the ontology after restriction: " + refOnt.getClassesInSignature().size() , 0);
        helpers.print("Count of axioms in the ontology after restriction: " + refOnt.getAxiomCount(), 0);
        helpers.print("Count of unsatisfiable classes after restriction: " + unsatAfterRemoval.size(), 0);
        if (!unsatAfterRemoval.isEmpty()) {
            helpers.print("The following classes are unsatisfiable: ", 0);
            for (OWLClass cls : unsatAfterRemoval) {
           	 helpers.print(" " + cls, 0);
            }
       }
        
        
        
        //locating the GCIs that, by themselves, cause unsat classes:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        helpers.print("AFTER RESTRICTING ONTOLOGY TO CLASSES IN GCI, identifying the GCIs that -individually- cause unsat classes:", 0);
        getIndividuallyProblematicGCIs(axioms, classesToRemove);
        
        
        //locating a set of GCIs whose removal prevents unsat classes from occuring:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        helpers.print("AFTER RESTRICTING ONTOLOGY TO CLASSES IN GCI, identifying a set of GCIs that -collectively- cause unsat classes:", 0);
        Set<OWLAxiom> unsatClassGCIsAfterRestriction = getCollectivelyProblematicGCIs(axioms, classesToRemove);
        helpers.print("size of GCI set (non-minimal) that needs to be removed to get rid of unsat classes:_" + unsatClassGCIsAfterRestriction.size() , 0);
        for(OWLAxiom a: unsatClassGCIsAfterRestriction) {
        	helpers.print(a, 0);
        }
        
        
        
        //locating GCIs entailed by the ontology:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        loadReferenceOntolgoy();
        ArrayList<OWLAxiom> axiomsEntaildByOnt = getEntailedGCIsManualEval(axioms);
        helpers.print("Number of GCIs entailed by the ontology: " + axiomsEntaildByOnt.size(), 0);
        helpers.print("List of GCIs entailed by Ontology: ", 1);
        for (OWLAxiom a: axiomsEntaildByOnt){
        	helpers.print(axiomsToGcis.get(a.toString()), 1);
        	helpers.print(a.toString() + "\n", 1);
        }
        
        
        
        
        //Identifying GCIs that neither follow form the ontology nor cause unsatisfiable classes:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        ArrayList<OWLAxiom> axiomsMinusUnsatClassGCIs = filterOutAxiomsCausingUnsatClasses(axioms);
        ArrayList<OWLAxiom> axiomsMinusUnsatAndEntailed = filterOutAxiomsEntailedByOntology(axiomsMinusUnsatClassGCIs); 
        helpers.print("GCIs that neither cause unsat classes nor follow from GRO. "
        		+ "size: " + axiomsMinusUnsatAndEntailed.size(), 0);
        for (OWLAxiom a: axiomsMinusUnsatAndEntailed) {
        	helpers.print(axiomsToGcis.get(a.toString()), 0);
        }
        
        
        
        //Axioms violating subclass relations:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        ArrayList<OWLAxiom> axiomsViolatingSubclassness = getAxiomsViolatingSubClassRels(axioms, false);
        helpers.print("Number of GCIs violating subclass relations: " + axiomsViolatingSubclassness.size(), 0);
        helpers.print(axiomsViolatingSubclassness, 0);
        
        //Axioms violating direct subclass relations:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        axiomsViolatingSubclassness = getAxiomsViolatingSubClassRels(axioms, true);
        helpers.print("Number of GCIs violating (direct) subclass relations: " + axiomsViolatingSubclassness.size(), 0);
        helpers.print(axiomsViolatingSubclassness, 0);
        
        ////Axioms violating role relations:
        helpers.print("\n\n\n\nNEXT TEST:", 0);
        ArrayList<OWLAxiom> axiomsViolatingRoles = getAxiomsViolatingRoleRels(axioms);
        helpers.print("number of GCIs violating GRO role relations: " + axiomsViolatingRoles.size(), 0);
		helpers.print(axiomsViolatingRoles, 0);
		
		
		//Counting relevant GRO axioms:
		helpers.print("\n\n\n\nNEXT TEST:", 0);
		countRelevantGROAxioms(axioms);
		
		///GRO axioms that follow from the GCIs:
		helpers.print("\n\n\n\nNEXT TEST:", 0);
		OWLOntology gciOnt = createOntologyWithGCIsAsAxioms(axioms);
		ArrayList<OWLAxiom> groAxiomsEntailedByGCIs = getGroAxiomsEntailedByGCIs(gciOnt);
		helpers.print("GRO axioms entailed by the GCIs: ", 0);
		helpers.print(groAxiomsEntailedByGCIs, 0);
		
	}
	
	
	
	
	
	public static void main(String[] args) throws Exception{
		//the 4 args to the constructor: IRI string, reference ontology file, input (GCIs)file, log level.
		GCIEvaluator evaluator1 = new GCIEvaluator("http://www.bootstrep.eu/ontology/GRO",
		                                           "C:\\Users\\Anas\\Desktop\\GRO_latest.xml",
		                                           "C:\\Users\\Anas\\Desktop\\role-depth1_top50", 1);
                evaluator1.runAllTests(2); //we can specify a different log level here.
		System.out.println("REACHED END OF MAIN.");
      
     }


}
