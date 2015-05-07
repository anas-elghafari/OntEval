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
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.omg.CORBA.INITIALIZE;
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
import org.semanticweb.owlapi.model.OWLOntologyChangeVetoException;
import org.semanticweb.owlapi.model.OWLOntologyChangesVetoedListener;
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

/** @author Anas
 *
 */
public class EvaluatingGCIs {
	
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
	
	
	
	private static void p(String arg) {
		System.out.println(arg);
	}
	
	
	private static void p(Object o) {
		if (o instanceof Iterable<?>) {
			Iterator<?> i = ((Iterable<?>)o).iterator();
			while(i.hasNext()) {
				System.out.println(i.next());
			}
		}
		else {
			System.out.println(o);
		}
	}
	
	
	
	
	static void loadGRO() throws OWLOntologyCreationException {
		manager = OWLManager.createOWLOntologyManager();
		groIRI = IRI.create("http://www.bootstrep.eu/ontology/GRO");
		IRI fileIRI = IRI.create(new File("C:\\Users\\Anas\\Desktop\\GRO_latest.xml"));
		SimpleIRIMapper mapper = new SimpleIRIMapper(groIRI, fileIRI);
		manager.getIRIMappers().add(mapper);
		gro = manager.loadOntology(groIRI);
		factory = manager.getOWLDataFactory();
		OWLReasonerFactory reasonerFactory = new ElkReasonerFactory();
		reasoner = reasonerFactory.createReasoner(gro);
		Logger.getLogger("org.semanticweb.elk").setLevel(Level.ERROR);
	}
	
	
	
	
	
	static void initializeRecords() {
		AxiomToGci = new HashMap<String, String>();
		unsatClassesGCIs = new HashSet<OWLAxiom>();
		unsatClassesGCIs2 = new HashSet<OWLAxiom>();
		extractedClassNames = new HashSet<String>();
		extractedPropertyNames = new HashSet<String>();
	}
	
	
	
	
	public static OWLSubClassOfAxiom parseGCI(String exp){
		//System.out.println("\n\ninput GCI: " + exp);
		ArrayList<String> operands = (ArrayList<String>) getGciOperands(exp);
		//System.out.println("In parseGCI, operands: " + operands);
		/*
		if(operands.get(1).equals("(bottom)")) {
			ArrayList<String> disjointClassesOperands = getGciOperands(operands.get(0));
			System.out.println("DISJOINT CLASSES OPERANDS:" + disjointClassesOperands);
		}*/
		
		OWLClassExpression subclass = getOWLClass(operands.get(0));
		OWLClassExpression superclass = getOWLClass(operands.get(1));
		OWLSubClassOfAxiom axiom = factory.getOWLSubClassOfAxiom(subclass, superclass);
		//System.out.println("OWL axiom: " + axiom);
		return axiom;
	}
	
	
	
	
	
	
	private static OWLClassExpression parseExists(String exp) {
		//8 because it's the length of "(exists "
		String propertyName = exp.substring(8, exp.indexOf(" ", 8));
		propertyName =  propertyName.substring(0, 1).toLowerCase() + propertyName.substring(1);
		OWLObjectProperty p = factory.getOWLObjectProperty(IRI.create(groIRI + 
				"#" + propertyName));
		extractedPropertyNames.add(propertyName);
		int startIndx = 8+ propertyName.length() +1;
		String classPart = exp.substring(startIndx, exp.length()-1);
		OWLClassExpression c;
		
		if(classPart.startsWith("(and)")) {
			c = factory.getOWLThing();
		}
		else {
			//this must go through the recursive getOWLClass (rather than the
			//factory.getOWLClass () because className might be a conjunction
		    c = getOWLClass(classPart);
		}
		
		OWLClassExpression ce = factory.getOWLObjectSomeValuesFrom(p, c);
		//System.out.println("\nIn parseExists()");
		//System.out.println("property:" + p + ", class:" + c.toString());
		//System.out.println("expression of existential restriction: " +ce);
		return ce;
	}
	
	
		
	
	
	private static  OWLClassExpression getOWLClass(String e) {
		String exp = e.trim();
		
		//base case: single concept or "bottom"
		if(exp.indexOf(" ") == -1) {
			
			if(exp.equals("(bottom)")) {
				return factory.getOWLNothing();
			}
			else {
				String fixedExp = exp;
				if(exp.endsWith("_cncpt")) {
					fixedExp = exp.substring(0, exp.length()-6);
				}
				extractedClassNames.add(fixedExp);
				OWLClass result = factory.
						getOWLClass(IRI.create(groIRI + "#" + fixedExp));
				return result;
			}
		}
	
		//"and" case:
		if(exp.startsWith("(and")) {
			ArrayList<String> operands =  getAndOperands(exp);
			HashSet<OWLClassExpression> expressionsList = new HashSet<OWLClassExpression>();
			for(int i =0; i<operands.size(); i++) {
				String s = operands.get(i);
				OWLClassExpression operandResult = getOWLClass(s);
				expressionsList.add(operandResult);
			}
			OWLClassExpression result = factory.getOWLObjectIntersectionOf(expressionsList);
			return result;
		}
		
		
		//"exist" case:
		if(exp.startsWith("(exists")) {
			OWLClassExpression result = parseExists(exp);
			return result;		
		}
		
	   //if this happens, the input is not well-formed.
	   return null;
	}
	
	
	
	
	
	
	
	/*
	static OWLAxiom makeSubclassAxiom(String subclassName, String superclassName) {
		OWLClass subclass = factory.getOWLClass(IRI.create(groIRI + "#" + subclassName));
		OWLClass superclass = factory.getOWLClass(IRI.create(groIRI + "#" + superclassName));
		 // Now create the axiom
		 OWLAxiom axiom = factory.getOWLSubClassOfAxiom(subclass, superclass);
		 return axiom;
	}
	*/
	
	/*
	static OWLAxiom makeSubclassAxiom2(String subName, String superName) {
		//following is modified from examples on github
		OWLObjectProperty hasPart = factory.getOWLObjectProperty(IRI
				.create(base + "#hasPart"));
				OWLClass nose = factory.getOWLClass(IRI.create(base + "#Nose"));
				// Now create a restriction to describe the class of individuals that
				// have at least one part that is a kind of nose
				OWLClassExpression hasPartSomeNose = factory
				.getOWLObjectSomeValuesFrom(hasPart, nose);
				// Obtain a reference to the Head class so that we can specify that
				// Heads have noses
				OWLClass head = factory.getOWLClass(IRI.create(base + "#Head"));
				// We now want to state that Head is a subclass of hasPart some Nose, to
				// do this we create a subclass axiom, with head as the subclass and
				// "hasPart some Nose" as the superclass (remember, restrictions are
				// also classes - they describe classes of individuals -- they are
				// anonymous classes).
				OWLSubClassOfAxiom ax = factory.getOWLSubClassOfAxiom(head,
				hasPartSomeNose);
	}*/
	
	
	
	
	
	public static ArrayList<String> getAndOperands(String e) {
		String exp = e.trim();
		String operandsString = exp.substring(5, exp.length()-1);
		//5 because that's the length of "(and"
		//System.out.println("\nexpression now is:" + exp);
		ArrayList<String> operands = new ArrayList<String>();
		ArrayList<Integer> splitPoints = new ArrayList<Integer>();
			
		if(operandsString.indexOf("(") == -1) {
			operands.addAll(Arrays.asList(operandsString.split("\\s+")));
		}
		else {
			operandsString += " "; //makes parsing easier
			int bracketsCount = 0;
			for (int i= 0; i<operandsString.length(); i++) {
				if (operandsString.charAt(i) == '(') {
					bracketsCount++;
				}
				if (operandsString.charAt(i) == ')') {
					bracketsCount--;
				}
				if (bracketsCount== 0 && operandsString.charAt(i)==' ') {
					splitPoints.add(i);
				}
			}
		}
		
		int lastSplit = 0;
		for (int split: splitPoints) {
			operands.add(operandsString.substring(lastSplit, split).trim());
			lastSplit = split;
		}
		//System.out.println("split points" + splitPoints);
		//System.out.println("AND operands: " + operands);
		return operands;
	}
	
	
	
	public static ArrayList<String> getGciOperands(String exp) {
		String operandsString = exp.substring(exp.indexOf("(gci ")+5, exp.length()-1);
		int bracketsCount = 0;
		int splitPoint = 0;
		for(int i= 0; i<operandsString.length(); i++) {
			if (operandsString.charAt(i) == '(') {
				bracketsCount++;
			}
			if (operandsString.charAt(i) == ')') {
				bracketsCount--;
			}
			
			if (bracketsCount == 0 && operandsString.charAt(i) == ' ') {
				splitPoint = i;
				break;
			}
		}
		ArrayList<String> result = new ArrayList<String>();
		result.add(operandsString.substring(0, splitPoint));
		result.add(operandsString.substring(splitPoint+1));
		return result;
		
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

    
	private static String[] fileToLines(String fileName) throws IOException {
		Path filePath = new File(fileName).toPath();
		Charset charset = Charset.defaultCharset();        
		List<String> lines = Files.readAllLines(filePath, charset);
		for(String l: lines) {
			inputFileAsString += l;
		}
		return lines.toArray(new String[] {});
	}
	
	
	
	
	static ArrayList<OWLAxiom> fileToAxioms(String fileName) throws IOException {
		ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
		String[] lines = fileToLines(fileName);
		for(String line: lines) {
			//System.out.println("line now is:" + line + "END OF LINE");
			if(line.isEmpty()) {
				continue;
			}
			OWLAxiom a = parseGCI(line);
			AxiomToGci.put(a.toString(), line);
			result.add(a);
		}
		return result;
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
        	
        	ChangeApplied c = manager.addAxiom(gro, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		System.out.println("This Axiom couldn't be added to the ontology:\n" + a);
   		
        	}
        }
   }
	
	
	
	
	private static void mapGCIsToUnsatClasses(ArrayList<OWLAxiom> axioms) throws Exception {
		HashMap<String, HashSet<String>> m = new HashMap<String, HashSet<String>>();
		HashSet<String> allUnsatClasses = new HashSet<String>();
		for(OWLAxiom a: axioms) {
			loadGRO();
			ChangeApplied c = manager.addAxiom(gro, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		System.out.println("This Axiom couldn't be added to the ontology:\n" + a);	
        	}
        	reasoner.flush();
        	Node<OWLClass> bottomNode = reasoner.getUnsatisfiableClasses();
            Set<OWLClass> unsat = bottomNode.getEntitiesMinusBottom();
			HashSet<String> unsatClassNames = new HashSet<String>();
			for(OWLClass cl: unsat) {
				unsatClassNames.add(cl.getIRI().getShortForm());
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
			ChangeApplied c = manager.addAxiom(gro, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		System.out.println("In function mapGCI: This Axiom couldn't be added to the ontology:\n" + a);	
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
			ChangeApplied c = manager.addAxiom(gro, a);
        	if(c == ChangeApplied.UNSUCCESSFULLY) {
        		throw new IllegalArgumentException("This Axiom could not be added to the ontology: " + a);
        		
        	}
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
		
		ArrayList<String> parts = (ArrayList<String>) getGciOperands(example8);
		System.out.println("GCI operands: ");
		System.out.println(parts);
		System.out.println("parsing GCI:");
		System.out.println(parseGCI(example8));
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
        ArrayList<OWLAxiom> axioms = fileToAxioms("C:\\Users\\Anas\\Desktop\\yue_role-depth-1");
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
        p("Num of input axioms:" + axioms.size()); 
        p("Num of axioms after removing those containing invalid names: " + axioms2.size());
        p("Num of axioms after removing those causing unsat classes: " + axioms3.size());
        p("Num of axioms after removing those entailed by GRO: " +  + axioms4.size());
        p("Surviving axioms (Not containing bad rel name, not causing unsat classes, "
        		+ "not entailed by GRO): \n\n");
        for (OWLAxiom a: axioms4) {
        	p("\n\nGCI: "+ AxiomToGci.get(a.toString()));
        	p(a);
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
       
   
       System.out.println("REACHED END OF MAIN.");
     }

}
