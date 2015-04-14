/**
 * 
 */


import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyChangeVetoException;
import org.semanticweb.owlapi.model.OWLOntologyChangesVetoedListener;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.parameters.ChangeApplied;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.util.SimpleIRIMapper;

import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;


/** @author Anas Elghafari
 *
 */
public class EvaluatingGCIs {
	
	private static OWLOntology gro;
	private static OWLOntologyManager manager;
	private static OWLDataFactory factory;
	private static IRI groIRI;
    private static OWLReasoner reasoner;
	private static HashMap<String,String> AxiomToGci;
	
	
	
	static void loadGRO() throws Exception {
		manager = OWLManager.createOWLOntologyManager();
		groIRI = IRI.create("http://www.bootstrep.eu/ontology/GRO");
		IRI fileIRI = IRI.create(new File("C:\\Users\\Anas\\Desktop\\GRO_latest.xml"));
		SimpleIRIMapper mapper = new SimpleIRIMapper(groIRI, fileIRI);
		manager.getIRIMappers().add(mapper);
		gro = manager.loadOntology(groIRI);
		factory = manager.getOWLDataFactory();
		AxiomToGci = new HashMap<String, String>();
		OWLReasonerFactory reasonerFactory = new ElkReasonerFactory();
		reasoner = reasonerFactory.createReasoner(gro);
	}
	
	
	
	public static OWLSubClassOfAxiom parseGCI(String exp){
		System.out.println("\nGCI:" + exp);
		ArrayList<String> operands = (ArrayList<String>) getGciOperands(exp);
		System.out.println("operands: " + operands);
		/*
		if(operands.get(1).equals("(bottom)")) {
			ArrayList<String> disjointClassesOperands = getGciOperands(operands.get(0));
			System.out.println("DISJOINT CLASSES OPERANDS:" + disjointClassesOperands);
		}*/
		
		OWLClassExpression subclass = getOWLClass(operands.get(0));
		OWLClassExpression superclass = getOWLClass(operands.get(1));
		OWLSubClassOfAxiom axiom = factory.getOWLSubClassOfAxiom(subclass, superclass);
		System.out.println("Corresponding OWL axiom:" + axiom);
		return axiom;
	}
	
	
	
	
	
	
	private static OWLClassExpression parseExists(String exp) {
		//8 because it's the length of "(exists "
		String propertyName = exp.substring(8, exp.lastIndexOf(" "));
		OWLObjectProperty p = factory.getOWLObjectProperty(IRI.create(groIRI + 
				"#" + propertyName));
		OWLClassExpression c;
		
		if(exp.indexOf("and") == -1) {
			String className = exp.substring(exp.lastIndexOf(" ") +1 , exp.length()-2);
			//this must go through the recursive getOWLClass (rather than the
			//factory.getOWLClass () because className might be a conjunction
		    c = getOWLClass(className);
		}
		else {
			c = factory.getOWLThing();
		}
		
		OWLClassExpression ce = factory.getOWLObjectSomeValuesFrom(p, c);
		//System.out.println("\nIn parseExists()");
		//System.out.println("property:" + p + ", class:" + c.toString());
		//System.out.println("expression of existential restriction: " +ce);
		return ce;
	}
	
	
	
	/*
	private static OWLClassExpression parseAND(String exp) {
		if(exp.substring(1).indexOf("(") == -1) {
			String conj1Name = exp.substring(1, exp.indexOf(" "));
			String conj2Name = exp.substring(exp.indexOf(" ")+1, exp.length()-1);
			System.out.println("conjunct 1 is:" + conj1Name + " conjunct 2 is:" + conj2Name);
			OWLClass conj1class = factory.getOWLClass(IRI.create(groIRI + "#" + conj1Name));
			OWLClass conj2class = factory.getOWLClass(IRI.create(groIRI + "#" + conj2Name));
			OWLClassExpression intersection = factory.getOWLObjectIntersectionOf(conj1class, conj2class);
			return intersection;
			
		}
		else {
			return null;
		}
		
		
	}*/
	
	
	
	
	private static  OWLClassExpression getOWLClass(String exp) {
		ArrayList<String> operands =  getAndOperands(exp, true);
		if(operands.size() == 1) {
			if(operands.get(0).equals("(bottom)")) {
				return factory.getOWLNothing();
			}
			else {
				OWLClass result = factory.
					getOWLClass(IRI.create(groIRI + "#" + operands.get(0)));
			    return result;
			}
		}
		
		if(operands.get(0).endsWith("exists")) {
			OWLClassExpression result = parseExists(exp);
			return result;
		}
	
		if(operands.get(0).endsWith("and")) {
			HashSet<OWLClassExpression> expressionsList = 
					new HashSet<OWLClassExpression>();
			for(int i =1; i<operands.size(); i++) {
				String s = operands.get(i);
				OWLClassExpression operandResult = getOWLClass(s);
				expressionsList.add(operandResult);
			}
			OWLClassExpression result = factory.getOWLObjectIntersectionOf(expressionsList);
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
	
	
	
	
	/*
	 * 
	 */
	public static ArrayList<String> getAndOperands(String exp, boolean operatorIncluded) {
		//System.out.println("expression now is:" + exp);
		ArrayList<String> operands = new ArrayList<String>();
		if(exp.indexOf(" ") == -1) {
			//System.out.println("BASE CASE");
			operands.add(exp);
			return operands;
		}
		
		String operandsString;
		//operators part starts after the space that separates operator from operands
		if(operatorIncluded) {
			String operator = exp.substring(0,  exp.indexOf(" "));
			operands.add(operator);
			operandsString = exp.substring(exp.indexOf(" ")+1, exp.length()-1);
		}
		else {
			operandsString = exp;
		}
		
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


		String firstArg = operandsString.substring(0, splitPoint);
		String rest = operandsString.substring(splitPoint+1);
		operands.add(firstArg);
		operands.addAll(getAndOperands(rest, false));
		return operands;		
	}
	
	
	
	
	public static ArrayList<String> getGciOperands(String exp) {
		String operandsString = exp.substring(exp.indexOf(" (")+1, exp.length()-1);
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
			NodeSet<OWLClass> zombiesSuperclass = reasoner.getSuperClasses(zombies, true);
			Node<OWLClass> zombiesEquivalent = reasoner.getEquivalentClasses(zombies);
			System.out.println("zombies superclass:" + zombiesSuperclass);
			System.out.println("zombies equivalentclasses:" + zombiesEquivalent);
			
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
		int bottomAsSuperclass = 0;
	    int topAsSuperclass = 0;
	    int topNotSuperclass = 0;
	    int singleSuperclass = 0;
	    int superclassIsExpression = 0;
	    
		for(OWLAxiom a: axioms){
			OWLSubClassOfAxiom axiom = (OWLSubClassOfAxiom) a;
			if (axiom.getSuperClass().equals(factory.getOWLNothing())) {
				disjointnessAxioms++;
			    OWLClassExpression subclass = axiom.getSubClass();
			    NodeSet<OWLClass> inferredSuperclasses = reasoner.getSuperClasses(subclass, false);
			    Node<OWLClass> inferredEquivalentclasses = reasoner.getEquivalentClasses(subclass);
			    System.out.println("\nDisjointness Axiom: " + a.toString());
			    System.out.println("superclasses of the subclass: "+ inferredSuperclasses);
			    
			    if (inferredSuperclasses.containsEntity(factory.getOWLNothing())  ||
			    	inferredEquivalentclasses.contains(factory.getOWLNothing())) {
			    	System.out.println("Bottom found as a superclass!!");
			    	redundant.add(axiom);
			    	bottomAsSuperclass++;
			    }
			    
			    if (inferredSuperclasses.containsEntity(factory.getOWLThing())) {
			    	topAsSuperclass++;
			    }else {
			    	topNotSuperclass++;
			    }
			   
			    
			    if (inferredSuperclasses.isSingleton()) {
			    	singleSuperclass++;
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
			
			else {

				
				OWLClassExpression subclass = axiom.getSubClass();
				OWLClassExpression superclass = axiom.getSuperClass();
			    NodeSet<OWLClass> inferredSuperclasses = reasoner.getSuperClasses(subclass, false);
			    Node<OWLClass> inferredEquivalentclasses = reasoner.getEquivalentClasses(subclass);
			    if (!superclass.getClass().equals(OWLClass.class)) {
			    	System.out.println("Superclass of the axiom is an expression, not a class");
			    	superclassIsExpression++;
			    	continue;
			    }
			    
			    if (inferredSuperclasses.containsEntity((OWLClass) superclass) ||
			        inferredEquivalentclasses.contains((OWLClass) superclass)) {
			    	System.out.println("Redundant axiom found!!" );
			    	redundant.add(axiom);
			    }
			    System.out.println("\nSubclass Axiom: " + a.toString());
			    System.out.println("superclasses of the subclass: "+ inferredSuperclasses);
			    System.out.println("equivalent classes to the subclass:" + inferredEquivalentclasses);
			    
			}
		}
		
		System.out.println("Total number of axioms: " + axioms.size());
        System.out.println("number of disjointness axioms: " + disjointnessAxioms);
	    System.out.println("number of times bottom was found as superclass: " + bottomAsSuperclass);
	    System.out.println("number of times top was found as superclass: " + topAsSuperclass);
	    System.out.println("number of time top was not a superclass: " + topNotSuperclass);
		System.out.println("number of casese with only 1 superclass:" + singleSuperclass);
		System.out.println("number of redundant suclassof axioms:" +  redundant.size());
		System.out.println("number of axioms where the superclass is an expression:" + superclassIsExpression);
		
		return redundant;
    }
	
	
	
	
	
	
	public static void main(String[] args) throws Exception{
		
		loadGRO();
		
		/*
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
		
		ArrayList<String> parts = (ArrayList<String>) getGciOperands(example6);
		System.out.println("operands: ");
		System.out.println(parts);
		*/
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
		
		
		boolean consistency = reasoner.isConsistent();
        System.out.println("consistency (before adding any axioms): " + consistency);
        
        
        /*
        addInconsistency();
        reasoner.flush();
        consistency = reasoner.isConsistent();
        System.out.println("consistency: " + consistency);
        */
        
        
        
        /*
        System.out.println("testing fileToLines: ");
        String[] lines = fileToLines("C:\\Users\\Anas\\Desktop\\axiomsTest1.txt");
        System.out.println("number of lines:" + lines.length);
        for(String l: lines) {
        	System.out.println(l);
        }
        */
        
        
        /*
        System.out.println("testing fileToAxioms");
        ArrayList<OWLAxiom> axioms = fileToAxioms("C:\\Users\\Anas\\Desktop\\axiomsTest1.txt");
        System.out.println("number of axioms parsed: " + axioms.size());
        for(OWLAxiom a: axioms) {
        	System.out.println(a);
        }*/
        
        
        //adding the axioms from the file:
        ArrayList<OWLAxiom> axioms = fileToAxioms("C:\\Users\\Anas\\Desktop\\yue_role-depth-1");
        System.out.println("Axioms count before adding GCIs: " + gro.getAxiomCount());
        System.out.println("number of GCIs parsed from file:" + axioms.size());
        OWLOntologyChangesVetoedListener vetoesListener = new OWLVetoesListener();
    	manager.addOntologyChangesVetoedListener(vetoesListener);
    	
    	
    	
    	/*
        for(OWLAxiom a: axioms) {
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
        */
        
    	//ArrayList<OWLAxiom> re = getRedundantAxioms(axioms);
        ArrayList<OWLAxiom> re = getRedundantAxiomsDETAILED(axioms);
    	System.out.println("REDUNDANT AXIOMS: " + re);
        
        //testing the reasoner, comment out as needed. only 1 of those 2 can be tested at one time
        //addInconsistency();
        //addUnsatisfiableClass();    
        addUnsatisfiableClassAsGCI();        
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
        if (!unsatisfiable.isEmpty()) {
             System.out.println("The following classes are unsatisfiable: ");
             for (OWLClass cls : unsatisfiable) {
            	 System.out.println(" " + cls);
             }
        } else {
        	System.out.println("There are no unsatisfiable classes");
        }
        
     }

}
