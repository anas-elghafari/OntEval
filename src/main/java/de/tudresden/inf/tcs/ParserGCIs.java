package de.tudresden.inf.tcs;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;



public class ParserGCIs {

        private OWLOntologyManager manager;
        private OWLDataFactory factory;
        private IRI groIRI;
        private HashMap<String,String> AxiomToGci;
        private HashSet<String> extractedClassNames;
        private HashSet<String> extractedPropertyNames;
        private String inputFileName;
        private String[] inputFileLines;



        ParserGCIs(OWLOntologyManager m, OWLDataFactory f, IRI i, String n) {
                manager = m;
                factory =  f;
                groIRI = i;
                inputFileName = n;
                AxiomToGci = new HashMap<String, String>();
                extractedClassNames =  new HashSet<String>();
                extractedPropertyNames = new HashSet<String>();

        }


        public ArrayList<OWLAxiom> parseFile() throws IOException, OntException {
                ArrayList<OWLAxiom> result = new ArrayList<OWLAxiom>();
                String[] lines = helpers.fileToLines(inputFileName);
                inputFileLines = lines;
                helpers.print("parsing input file...", 3);
                for(String line: lines) {
                        helpers.print("line now is:" + line + "END OF LINE", 3);
                        if(line.isEmpty()) {
                                continue;
                        }
                        OWLAxiom a = parseGCI(line);
                        AxiomToGci.put(a.toString(), line);
                        result.add(a);
                }
                return result;
        }


        public OWLSubClassOfAxiom parseGCI(String exp) throws OntException{
                helpers.print("\n\ninput GCI: " + exp, 2);
                ArrayList<String> operands = (ArrayList<String>) getGciOperands(exp);
                helpers.print("In parseGCI, operands: " + operands, 3);
                OWLClassExpression subclass = getOWLClass(operands.get(0));
                OWLClassExpression superclass = getOWLClass(operands.get(1));
                OWLSubClassOfAxiom axiom = factory.getOWLSubClassOfAxiom(subclass, superclass);
                helpers.print("OWL axiom: " + axiom, 2);
                return axiom;
        }



        OWLClassExpression parseExists(String exp) throws OntException {
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
                helpers.print("\nIn parseExists()", 3);
                helpers.print("property:" + p + ", class:" + c.toString(), 3);
                helpers.print("expression of existential restriction: " +ce, 3);
                return ce;
        }



        static ArrayList<String> getAndOperands(String e) {
                String exp = e.trim();
                String operandsString = exp.substring(5, exp.length()-1);
                //5 because that's the length of "(and"
                helpers.print("\nin getAndOperands(), expression is: " + exp, 3);
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
                helpers.print("split points for and expression: " + splitPoints, 3);
                helpers.print("AND operands: " + operands, 3);
                return operands;
        }




        static ArrayList<String> getGciOperands(String exp) {
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


        OWLClassExpression getOWLClass(String e) throws OntException {
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
                                OWLClass result = factory.getOWLClass(IRI.create(groIRI + "#" + fixedExp));
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


                //"exists" case:
                if(exp.startsWith("(exists")) {
                        OWLClassExpression result = parseExists(exp);
                        return result;
                }

           //if this happens, the input is not well-formed.
           throw new OntException("The input GCI (" + e + ") is not well-formed.");
        }


}
