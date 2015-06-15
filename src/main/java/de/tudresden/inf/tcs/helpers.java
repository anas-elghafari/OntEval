import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClass;



/**
 * @author Anas
 *
 *Class for some helper methods. Helper meaning the methods here abstract away from some basic operations but 
 *do not affect the logic of the evaluation process.
 */
public class helpers {
	
	static void print(String arg, int logLevel) {
		if (logLevel <= EvaluatingGCIs.getLogLevel()) {
			System.out.println(arg);
		}
	}
	
	
	static void print(Object o, int logLevel) {
		if(logLevel <= EvaluatingGCIs.getLogLevel()) {
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
	}
	
	
	
	static Set<OWLClass> subtractSets(Set<OWLClass> subtractFrom, Set<OWLClass> subtracted) {
		Set<OWLClass> result =  new HashSet<OWLClass>();
		for (OWLClass c: subtractFrom) {
			if(!subtracted.contains(c)) {
				result.add(c);
			}
		}
		return result;
	}
 	
	
	static Set<OWLClass> classNamesToClasses(Set<String> classNames) {
		Set<OWLClass> result = new HashSet<OWLClass>();
		for (String cname: classNames) {
			result.add(EvaluatingGCIs.getClassFromName(cname));
		}
		return result;
	}
	
	
	static String[] fileToLines(String fileName) throws IOException {
		Path filePath = new File(fileName).toPath();
		Charset charset = Charset.defaultCharset();        
		List<String> lines = Files.readAllLines(filePath, charset);
		return lines.toArray(new String[] {});
	}

}
