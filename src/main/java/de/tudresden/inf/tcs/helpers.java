package de.tudresden.inf.tcs;

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Iterator;
import java.util.List;


public class helpers {

        static void print(String arg, int logLevel) {
                if (logLevel <= EvaluatingGCIs.LOGLEVEL) {
                        System.out.println(arg);
                }
        }


        static void print(Object o, int logLevel) {
                if(logLevel <= EvaluatingGCIs.LOGLEVEL) {
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


        static String[] fileToLines(String fileName) throws IOException {
                Path filePath = new File(fileName).toPath();
                Charset charset = Charset.defaultCharset();
                List<String> lines = Files.readAllLines(filePath, charset);
                return lines.toArray(new String[] {});
        }

}
