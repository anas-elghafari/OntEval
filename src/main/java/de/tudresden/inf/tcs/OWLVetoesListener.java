package de.tudresden.inf.tcs;

import java.util.ArrayList;
import java.util.List;

import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.OWLOntologyChangeVetoException;
import org.semanticweb.owlapi.model.OWLOntologyChangesVetoedListener;

public class OWLVetoesListener implements OWLOntologyChangesVetoedListener {

        private ArrayList<OWLOntologyChange> ontChanges;
        private ArrayList<OWLOntologyChangeVetoException> rejections;

    public OWLVetoesListener() {
        ontChanges = new ArrayList<OWLOntologyChange>();
        rejections = new ArrayList<OWLOntologyChangeVetoException>();
    }


        @Override
        public void ontologyChangesVetoed(
                        List<? extends OWLOntologyChange> changes,
                        OWLOntologyChangeVetoException veto) {
                ontChanges.addAll(changes);
                rejections.add(veto);

        }

        public OWLOntologyChangeVetoException getLastVeto() {
                //System.out.println("rejections: " + rejections.toString());
                return rejections.get(rejections.size()-1);
        }

}
