package cl.uc.dcc.leapfrog;

import java.util.Iterator;

import org.apache.jena.sparql.core.Var;
import org.apache.jena.tdb.solver.BindingNodeId;

public interface LFIterBindingNodeId extends Iterator<BindingNodeId> {

	public boolean seekBinding(BindingNodeId previousBinding, int firstChangedVarPos);
	public Var[] init(Var[] upperVars);
}