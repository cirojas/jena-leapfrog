package cl.uc.dcc.leapfrog;

import java.util.Iterator;

import org.apache.jena.sparql.algebra.Op;
import org.apache.jena.sparql.algebra.op.OpBGP;
import org.apache.jena.sparql.algebra.op.OpFilter;
import org.apache.jena.sparql.algebra.op.OpConditional;
import org.apache.jena.sparql.algebra.op.OpQuadPattern;
import org.apache.jena.sparql.core.BasicPattern;
import org.apache.jena.sparql.core.Var;
import org.apache.jena.sparql.engine.binding.Binding;
import org.apache.jena.sparql.engine.optimizer.reorder.ReorderTransformation;
import org.apache.jena.sparql.expr.Expr;
import org.apache.jena.sparql.expr.ExprList;
import org.apache.jena.tdb.solver.BindingNodeId;
import org.apache.jena.tdb.solver.BindingTDB;
import org.apache.jena.tdb.store.NodeId;
import org.apache.jena.tdb.store.nodetable.NodeTable;
import org.apache.jena.tdb.store.nodetupletable.NodeTupleTable;

import cl.uc.dcc.leapfrog.BGPIter;

public class OptionalTreeNode implements LFIterBindingNodeId {

	private OptionalTreeNode[] children;
	private BGPIter myPattern;
	private NodeTable nodeTable;

	private BindingNodeId myBinding;
	private ExprList myFilters;
	private BindingNodeId extendedBinding;

	private Var[] globalAttributeOrder;

	private boolean atEnd = false;
	private boolean nextFound = false;
	private int stage = STAGE_FIND;

	private final static int STAGE_FIND = 0;
	private final static int STAGE_EXTEND = 1;

	private final static int MAX_CACHE = 1000;

	private int childrenExtended;
	private int[] cacheSize;
	private int[] cacheCurrentPos;
	private BindingNodeId[][] cacheBindings;


	private OptionalTreeNode(NodeTupleTable ntt, BasicPattern pattern) {
		nodeTable = ntt.getNodeTable();
		myPattern = new BGPIter(pattern, ntt);
		extendedBinding = new BindingNodeId();
		myFilters = new ExprList();
	}
	
	private OptionalTreeNode(NodeTupleTable ntt, BasicPattern pattern, ExprList exprList) {
		nodeTable = ntt.getNodeTable();
		myPattern = new BGPIter(pattern, ntt);
		extendedBinding = new BindingNodeId();
		myFilters = exprList;
	}

	public static OptionalTreeNode getNode(NodeTupleTable ntt, Op op, ReorderTransformation reorderTransformation) {
		if (op instanceof OpBGP) {
			OpBGP opBGP = (OpBGP) op;
			return new OptionalTreeNode(ntt, reorderTransformation.reorder(opBGP.getPattern()));

		} else if (op instanceof OpQuadPattern) {
			OpQuadPattern opQuad = (OpQuadPattern) op;
			if (!opQuad.isDefaultGraph()) {
				throw new IllegalStateException("No graph allowed");	
			}
			return new OptionalTreeNode(ntt, reorderTransformation.reorder(opQuad.getBasicPattern()));

        } else if (op instanceof OpConditional) {
        	OpConditional opConditional = (OpConditional) op;
			OptionalTreeNode leftNode = OptionalTreeNode.getNode(ntt, opConditional.getLeft(), reorderTransformation);
			OptionalTreeNode rightNode = OptionalTreeNode.getNode(ntt, opConditional.getRight(), reorderTransformation);
			leftNode.addChild(rightNode);
			return leftNode;

		} else if (op instanceof OpFilter) {
			OpFilter opFilter = (OpFilter) op;
			OptionalTreeNode res = OptionalTreeNode.getNode(ntt, opFilter.getSubOp(), reorderTransformation);
			res.addFilter(opFilter.getExprs());
			return res;
			
		}  else {
          throw new IllegalStateException(op.getName() + " not supported");
        }

	}
	
	private void addFilter(ExprList exprs) {
		myFilters.addAll(exprs);
	}

	public void addChild(OptionalTreeNode newChild) {
		if (children == null) {
			children = new OptionalTreeNode[1];
			children[0] = newChild;
		} else {
			OptionalTreeNode[] newChildren = new OptionalTreeNode[children.length + 1];
			for (int i = 0; i < children.length; i++) {
				newChildren[i] = children[i];
			}
			newChildren[children.length] = newChild;
			this.children = newChildren;
		}
	}

	@Override
	public Var[] init(Var[] upperVars) {
		return init(upperVars, true);
	}
	
	public Var[] init(Var[] upperVars, boolean root) {
		if (children == null) {
			children = new OptionalTreeNode[0];
		}

		cacheSize = new int[children.length];
		cacheCurrentPos = new int[children.length];
		cacheBindings = new BindingNodeId[children.length][];

		globalAttributeOrder = myPattern.init(upperVars);
		if (!myPattern.openTerms()) {
			atEnd = true;
		}
		if (root) {
			myPattern.open();
		}
		
		for (int i = 0; i < children.length; i++) {
			cacheBindings[i] = new BindingNodeId[MAX_CACHE];
			globalAttributeOrder = children[i].init(globalAttributeOrder, false);
		}
		return globalAttributeOrder;
	}

	@Override
	public boolean hasNext() {
		if (atEnd) {
			return false;
		} else if (nextFound) {
			return true;
		}

		if (stage == STAGE_FIND) {
			if (myPattern.hasNext()) {
				BindingNodeId myOldBinding = myBinding;
				long[] myPatternIds = myPattern.next();
				myBinding = new BindingNodeId();
				
				for (int i = 0; i < myPatternIds.length; i++) {
					myBinding.put(myPattern.getLocalAttribute(i), NodeId.create(myPatternIds[i]));
				}
				
				extendedBinding = new BindingNodeId(myBinding);
				
				if (myFilters.size() > 0) {
					Binding binding = new BindingTDB(extendedBinding, nodeTable);
					
					for (Expr filter : myFilters) {
						if(!filter.isSatisfied(binding, null)) {
							return hasNext();
						}
					}
				}

				if (children.length > 0) {
					int firstChangedVarPos = myPattern.getFirstChangedVar(myOldBinding);

					childrenExtended = 0;
					for (OptionalTreeNode child : children) {
						if (child.seekBinding(myBinding, firstChangedVarPos) && child.hasNext()) {
							stage = STAGE_EXTEND; // it takes at least 1 child to be extended to change the stage to STAGE_EXTEND

					        BindingNodeId firstBinding = child.next();
					        Iterator<Var> bindingVars = firstBinding.iterator();
					        while (bindingVars.hasNext()) {
					        	Var v = bindingVars.next();
					        	if (!myBinding.containsKey(v)) {
					        		extendedBinding.put(v, firstBinding.get(v));
					        	}
					        }

							cacheBindings[childrenExtended][0] = firstBinding;
							cacheCurrentPos[childrenExtended] = 0;

					        int size = 1;
					        while (child.hasNext()) {
					        	cacheBindings[childrenExtended][size++] = child.next();
					        }
					        cacheSize[childrenExtended] = size;
					        childrenExtended++;
					    }
					}
				}
				nextFound = true;
				return true;
			} else {
				atEnd = true;
				return false;
			}
		} else { // stage == STAGE_EXTEND
			for (int i = 0; i < childrenExtended; i++) {
				cacheCurrentPos[i]++;
				if (cacheSize[i] > cacheCurrentPos[i]) {
					for (int j = 0; j < childrenExtended; j++) {
						Iterator<Var> bindingVars = cacheBindings[j][cacheCurrentPos[j]].iterator();
				        while (bindingVars.hasNext()) {
				        	Var v = bindingVars.next();
				        	if (!myBinding.containsKey(v)) {
				        		extendedBinding.put(v, cacheBindings[j][cacheCurrentPos[j]].get(v));
				        	}
				        }
					}
					nextFound = true;
					return true;
				}
				else {
					cacheCurrentPos[i] = 0;
				}
			}
			stage = STAGE_FIND;
			return hasNext();
		}
	}

	@Override
	public BindingNodeId next() {
		nextFound = false;
		return extendedBinding;
	}

	@Override
	public boolean seekBinding(BindingNodeId previousBinding, int firstChangedVarPos) {
		atEnd = false;
		return myPattern.seekBinding(previousBinding, firstChangedVarPos);
	}

}