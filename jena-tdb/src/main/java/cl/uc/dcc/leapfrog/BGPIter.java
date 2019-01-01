package cl.uc.dcc.leapfrog;

import java.util.ArrayList;
import java.util.List;

import org.apache.jena.graph.Node;
import org.apache.jena.graph.Triple;
import org.apache.jena.sparql.core.BasicPattern;
import org.apache.jena.sparql.core.Var;
import org.apache.jena.tdb.index.bplustree.BPlusTree;
import org.apache.jena.tdb.solver.BindingNodeId;
import org.apache.jena.tdb.store.nodetable.NodeTable;
import org.apache.jena.tdb.store.nodetupletable.NodeTupleTable;
import org.apache.jena.tdb.store.tupletable.TupleIndexRecord;

import cl.uc.dcc.leapfrog.LFTrieIndex;

public class BGPIter {
	
	private NodeTupleTable ntt;								// Required to get the B+Tree indexes and the nodeTable
	private Triple[] triples;								// Array of all triples in the Pattern.
	
	private LFTrieIndex[] iter;								// Corresponding iterator for each triple.
	private LFTrieIndex[] iterOrderedForEnumeration;		// Copy of iter, might be in a different order.
	private LFTrieIndex[][] itersForVar;					// Each itersForVar[i] contains all iterators containing the variable localAttributeOrder[i].
															// These iterators are supposed to be ordered at opening the corresponding level
															// and the order is always maintained (the position of the minimum changes p=(p+1)%n after each seek).
	
	private long[] binding;									// Temp bindings are saved here.
	private int idxMin[]; 									// idxMin[i] points to the iterator having the minimum key in the array itersForVar[i].
	
	private int level = -1;									// Current variable index in the local attribute order, if level = i, we know that variables 0...(i-1) already have a binding.
	private int baseLevel = 0;								// how many variables in local will be setted from outside
	
	private boolean beforeFirst;							// To avoid calling iter.next() immediately after a open(). 
	
	private Var[] globalAttributeOrder;						// Attribute order for the complete query
	private Var[] localAttributeOrder;						// Attribute order for variables from the internal BGP 
	
	private int[] localToGlobal;							// index of a variable in the global order given its local index
	private int[] globalToLocal;							// index of a variable in the local order given its global index
	
	private boolean beforeFirstEnumeration;
	private int enumarationLevel;
		
	
	public BGPIter(BasicPattern pattern, NodeTupleTable ntt) {
		this.ntt = ntt;
		List<Triple> temp = pattern.getList();
		triples = temp.toArray(new Triple[temp.size()]);
	}
	
	/** Searches for terms in the BGP and open their corresponding iterators. 
	 *  @return true if terms were found, false if it weren't
	 *  */
	public boolean openTerms() {
		NodeTable nodeTable = ntt.getNodeTable();
		for (int i = 0; i < triples.length; i++) {
			Node nodes[] = { triples[i].getSubject(), triples[i].getMatchPredicate(), triples[i].getObject() };
			LFTrieIndex iter = this.iter[i];
			
			for (int j = 0; j < 3; j++) {
				if ( ! nodes[j].isVariable() ) {
					long id = nodeTable.getNodeIdForNode(nodes[j]).getId();
					
					iter.open();
					// Have to check this first because exists the possibility that after open
					// it ended up finding the key. Calling iter.seek would move forwards
					if (iter.key() != id) {
						
						iter.seek(id);
						
						if (iter.atEnd() || iter.key() != id) {
							// no match is found, we know is impossible to have any binding
							return false;
						}
					}
				}
			}
		}
		
		//open();
		return true;
	}
	
	/** calls up() in all the corresponding iterators */
	private void up() {		
		LFTrieIndex it[] = itersForVar[level];
		for (int i = 0; i < it.length; i++) {
			it[i].up();
		}
		level--;
	}
	
	/** opens all the corresponding iterators for the current level and orders them by key */
	public void open() {
		level++;
		
		if (level < enumarationLevel) {
			beforeFirst = true;
			LFTrieIndex it[] = itersForVar[level];
			for (int i = 0; i < it.length; i++) {
				it[i].open();
			}
			
			// sort the corresponding iterators using insertion sort
			for (int i = 1; i < it.length; i++) {
				LFTrieIndex aux = it[i];
				int j;
				for (j = i-1; j >= 0 && it[j].key() > aux.key(); j--) {
					it[j+1] = it[j];
				}
				it[j+1] = aux;
			}
			idxMin[level] = 0;
		} else {
			beforeFirstEnumeration = true;
			for (int i = 0; i < iter.length; i++) {
				iter[i].startNoIntersection(binding);
			}

			for (int i = 0; i < iter.length; i++) {
				iterOrderedForEnumeration[i] = iter[i];
			}
			
			// sort the corresponding iterators using insertion sort
			for (int i = 1; i < iterOrderedForEnumeration.length; i++) {
				LFTrieIndex aux = iterOrderedForEnumeration[i];
				int j;
				for (j = i-1; j >= 0 && iterOrderedForEnumeration[j].bufferSize() > aux.bufferSize(); j--) {
					iterOrderedForEnumeration[j+1] = iterOrderedForEnumeration[j];
				}
				iterOrderedForEnumeration[j+1] = aux;
			}
		}		
	}
	
	
	public boolean hasNext() {
		while (level != enumarationLevel) {
			// We try to bind the variable for the current level
			if ( findIntersection() ) {
				open();
			} else {
				if (level == baseLevel) {
					return false;
				} else {
					up();
				}
			}
		}
		
		if (beforeFirstEnumeration) {
			beforeFirstEnumeration = false;
			return true;
		}
		
		for (int i = 0; i < iterOrderedForEnumeration.length; i++) {
			if (iterOrderedForEnumeration[i].hasNextInBuffer()) {
				iterOrderedForEnumeration[i].nextInBuffer(binding);
				
				while (--i >= 0) {
					iterOrderedForEnumeration[i].resetBuffer(binding);
				}
				return true;
			}
		}
		
		for (int i = 0; i < iterOrderedForEnumeration.length; i++) {
			if (iterOrderedForEnumeration[i].hasNextBuffer()) {
				iterOrderedForEnumeration[i].nextBuffer(binding);
				
				while (--i >= 0) {
					iterOrderedForEnumeration[i].resetAll(binding);
				}
				return true;
			}
		}
		
		level--;
		if (level < baseLevel) {
			return false;
		} else {
			return hasNext();
		}
	}
	
	/** 
	 * tries to find a match in corresponding iterators for the current level
	 * @return true if it matches successfully or false if couldn't 
	 */	
	private boolean findIntersection() {
		
		LFTrieIndex currentIter[] = itersForVar[level];
		int p = idxMin[level]; // to make code simpler, don't forget to reassign idxMin[level] = p before returning true.
		
		// Call next unless this is the first call to leapfrogSearch after open() was called
		if (beforeFirst) {
			beforeFirst = false;
		} else {
			currentIter[p].next();
			if ( currentIter[p].atEnd() ) {
				return false;
			} else {
				p = (p + 1) % currentIter.length;
			}
		}
		
		// normal modulus of negative number gives a negative result, so we use Math.floorMod to avoid this
		long max = currentIter[Math.floorMod(p - 1, currentIter.length)].key();
		
		while (true) {
			long min = currentIter[p].key();
			if (min == max) { // min = max means all are equal
				binding[level] = min;
				return true;
			} else {
				currentIter[p].seek(max);
				if ( currentIter[p].atEnd() ) {
					return false;
				} else {
					max = currentIter[p].key();
					p = (p + 1) % currentIter.length;
				}
			}
		}
	}
	
	
	public Var[] init(Var[] upperVars) {
		setAttributesOrder(upperVars);
		
		// Create local-global mapping
		localToGlobal = new int[localAttributeOrder.length];
		globalToLocal = new int[globalAttributeOrder.length];
		
		int globalIndex = 0;
		for (int localIndex = 0; localIndex < localAttributeOrder.length; localIndex++) {
			while (!localAttributeOrder[localIndex].equals(globalAttributeOrder[globalIndex])) {
				globalToLocal[globalIndex] = localIndex;
				globalIndex++;
			}
			globalToLocal[globalIndex] = localIndex;
			localToGlobal[localIndex] = globalIndex;
			globalIndex++;
		}
		
		// Create one iterator per each triple
		iter = new LFTrieIndex[triples.length];
		iterOrderedForEnumeration = new LFTrieIndex[triples.length];
		
		for (int i = 0; i < triples.length; i++) {
			int permutation = getIndex(triples[i]);
			TupleIndexRecord index = (TupleIndexRecord) ntt.getTupleTable().getIndex(permutation);
			BPlusTree btree = (BPlusTree) index.getRangeIndex();
			iter[i] = new LFTrieIndex(btree, triples[i], localAttributeOrder, permutation, getNoIntersectionLevel(triples[i], permutation, upperVars));
		}
		
		// dont't need to initialize each idxMin element at 0, java does it automatically.
		idxMin = new int[localAttributeOrder.length];
		
		// for each variable in the gao, we create an array containing the corresponding iterators.
		itersForVar = new LFTrieIndex[localAttributeOrder.length][];
		
		binding = new long[localAttributeOrder.length];
		
		for (int i = 0; i < localAttributeOrder.length; i++) {
			for (int lvl = 0; lvl < localAttributeOrder.length; lvl++) {
				// we add to triplesForLevel all the iterators for the current lvl
				List<LFTrieIndex> triplesForLevel = new ArrayList<>();
				
				for (int j = 0; j < triples.length; j++) {
					if ( tripleContainsVariable(triples[j], localAttributeOrder[lvl]) ) {
						triplesForLevel.add(iter[j]);
					}
				}
				// triplesForLevel list is converted to an array.
				itersForVar[lvl] = new LFTrieIndex[triplesForLevel.size()];
				for (int k = 0; k < triplesForLevel.size(); k++) {
					// Order does not matter yet. They will be ordered after a open() is called at their level.
					itersForVar[lvl][k] = triplesForLevel.get(k);
				}	
			}
		}
		enumarationLevel = localAttributeOrder.length;
		while (enumarationLevel > 0 && !repitedVar(localAttributeOrder[enumarationLevel-1], upperVars)) {
			enumarationLevel--;	
		}
		
		return globalAttributeOrder;		
	}
	
	
	private void setAttributesOrder(Var[] upperVars) {
		List<Var> previous = new ArrayList<>();
		List<Var> after = new ArrayList<>();
		
		List<Var> tempGao = new ArrayList<>();

		for (Var upperVar : upperVars) {
			tempGao.add(upperVar);
		}
		
		for (Triple triple : triples) {
			Node nodes[] = { triple.getSubject(), triple.getMatchPredicate(), triple.getObject() };
			
			for (int i = 0; i < nodes.length; i++) {
				if ( Var.isVar(nodes[i]) ) {
					Var v = (Var) nodes[i];
					boolean contains = false;
					for (Var upperVar : upperVars) {
						if (upperVar.equals(nodes[i])) {
							contains = true;
							break;
						}
					}
					if (contains) {
						if (!previous.contains(v))
							previous.add(v);
					} else {
						if (!after.contains(v))
							after.add(v);
					}
				}
			}
		}
		List<Var> afterOrdered = getVarOrder(after);
		List<Var> localAttributeOrderList = new ArrayList<>();
		
		for (Var upperVar : upperVars) {
			if (previous.contains(upperVar)) {
				localAttributeOrderList.add(upperVar);
				baseLevel++;
			}
		}
		
		localAttributeOrderList.addAll(afterOrdered);
		localAttributeOrder = localAttributeOrderList.toArray(new Var[localAttributeOrderList.size()]);
		
		// now previous have all variables
		tempGao.addAll(afterOrdered);
		globalAttributeOrder = tempGao.toArray(new Var[tempGao.size()]);
	}
	
	
	public List<Var> getVarOrder(List<Var> after) {
		List<Var> res = new ArrayList<>();
		if (triples.length <= 1) {
			return after;
		}
		
		for (int i = 1; i < triples.length; i++) {
			int[] varAppereances = new int[after.size()];
			
			for (int j = 0; j <= i; j++) {
				Triple triple = triples[j];
				for (int k = 0; k < after.size(); k++) {
					if (triple.getSubject().equals(after.get(k))) {
						varAppereances[k]++;
					}
					if (triple.getPredicate().equals(after.get(k))) {
						varAppereances[k]++;
					}
					if (triple.getObject().equals(after.get(k))) {
						varAppereances[k]++;
					}
				}
			}
			
			for (int j = 0; j < varAppereances.length; j++) {
				Var v = after.get(j);
				if (varAppereances[j] > 1 && !res.contains(v)) {
					res.add(v);
				}
			}
		}
		// agrego las variables que no esten
		for (Var v : after) {
			if (!res.contains(v)) {
				res.add(v);
			}
		}
		return res;
	}
	
	/** 
	 * @param triple the triple you want to know its permutation.
	 * @return the corresponding position in the indexes array, need to be consistent with 
	 * the order declared at Names.java 
	 */
	private int getIndex(Triple triple) {
		// Default values satisfy s < p < o, because openTerms() will check in that order.
		int s=-3, p=-2, o=-1;

		// If the node is a variable, we assign their position in the gao.
		for (int i = 0; i < localAttributeOrder.length; i++) {
			if ( localAttributeOrder[i].equals(triple.getSubject()) ) {
				s = i;
			} else if ( localAttributeOrder[i].equals(triple.getPredicate()) ) {
				p = i;
			} else if ( localAttributeOrder[i].equals(triple.getObject()) ) {
				o = i;
			}
		}
		if (s <= p && s <= o) { // S??
			if (p <= o) {
				return 0; // SPO
			} else {
				return 3; // SOP
			}
				
		} else if (p <= s && p <= o) { // P??
			if (s <= o) {
				return 4; // PSO
			} else {
				return 1; // POS
			}		
		} else { // O??
			if (s <= p) {
				return 2; // OSP
			} else {
				return 5; // OPS
			}
		}
	}
	
	
	private int getNoIntersectionLevel(Triple triple, int permutation, Var[] upperVars) {
		if (permutation == 0) { // SPO
			if (repitedVar(triple.getObject(), upperVars))
				return 3;
			else if (repitedVar(triple.getPredicate(), upperVars))
				return 2;
			else if (repitedVar(triple.getSubject(), upperVars))
				return 1;
		}
		else if (permutation == 1) { // POS
			if (repitedVar(triple.getSubject(), upperVars))
				return 3;
			else if (repitedVar(triple.getObject(), upperVars))
				return 2;
			else if (repitedVar(triple.getPredicate(), upperVars))
				return 1;
		}
		else if (permutation == 2) { // OSP
			if (repitedVar(triple.getPredicate(), upperVars))
				return 3;
			else if (repitedVar(triple.getSubject(), upperVars))
				return 2;
			else if (repitedVar(triple.getObject(), upperVars))
				return 1;
		}
		else if (permutation == 3) { // SOP
			if (repitedVar(triple.getPredicate(), upperVars))
				return 3;
			else if (repitedVar(triple.getObject(), upperVars))
				return 2;
			else if (repitedVar(triple.getSubject(), upperVars))
				return 1;
		}
		else if (permutation == 4) { // PSO
			if (repitedVar(triple.getObject(), upperVars))
				return 3;
			else if (repitedVar(triple.getSubject(), upperVars))
				return 2;
			else if (repitedVar(triple.getPredicate(), upperVars))
				return 1;
		}
		else { // permutation == 5 // OPS
			if (repitedVar(triple.getSubject(), upperVars))
				return 3;
			else if (repitedVar(triple.getPredicate(), upperVars))
				return 2;
			else if (repitedVar(triple.getObject(), upperVars))
				return 1;
		}
		return 0;
	}
	
	
	private boolean repitedVar(Node node, Var[] upperVars) {
		if (!node.isVariable()) {
			return true;
		} else {
			for (Var var : upperVars) {
				if (var.equals(node)) {
					return true;
				}
			}
			int appearances = 0;
			for (Triple triple : triples) {
				if (triple.getSubject().equals(node)) {
					appearances++;
				}
				else if (triple.getPredicate().equals(node)) {
					appearances++;
				}
				else if (triple.getObject().equals(node)) {
					appearances++;
				}
			}
			return appearances > 1;
		}
	}
	
	/**
	 * @param triple the triple you want to check if the variable is in.
	 * @param var the variable you are searching into the triple.
	 * @return true if the variable is contained in the triple, false otherwise. 
	 * */
	private static boolean tripleContainsVariable(Triple triple, Var var) {
		return triple.subjectMatches(var) || triple.predicateMatches(var) || triple.objectMatches(var); 
	}	
	
	
	public Var getLocalAttribute(int i) {
		return localAttributeOrder[i];
	}
	

	public long[] next() {
		return binding;
	}

	
	public boolean tryOpenAndSeek(long nodeId) {
		boolean res = true;
		level++;
		LFTrieIndex it[] = itersForVar[level];
		// tengo que abrir todos los iteradores para que sea consistente
		for (int i = 0; i < it.length; i++) {
			it[i].open();
			if (it[i].key() != nodeId) { // podría quedar justo abierto en la key que necesito, si hago seek me paso
				it[i].seek(nodeId);
			}
			if (it[i].key() != nodeId) {
				res = false;
			}
		}
		if (res) {
			binding[level] = nodeId;
		}
		return res;
	}
	
	
	public boolean seekBinding(BindingNodeId base, int firstChangedVarPos) {
		beforeFirst = true;
		int levelToReset = globalToLocal[firstChangedVarPos];
		
		// se supone que quede en baseLevel
		// por cada variable de mi gao que este en reset tengo que hacer up
		while (level >= levelToReset) {
			up(); // esto puede dejar en level = -1
		}
		
		while (level+1 < localAttributeOrder.length) {
			Var v = localAttributeOrder[level+1]; // veo si me toca abrir el ultimo nivel		
			if (base.containsKey(v)) {
				if ( !tryOpenAndSeek(base.get(v).getId()) ) { // si no llego a la variable dejo en el nivel anterior y devuelvo falso
					up();
					return false;
				}
			} else {
				break;
			}
		}
		open();
		return true;
	}
	

	public int getFirstChangedVar(BindingNodeId previousBinding) {		
		if (previousBinding != null) {
			for (int i = 0; i < localAttributeOrder.length; i++) {
				if ( previousBinding.get(localAttributeOrder[i]).getId() != binding[i]) {
					return localToGlobal[i];
				}
			}
		}
		return localToGlobal[0];
	}
	
}