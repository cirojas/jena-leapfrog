package cl.uc.dcc.leapfrog;

import static org.apache.jena.tdb.sys.SystemTDB.SizeOfLong;

import java.util.Stack;

import org.apache.jena.atlas.lib.Bytes;
import org.apache.jena.graph.Node;
import org.apache.jena.graph.Triple;
import org.apache.jena.sparql.core.Var;
import org.apache.jena.tdb.base.record.Record;
import org.apache.jena.tdb.base.record.RecordFactory;
import org.apache.jena.tdb.base.recordbuffer.RecordBufferPageMgr;
import org.apache.jena.tdb.base.recordbuffer.RecordRangeIterator;
import org.apache.jena.tdb.index.bplustree.BPTreeNode;
import org.apache.jena.tdb.index.bplustree.BPTreeRecords;
import org.apache.jena.tdb.index.bplustree.BPlusTree;
import org.apache.jena.tdb.store.NodeId;


public class LFTrieIndex {
	
	private static final int MAX_LEVEL = 2;
	private static final RecordFactory factory;
	public static final Record zeroRecord;
	static {
		factory = new RecordFactory(32*MAX_LEVEL, 0);
		zeroRecord = factory.create(new byte[3 * NodeId.SIZE]);
	}
	
	private int level;
	private boolean atEnd;
	
	private long[] currentTuple;
	private Stack<BPTreeNode> nodes;
	private BPTreeRecords currentRecordsNode;
	
	private int[] varIndexInLocalOrder;
	
	private Var[] noIntersectionVars;
	private int noIntersectionLevel;
	
	private RecordBufferPageMgr pageMgr;
	private RecordRangeIterator recordIter;
	private Record noIntersectionMin;
	private Record noIntersectionMax;
	
	private static final int BUFFER_SIZE = 1_000;
	private int maxBufferPos;
	private int currentBufferPos;
	private long buffer[][];
	
	
	public LFTrieIndex(BPlusTree btree, Triple triple, Var[] localAttributeOrder, int permutation, int noIntersectionLevel) {
		this.noIntersectionLevel = noIntersectionLevel;
		buffer = new long[BUFFER_SIZE][];
		
		pageMgr = btree.getRecordsMgr().getRecordBufferPageMgr();
				
		noIntersectionVars = new Var[3-noIntersectionLevel];
		
		if (permutation == 0) { //SPO
			setNoIntersectionVars(triple.getSubject(), triple.getPredicate(), triple.getObject());
		}
		else if (permutation == 1) { //POS
			setNoIntersectionVars(triple.getPredicate(), triple.getObject(), triple.getSubject());
		}
		else if (permutation == 2) { //OSP
			setNoIntersectionVars(triple.getObject(), triple.getSubject(), triple.getPredicate());
		}
		else if (permutation == 3) { //SOP
			setNoIntersectionVars(triple.getSubject(), triple.getObject(), triple.getPredicate());
		}
		else if (permutation == 4) { //PSO
			setNoIntersectionVars(triple.getPredicate(), triple.getSubject(), triple.getObject());
		}
		else { // permutation == 5 //OPS
			setNoIntersectionVars(triple.getObject(), triple.getPredicate(), triple.getSubject());
		}
		
		varIndexInLocalOrder = new int[3];
		
		for (int i = noIntersectionLevel; i < 3; i++) {
			for (int j = 0; j < localAttributeOrder.length; j++ ) {
				if (localAttributeOrder[j].equals(noIntersectionVars[i-noIntersectionLevel])) {
					varIndexInLocalOrder[i] = j;
					break;
				}
			}
		}
		
    	level = -1;
    	nodes = new Stack<>();
    	nodes.add(btree.getRoot());
	}

	private void setNoIntersectionVars(Node node1, Node node2, Node node3) {
		int i = 0;
		if (noIntersectionLevel <= 0) {
			noIntersectionVars[0] = (Var) node1; 
			i++;
		}
		if (noIntersectionLevel <= 1) {
			noIntersectionVars[i] = (Var) node2; 
			i++;
		}
		if (noIntersectionLevel <= 2) {
			noIntersectionVars[i] = (Var) node3; 
		}
	}
	
	public void up() {
		atEnd = false;
		level--;
	}
	
	public void open() {		
		level++;

		// iterator starts again
		if (level == 0) {
			BPTreeNode n = nodes.pop();
			
			// n must be the root node
			while (!nodes.empty()) {
				n.release();
				n = nodes.pop();
			}
			
			if (currentRecordsNode != null) {
				currentRecordsNode.release();
			}
			currentRecordsNode = n.search(nodes, zeroRecord);
			currentTuple = recordToTuple(currentRecordsNode.minRecord());
		} else {
			byte[] min = new byte[3 * NodeId.SIZE];
			switch (level) {
			case 0:
				// 0, 0, 0
				//Bytes.setLong(0L, min, 0);
				//Bytes.setLong(0L, min, SizeOfLong);
				//Bytes.setLong(0L, min, 2*SizeOfLong);
				break;
			case 1:
				// current, 0, 0
				Bytes.setLong(currentTuple[0], min, 0);
				//Bytes.setLong(0L, min, SizeOfLong);
				//Bytes.setLong(0L, min, 2*SizeOfLong);
				break;
			case 2:
				// current, current, 0
				Bytes.setLong(currentTuple[0], min, 0);
				Bytes.setLong(currentTuple[1], min, SizeOfLong);
				//Bytes.setLong(0L, min, 2*SizeOfLong);
				break;
			}
			Record recordMin = factory.create(min);
			
			Record r = currentRecordsNode.search(recordMin);
			// if low <= r <= high
			if (r != null && (Record.keyLE(r, recordMin) && Record.keyLE(recordMin, r))) {
				currentTuple = recordToTuple(r);
				return;
			}
			BPTreeNode n = nodes.pop();
			
			while ( (Record.keyLT(recordMin, n.getLowOrZeroRecord()) || Record.keyLT(n.getHighOrZeroRecord(), recordMin)) && !nodes.empty()) {
				n.release();
				n = nodes.pop();
			}
			
			BPTreeRecords recordsNodeFound = n.search(nodes, recordMin);
			r = recordsNodeFound.search(recordMin);
			
			currentRecordsNode.release();
			currentRecordsNode = recordsNodeFound;
			currentTuple = recordToTuple(r);
		}	
	}
	
	
	public long key() {
		return currentTuple[level];
	}


	public void next() {
		byte[] min = new byte[3 * NodeId.SIZE];
		byte[] max = new byte[3 * NodeId.SIZE];
		
		switch (level) {
		case 0:
			// min = current+1, 0, 0
			Bytes.setLong(currentTuple[0]+1, min, 0);
			//Bytes.setLong(0L, min, SizeOfLong);
			//Bytes.setLong(0L, min, 2*SizeOfLong);
			
			// max = null
			break;
		case 1:
			// min = current, current+1, 0				
			Bytes.setLong(currentTuple[0], min, 0);
			Bytes.setLong(currentTuple[1]+1, min, SizeOfLong);
			//Bytes.setLong(0L, min, 2*SizeOfLong);
			
			// max = current+1, 0, 0
			Bytes.setLong(currentTuple[0]+1, max, 0);
			//Bytes.setLong(0L, max, SizeOfLong);
			//Bytes.setLong(0L, max, 2*SizeOfLong);
			
			break;
		case 2:
			// min = current, current, current+1
			Bytes.setLong(currentTuple[0], min, 0);
			Bytes.setLong(currentTuple[1], min, SizeOfLong);
			Bytes.setLong(currentTuple[2]+1, min, 2*SizeOfLong);
			
			// max = current, current+1, 0
			Bytes.setLong(currentTuple[0], max, 0);
			Bytes.setLong(currentTuple[1]+1, max, SizeOfLong);
			//Bytes.setLong(0L, max, 2*SizeOfLong);
			
			break;
		}
		Record recordMin = factory.create(min);
		Record recordMax = (level==0)? null : factory.create(max);
		
		internalSearch(recordMin, recordMax);
	}
	
	
	/** search a record in the interval [min, max) */
	public void internalSearch(Record min, Record max) {
		Record r = currentRecordsNode.search(min);
		
		if (r == null) {
			BPTreeNode n = nodes.pop();
			while ( !nodes.empty() && (Record.keyLT(n.getHighOrZeroRecord(), min) || Record.keyLT(min, n.getLowOrZeroRecord())) ) {
				n.release();
				n = nodes.pop();
			}
			
			BPTreeRecords recordsNodeFound = n.search(nodes, min);
			r = recordsNodeFound.search(min);
			
			if (r == null || (max != null && Record.keyGE(r, max)) ) {
				recordsNodeFound.release();
				atEnd = true;
				return;
			} else {
				currentRecordsNode.release();
				currentRecordsNode = recordsNodeFound;
				currentTuple = recordToTuple(r);
			}
		} else if (max != null && Record.keyGE(r, max)) {
			atEnd = true;
		} else {
			currentTuple = recordToTuple(r);
		}
	}


	public void seek(long key) {
		// If the current position is already greater or equal it moves to the next position anyways.
		if (key <= currentTuple[level]) {
			next();
			return;
		}
		
		byte[] min = new byte[3 * NodeId.SIZE];
		byte[] max = new byte[3 * NodeId.SIZE];
		
		switch (level) {
		case 0:
			// min = key, 0, 0
			Bytes.setLong(key, min, 0);
			//Bytes.setLong(0L, min, SizeOfLong);
			//Bytes.setLong(0L, min, 2*SizeOfLong);
			
			// max = null
			break;
		case 1:
			// min = current, key, 0				
			Bytes.setLong(currentTuple[0], min, 0);
			Bytes.setLong(key, min, SizeOfLong);
			//Bytes.setLong(0L, min, 2*SizeOfLong);
			
			// max = current+1, 0, 0
			Bytes.setLong(currentTuple[0]+1, max, 0);
			//Bytes.setLong(0L, max, SizeOfLong);
			//Bytes.setLong(0L, max, 2*SizeOfLong);
			
			break;
		case 2:
			// min = current, current, key
			Bytes.setLong(currentTuple[0], min, 0);
			Bytes.setLong(currentTuple[1], min, SizeOfLong);
			Bytes.setLong(key, min, 2*SizeOfLong);
			
			// max = current, current+1, 0
			Bytes.setLong(currentTuple[0], max, 0);
			Bytes.setLong(currentTuple[1]+1, max, SizeOfLong);
			//Bytes.setLong(0L, max, 2*SizeOfLong);
			
			break;
		}
		Record recordMin = factory.create(min);
		Record recordMax = (level==0)? null : factory.create(max);
		internalSearch(recordMin, recordMax);
	}
	

	public boolean atEnd() {
		return atEnd;
	}


	public void startNoIntersection(long[] binding) {
		byte[] min = new byte[3 * NodeId.SIZE];
		byte[] max = new byte[3 * NodeId.SIZE];
		
		switch (level) {
		case -1:
			noIntersectionMin = factory.create(min);
			
			break;
		case 0:	
			Bytes.setLong(currentTuple[0], min, 0);
			
			Bytes.setLong(currentTuple[0]+1, max, 0);
			
			break;
		case 1:
			Bytes.setLong(currentTuple[0], min, 0);
			Bytes.setLong(currentTuple[1], min, SizeOfLong);
			
			Bytes.setLong(currentTuple[0], max, 0);
			Bytes.setLong(currentTuple[1]+1, max, SizeOfLong);
			
			break;
		case 2:
			Bytes.setLong(currentTuple[0], min, 0);
			Bytes.setLong(currentTuple[1], min, SizeOfLong);
			Bytes.setLong(currentTuple[2], min, 2*SizeOfLong);
			
			Bytes.setLong(currentTuple[0], max, 0);
			Bytes.setLong(currentTuple[1], max, SizeOfLong);
			Bytes.setLong(currentTuple[2]+1, max, 2*SizeOfLong);
		}
			
		noIntersectionMin = factory.create(min);
		noIntersectionMax = (level==-1)? null : factory.create(max);

		if (recordIter != null) {
			recordIter.close();
		}
		int idx = BPTreeNode.convert(nodes.peek().findSlot(noIntersectionMin)) ;
        int id = nodes.peek().getPtrBuffer().get(idx) ;
		recordIter = (RecordRangeIterator) RecordRangeIterator.iterator(id, noIntersectionMin, noIntersectionMax, pageMgr);		
		fillBuffer();

		currentTuple = buffer[0];
		for (int i = noIntersectionLevel; i < 3; i++) {
			binding[varIndexInLocalOrder[i]] = currentTuple[i];
		}
	}
	

	public void resetBuffer(long[] binding) {
		currentBufferPos = 0;
		currentTuple = buffer[0];
		
		for (int i = noIntersectionLevel; i < 3; i++) {
			binding[varIndexInLocalOrder[i]] = currentTuple[i];
		}
	}
	

	public void resetAll(long[] binding) {
		recordIter.close();
		int idx = BPTreeNode.convert(nodes.peek().findSlot(noIntersectionMin)) ;
        int id = nodes.peek().getPtrBuffer().get(idx) ;
		recordIter = (RecordRangeIterator) RecordRangeIterator.iterator(id, noIntersectionMin, noIntersectionMax, pageMgr);		
		fillBuffer();
		
		currentTuple = buffer[0];
		
		for (int i = noIntersectionLevel; i < 3; i++) {
			binding[varIndexInLocalOrder[i]] = currentTuple[i];
		}
	}
	

	public boolean hasNextBuffer() {
		return recordIter.hasNext();
	}
	

	public boolean hasNextInBuffer() {
		return currentBufferPos < maxBufferPos - 1; 
	}


	public void nextInBuffer(long[] binding) {
		currentTuple = buffer[++currentBufferPos];
		for (int i = noIntersectionLevel; i < 3; i++) {
			binding[varIndexInLocalOrder[i]] = currentTuple[i];
		}
	}

	
	public void nextBuffer(long[] binding) {
		fillBuffer();
		currentTuple = buffer[0];
		for (int i = noIntersectionLevel; i < 3; i++) {
			binding[varIndexInLocalOrder[i]] = currentTuple[i];
		}
	}
	
	
	private void fillBuffer() {
		maxBufferPos = 0;
		while (maxBufferPos < BUFFER_SIZE && recordIter.hasNext()) {
			buffer[maxBufferPos++] = recordToTuple(recordIter.next());
		}
		currentBufferPos = 0;
	}
	
	
	private static long[] recordToTuple(Record r) {
        int n = r.getKey().length/SizeOfLong;
        long[] nodeIds = new long[n] ;
        for (int i = 0 ; i < n ; i++) {
            nodeIds[i] = Bytes.getLong(r.getKey(), i*SizeOfLong);
        }
        return nodeIds;
    }


	public int bufferSize() {
		return maxBufferPos;
	}
	
}