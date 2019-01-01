package cl.uc.dcc.leapfrog;

import org.apache.jena.tdb.base.record.Record;
import org.apache.jena.tdb.base.record.RecordFactory;
import org.apache.jena.tdb.store.NodeId;

public class LFTrieIndex {
	
 	private static final int MAX_LEVEL = 2;
 	private static final RecordFactory factory;
 	public static final Record zeroRecord;
	static {
 		factory = new RecordFactory(32*MAX_LEVEL, 0);
 		zeroRecord = factory.create(new byte[3 * NodeId.SIZE]);
 	}
}
