package tw.exact;

import java.io.File;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class MTDecomposer {

//  static final boolean VERBOSE = true;
   private static final boolean VERBOSE = false;
//   private static boolean DEBUG = true;
  static boolean DEBUG = false;

  Graph g;
  
  Bag currentBag;
    
  LayeredSieve tBlockSieve;

  Queue<MBlock> readyQueue;

  ArrayList<PMC> pendingEndorsers;

//  Set<XBitSet> processed;

  Map<XBitSet, TBlock> tBlockCache;

  Map<XBitSet, Block> blockCache;
  
  Map<XBitSet, MBlock> mBlockCache;
  
  Set<XBitSet> pmcCache;
  
  int upperBound;
  int lowerBound;
  
  int targetWidth;

  PMC solution;
  
  SafeSeparator ss;

  static int TIMEOUT_CHECK = 100;

  public MTDecomposer(Bag bag, 
      int lowerBound, int upperBound) {

    currentBag = bag;
    g = bag.graph;
    if (!g.isConnected(g.all)) {
      System.err.println("graph must be connected, size = " + bag.size);
    }
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;
    
    ss = new SafeSeparator(g);
  }
  
  public void decompose() {
    blockCache = new HashMap<>();
    mBlockCache = new HashMap<>();

    pendingEndorsers = new ArrayList<>();
    pmcCache = new HashSet<>();

    decompose(lowerBound);
  }
  
  public void decompose(int targetWidth) {
    if (VERBOSE) {
      System.out.println("deompose enter, n = " + currentBag.size + 
          ", targetWidth = " + targetWidth);
    }
    if (targetWidth > upperBound) {
      return;
    }
    this.targetWidth = targetWidth;
    
    if (currentBag.size <= targetWidth + 1) {
      currentBag.nestedBags = null;
      currentBag.separators = null;
      return;
    }
    
    // endorserMap = new HashMap<>();

    tBlockSieve = new LayeredSieve(g.n, targetWidth);
    tBlockCache = new HashMap<>();

    readyQueue = new LinkedList<>();

    readyQueue.addAll(mBlockCache.values());
    
    for (int v = 0; v < g.n; v++) {
      XBitSet cnb = (XBitSet) g.neighborSet[v].clone();
      cnb.set(v);

      if (DEBUG) {
        System.out.println(v + ":" + cnb.cardinality() + ", " + cnb);
      }

      if (cnb.cardinality() > targetWidth + 1) {
        continue;
      }
      
//      if (!pmcCache.contains(cnb)) {
        PMC pmc = new PMC(cnb, getBlocks(cnb));
        if (pmc.isValid) {
//          pmcCache.add(cnb);
          if (pmc.isReady()) {
            pmc.endorse();
          }
          else {
          pendingEndorsers.add(pmc);
          }
//        }
      }
    }

    while (true) {
      while (!readyQueue.isEmpty()) {

        MBlock ready = readyQueue.remove();

        ready.process();

        if (solution != null) {
          log("solution found");
          Bag bag = currentBag.addNestedBag(solution.vertexSet); 
          solution.carryOutDecomposition(bag);
          return;
        }
      }

      if (!pendingEndorsers.isEmpty()) {
        log("queue empty");
      }

      ArrayList<PMC> endorsers = pendingEndorsers;
      pendingEndorsers = new ArrayList<PMC>();
      for (PMC endorser : endorsers) {
        endorser.process();
        if (solution != null) {
          log("solution found");
          Bag bag = currentBag.addNestedBag(solution.vertexSet); 
          solution.carryOutDecomposition(bag);
          return;
        }
      }
      if (readyQueue.isEmpty()) {
        break;
      }
    }
    
    log("failed");
    
    decompose(targetWidth + 1);
    return;
  }

  boolean crossesOrSubsumes(XBitSet separator1, XBitSet endorsed, XBitSet separator2) {
    ArrayList<XBitSet> components = g.getComponents(separator1);
    for (XBitSet compo: components) {
      if (endorsed.isSubset(compo)) {
        // subsumes
        return true;
      }
    }
    // test crossing
    XBitSet diff = separator2.subtract(separator1);
    for (XBitSet compo: components) {
      if (diff.isSubset(compo)) {
        return false;
      }
    }
    return true;
  }
  
  Block getBlock(XBitSet component) {
    Block block = blockCache.get(component);
    if (block == null) {
      block = new Block(component);
      blockCache.put(component, block);
    }
    return block;
  }

  void makeMBlock(XBitSet component, PMC endorser) {
    MBlock mBlock = mBlockCache.get(component);
    if (mBlock == null) {
      Block block = getBlock(component);
      mBlock = new MBlock(block, endorser);
      blockCache.put(component, block);
    }
  }

  MBlock getMBlock(XBitSet component) {
    return mBlockCache.get(component);
  }

  boolean isFullComponent(XBitSet component, XBitSet sep) {
    for (int v = sep.nextSetBit(0); v >= 0; v = sep.nextSetBit(v + 1)) {
      if (component.isDisjoint(g.neighborSet[v])) {
        return false;
      }
    }
    return true;
  }

  ArrayList<Block> getBlocks(XBitSet separator) {
    ArrayList<Block> result = new ArrayList<Block>();
    XBitSet rest = g.all.subtract(separator);
    for (int v = rest.nextSetBit(0); v >= 0; v = rest.nextSetBit(v + 1)) {
      XBitSet c = g.neighborSet[v].subtract(separator);
      XBitSet toBeScanned = (XBitSet) c.clone();
      c.set(v);
      while (!toBeScanned.isEmpty()) {
        XBitSet save = (XBitSet) c.clone();
        for (int w = toBeScanned.nextSetBit(0); w >= 0; w = toBeScanned
            .nextSetBit(w + 1)) {
          c.or(g.neighborSet[w]);
        }
        c.andNot(separator);
        toBeScanned = c.subtract(save);
      }

      Block block = getBlock(c);
      result.add(block);
      rest.andNot(c);
    }
    return result;
  }

  class Block implements Comparable<Block> {
    XBitSet component;
    XBitSet separator;
    XBitSet outbound;

    Block(XBitSet component) {
      this.component = component;
      this.separator = g.neighborSet(component);
      
      XBitSet rest = g.all.subtract(component);
      rest.andNot(separator);
      
      int minCompo = component.nextSetBit(0);

      // the scanning order ensures that the first full component
      // encountered is the outbound one
      for (int v = rest.nextSetBit(0); v >= 0; v = rest.nextSetBit(v + 1)) {
        XBitSet c = (XBitSet) g.neighborSet[v].clone();
        XBitSet toBeScanned = c.subtract(separator);
        c.set(v);
        while (!toBeScanned.isEmpty()) {
          XBitSet save = (XBitSet) c.clone();
          for (int w = toBeScanned.nextSetBit(0); w >= 0; 
              w = toBeScanned.nextSetBit(w + 1)) {
            c.or(g.neighborSet[w]);
          }
          toBeScanned = c.subtract(save).subtract(separator);
        }
        if (separator.isSubset(c)) {
          // full block other than "component" found
          if (v < minCompo) {
            outbound = c.subtract(separator);
          }
          else {
            // v > minCompo
            outbound = component;
          }
          return;
        }
        rest.andNot(c);
      }
    }

    boolean isOutbound() {
      return outbound == component;
    }
    
    boolean ofMinimalSeparator() {
      return outbound != null;
    }
    
    public String toString() {
      StringBuilder sb = new StringBuilder();
      if (outbound == component) {
        sb.append("o");
      } 
      else {
        if (mBlockCache.get(component) != null) {
          sb.append("f");
        } else {
          sb.append("i");
        }
      }
      sb.append(component + "(" + separator + ")");
      return sb.toString();
    }

    @Override
    public int compareTo(Block b) {
      return component.nextSetBit(0) - b.component.nextSetBit(0);
    }
  }

  class MBlock {
    Block block;
    PMC endorser;

    MBlock(Block block, PMC endorser) {
      this.block = block;
      this.endorser = endorser;

      if (DEBUG) {
        System.out.println("MBlock constructor" + this);
      }

    }

    void process() {
      if (DEBUG) {
        System.out.print("processing " + this);
      }

      makeSimpleTBlock();

      ArrayList<XBitSet> tBlockSeparators = new ArrayList<>();
      tBlockSieve.collectSuperblocks(
          block.component, block.separator, tBlockSeparators);

      for (XBitSet tsep : tBlockSeparators) {
        TBlock tBlock = tBlockCache.get(tsep);
        tBlock.plugin(this);
      }
    }

    void makeSimpleTBlock() {

      if (DEBUG) {
        System.out.print("makeSimple: " + this);
      }

      TBlock tBlock = tBlockCache.get(block.separator);
      if (tBlock == null) {
        tBlock = new TBlock(block.separator, block.outbound);
        tBlockCache.put(block.separator, tBlock);
        tBlockSieve.put(block.outbound, block.separator);
        tBlock.crown();
      }
    }

    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("MBlock:" + block.separator + "\n");
      sb.append("  in  :" + block.component + "\n");
      sb.append("  out :" + block.outbound + "\n");
      return sb.toString();
    }
  }

  class TBlock {
    XBitSet separator;
    XBitSet openComponent;

    TBlock(XBitSet separator, XBitSet openComponent) {
      this.separator = separator;
      this.openComponent = openComponent;
    }

    void plugin(MBlock mBlock) {
      if (DEBUG) {
        System.out.println("plugin " + mBlock);
        System.out.println("  to " + this);
      }

      XBitSet newsep = separator.unionWith(mBlock.block.separator);

      if (newsep.cardinality() > targetWidth + 1) {
        return;
      }

      ArrayList<Block> blockList = getBlocks(newsep);

      Block fullBlock = null;
      int nSep = newsep.cardinality();

      for (Block block : blockList) {
        if (block.separator.cardinality() == nSep) {
          if (fullBlock != null) {
//             minimal separator: treated elsewhere
            return;
          }
          fullBlock = block;
        }
      }

      if (fullBlock == null) {
//        if (!pmcCache.contains(newsep)) {  
          PMC pmc = new PMC(newsep, blockList);
          if (pmc.isValid) {
//            pmcCache.add(newsep);
            if (pmc.isReady()) {
              pmc.endorse();
            } 
            else {
              pendingEndorsers.add(pmc);
            }
//          }
        }
      }

      else {
        if (newsep.cardinality() > targetWidth) {
          return;
        }
        TBlock tBlock = tBlockCache.get(newsep);
        if (tBlock == null) {
          tBlock = new TBlock(newsep, fullBlock.component);
          tBlockCache.put(newsep, tBlock);
          tBlockSieve.put(fullBlock.component, newsep);
          tBlock.crown();
        }
      }
    }

    void crown() {
      for (int v = separator.nextSetBit(0); v >= 0; 
          v = separator.nextSetBit(v + 1)) {
        if (DEBUG) {
          System.out.println("try crowing by " + v);
        }

        XBitSet newsep = separator.unionWith(
          g.neighborSet[v].intersectWith(openComponent));
        if (newsep.cardinality() <= targetWidth + 1) {

          if (DEBUG) {
            System.out.println("crowing by " + v + ":" + this);
          }
//          if (!pmcCache.contains(newsep)) {  
            PMC pmc = new PMC(newsep);
            if (pmc.isValid) {
//              pmcCache.add(newsep);
              if (pmc.isReady()) {
                pmc.endorse();
              } 
              else {
                pendingEndorsers.add(pmc);
              }
//            }
          }
        }
      }
    }

    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("TBlock:\n");
      sb.append("  sep :" + separator + "\n");
      sb.append("  open:" + openComponent + "\n");
      return sb.toString();
    }
  }

  class PMC {
    XBitSet vertexSet;
    Block inbounds[];
    Block outbound;
    boolean isValid;

    PMC(XBitSet vertexSet) {
      this(vertexSet, getBlocks(vertexSet));
    }
    
    PMC(XBitSet vertexSet, ArrayList<Block> blockList) {
      this.vertexSet = vertexSet;
      if (vertexSet.isEmpty()) {
        return;
      }
      for (Block block: blockList) {
        if (block.isOutbound() &&
            (outbound == null || 
            outbound.separator.isSubset(block.separator))){
          outbound = block;
        }
      }
      if (outbound == null) {
        inbounds = blockList.toArray(
            new Block[blockList.size()]);  
      }
      else {
        inbounds = new Block[blockList.size()];
        int k = 0;
        for (Block block: blockList) {
          if (!block.separator.isSubset(outbound.separator)) {
            inbounds[k++] = block;
          }
        }
        if (k < inbounds.length) {
          inbounds = Arrays.copyOf(inbounds, k);
        }
      }
      checkValidity();
      
      if (DEBUG 
//          ||
//          vertexSet.equals(
//              new XBitSet(new int[]{0, 1, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 38, 39, 40, 41, 42, 43, 44, 45, 55, 56, 57, 58, 59, 60, 61, 66, 69}))
          ) {
        System.out.println("PMC created:");
        System.out.println(this);
      }
    }

    void checkValidity() {
      for (Block b: inbounds) {
        if (!b.ofMinimalSeparator()) {
          isValid = false;
          return;
        }
      }
      
      for (int v = vertexSet.nextSetBit(0); v >= 0; 
            v = vertexSet.nextSetBit(v + 1)) {
        XBitSet rest = vertexSet.subtract(g.neighborSet[v]);
        rest.clear(v);
        if (outbound != null && outbound.separator.get(v)) {
          rest.andNot(outbound.separator);
        }
        for (Block b : inbounds) {
          if (b.separator.get(v)) {
            rest.andNot(b.separator);
          }
        }
        if (!rest.isEmpty()) {
          isValid = false;
          return;
        }
      }
      isValid = true;
    }
    
    boolean isReady() {
      for (int i = 0; i < inbounds.length; i++) {
        if (mBlockCache.get(inbounds[i].component) == null) {
          return false;
        }
      }
      return true;
    }

    XBitSet getTarget() {
      if (outbound == null) {
        return null;
      }
      XBitSet combined = vertexSet.subtract(outbound.separator);
      for (Block b: inbounds) {
        combined.or(b.component);
      }
      return combined;
    }


    void process() {
      if (DEBUG) {
        System.out.print("processing " + this);
      }
      if (isReady()) {
        if (DEBUG) {
          System.out.print("endorsing " + this);
        }
        endorse();
      } 
      else {
        pendingEndorsers.add(this);
      }
    }

    void endorse() {

      if (DEBUG) {
        System.out.print("endorsing " + this);
      }

      if (DEBUG) {
        System.out.println("ontbound= " + outbound);
      }

      if (outbound == null) {
        if (DEBUG) {
          System.out.println("solution found in endorse()");
        }
        solution = this;
        return;
      } 
      else {
        endorse(getTarget());
      }
    }

    void endorse(XBitSet target) {
      if (DEBUG) {
        System.out.println("endorsed = " + target);
      }

      // if (separator.equals(bs1)) {
      // System.err.println("endorsed = " + endorsed +
      // ", " + endorserMap.get(endorsed));
      // }
      //

      if (mBlockCache.get(target) == null) {
        Block block = getBlock(target);
        MBlock mBlock = new MBlock(block, this);
        mBlockCache.put(target, mBlock);

        if (DEBUG) {
          System.out.println("adding to ready queue" + mBlock);
        }
        readyQueue.add(mBlock);
      }
    }

    void carryOutDecomposition(Bag bag) {
      if (DEBUG) {
        System.out.print("carryOutDecomposition:" + this);
      }
      
      for (Block inbound: inbounds) {
        if (DEBUG) {
          System.out.println("inbound  = " + inbound);
        }
        MBlock mBlock = mBlockCache.get(inbound.component);
        if (mBlock == null) {
          System.out.println("inbound mBlock is null, block = " + inbound);
          continue;
        }

        Bag subBag = currentBag.addNestedBag(
            mBlock.endorser.vertexSet);
        Separator separator = 
            currentBag.addSeparator(inbound.separator);
        
        separator.incidentBags.add(bag);
        separator.incidentBags.add(subBag);
        
        bag.incidentSeparators.add(separator);
        subBag.incidentSeparators.add(separator);
        mBlock.endorser.carryOutDecomposition(subBag);
      }
    }

    private XBitSet inletsInduced() {
      XBitSet result = new XBitSet(g.n);
      for (Block b : inbounds) {
        result.or(b.separator);
      }
      return result;
    }

    public String toString() {

      StringBuilder sb = new StringBuilder();
      sb.append("PMC");
      if (isValid) {
        sb.append("(valid):\n");
      }
      else {
        sb.append("(invalid):\n");
      }
      sb.append("  sep     : " + vertexSet + "\n");
      sb.append("  outbound: " + outbound + "\n");

      for (Block b : inbounds) {
        sb.append("  inbound : " + b + "\n");
      }
      return sb.toString();
    }
  }

  int numberOfEnabledBlocks() {
    return mBlockCache.size();
  }

  void dumpPendings() {
    System.out.println("pending endorsers\n");
    for (PMC endorser : pendingEndorsers) {
      System.out.print(endorser);
    }
  }

  void log(String logHeader) {
    if (VERBOSE) {

      int sizes[] = tBlockSieve.getSizes();

      System.out.println(logHeader);
      System.out.print("n = " + g.n + " width = " + targetWidth + ", tBlocks = "
          + tBlockCache.size() + Arrays.toString(sizes));
      System.out.print(", endorsed = " + mBlockCache.size());
      System.out.print(", pendings = " + pendingEndorsers.size());
      System.out.println(", blocks = " + blockCache.size());
    }
  }
}
