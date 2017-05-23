/*
 * Copyright (c) 2017, Hisao Tamaki and Hiromu Otsuka
*/

package tw.heuristic;

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

public class MTDecomposerHeuristic {

  //static final boolean VERBOSE = true;
   private static final boolean VERBOSE = false;
//   private static boolean DEBUG = true;
  static boolean DEBUG = false;

  private static final long STEPS_PER_MS = 25;
  
  Graph g;
  
  int maxMultiplicity;
  
  Bag currentBag;
    
  LayeredSieve tBlockSieve;

  Queue<MBlock> readyQueue;

  ArrayList<PMC> pendingEndorsers;

//  Set<VertexSet> processed;

  Map<VertexSet, TBlock> tBlockCache;

  Map<VertexSet, Block> blockCache;
  
  Map<VertexSet, MBlock> mBlockCache;
  
  Set<VertexSet> pmcCache;
  
  int upperBound;
  int lowerBound;
  
  int targetWidth;

  PMC solution;

  boolean abort;

  //SafeSeparator ss;

  static int TIMEOUT_CHECK = 100;
  
  boolean counting;
  long numberOfPlugins;

  long timeLimit;

  //int count;
  long count;
  long sumCount;
  CPUTimer timer;
  File logFile;
  
  int tbCount;
  int siCount;

  public MTDecomposerHeuristic(Bag bag, 
      int lowerBound, int upperBound,
      File logFile, CPUTimer timer, long timeMS) {
    this.timeLimit = STEPS_PER_MS * timeMS;
    this.logFile = logFile;
    this.timer = timer;
    this.timeLimit = timeLimit;

    currentBag = bag;
    g = bag.graph;
    if (!g.isConnected(g.all)) {
      System.err.println("graph must be connected, size = " + bag.size);
    }
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;
    
    //ss = new SafeSeparator(g);
    
  }

  private MTDecomposerHeuristic(Bag bag, 
      int lowerBound, int upperBound,
      File logFile, CPUTimer timer,
      long count, long timeLimit) {
    this.logFile = logFile;
    this.timer = timer;
    this.timeLimit = timeLimit;
    this.count = count;

    currentBag = bag;
    g = bag.graph;
    if (!g.isConnected(g.all)) {
      System.err.println("graph must be connected, size = " + bag.size);
    }
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;
    
    //ss = new SafeSeparator(g);
  }
  
  public void setMaxMultiplicity(int m) {
    maxMultiplicity = m;
  }

  public boolean isAborted(){
    return abort;
  }

  public long getTimeMS(){
    return (count + sumCount) / STEPS_PER_MS;
  }
  
  public boolean decompose() {
    abort = false;
    blockCache = new HashMap<>();
    mBlockCache = new HashMap<>();

    pendingEndorsers = new ArrayList<>();
    pmcCache = new HashSet<>();

    //return decompose(lowerBound);
    boolean result = decompose(lowerBound);
    //System.out.println("c count = " + count);
    return result;
  }
  
  public boolean decompose(int targetWidth) {
    if (counting) {
      numberOfPlugins = 0;
    }
    if (VERBOSE) {
      System.out.println("deompose enter, n = " + currentBag.size + 
          ", targetWidth = " + targetWidth);
    }
    if (targetWidth > upperBound) {
      return false;
    }
    this.targetWidth = targetWidth;
    
    //count = 0;
    tbCount = 0;
    siCount = 0;
    
    if (currentBag.size <= targetWidth + 1) {
      currentBag.nestedBags = null;
      currentBag.separators = null;
      return true;
    }
    
    // endorserMap = new HashMap<>();

    tBlockSieve = new LayeredSieve(g.n, targetWidth);
    tBlockCache = new HashMap<>();

    readyQueue = new LinkedList<>();

    readyQueue.addAll(mBlockCache.values());
    
    for (int v = 0; v < g.n; v++) {
      VertexSet cnb = (VertexSet) g.neighborSet[v].clone();
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
        //count++;
        /*
        if (count > TIMEOUT_CHECK) {
          count = 0;
          if (timer != null && timer.hasTimedOut()) {
            log("**TIMEOUT**");
            return false;
          }
        }
        */

        if(count > timeLimit){
          abort = true;
          return false;
        }

        MBlock ready = readyQueue.remove();

        ready.process();

        if (solution != null && !counting) {
          log("solution found");
          Bag bag = currentBag.addNestedBag(solution.vertexSet); 
          solution.carryOutDecomposition(bag);
          return true;
        }
      }

      if (!pendingEndorsers.isEmpty()) {
        log("queue empty");
      }

      ArrayList<PMC> endorsers = pendingEndorsers;
      pendingEndorsers = new ArrayList<PMC>();
      for (PMC endorser : endorsers) {
        endorser.process();
        if (solution != null && !counting) {
          log("solution found");
          Bag bag = currentBag.addNestedBag(solution.vertexSet); 
          solution.carryOutDecomposition(bag);
          return true;
        }
      }
      if (readyQueue.isEmpty()) {
        break;
      }
    }
    
    if (counting && solution != null) {
      log("solution found");
      System.out.println("IBlocks: " + mBlockCache.size() +   
          ", TBlocks: " + tBlockCache.size() +
          ", PMCs: " + pmcCache.size() + 
          ", numuberOfPlugins = " + numberOfPlugins);
      Bag bag = currentBag.addNestedBag(solution.vertexSet); 
      solution.carryOutDecomposition(bag);
      return true;
    }
    
    log("failed");
    
//    ArrayList<VertexSet> targets = new ArrayList<>();
//    targets.add(currentBag.vertexSet);
//    
//    ArrayList<VertexSet> endorseds = 
//        new ArrayList<>();
//    endorseds.addAll(mBlockCache.keySet());
//    
//    SafeSeparator ss = new SafeSeparator(g);
    Set<VertexSet> safeSeparators = new HashSet<>();
    
//    Collections.sort(endorseds, 
//        (s, t)-> t.cardinality() - s.cardinality());
//    
//    for (VertexSet endorsed: endorseds) {
//      VertexSet targetToSplit = null;
//      for (VertexSet compo: targets) {
//        if (endorsed.isSubset(compo)) {
//          targetToSplit = compo;
//          break;
//        }
//      }
//      if (targetToSplit == null) {
//        continue;
//      }
//      VertexSet separatorSet = g.neighborSet(endorsed);
//      if (safeSeparators.contains(separatorSet)) {
//        continue;
//      }
//      boolean available = true;
//      
//      for (VertexSet safe: safeSeparators) {
//        if (crossesOrSubsumes(safe, endorsed, separatorSet)) {
//          available = false;
//          System.out.println(separatorSet + " is crossed or subsumed by " + safe);
//          break;
//        }
//      }
//      
//      if (!available) {
//        continue;
//      }
//      
//      if (ss.isOneWaySafe(separatorSet, endorsed)) {
//        if (separatorSet.isEmpty()) {
//          System.err.println("empty safe separator, endorsed = " + endorsed);
//        }
//        if (VERBOSE) {
//          System.out.println("safe separator found: " + separatorSet + 
//              ", splitting off " + endorsed);
//        }
//
//        safeSeparators.add(separatorSet);
//      }
//    }

    if (safeSeparators.isEmpty()) {
//      System.out.println("no safe separators, advancing to " + (targetWidth + 1));
    return decompose(targetWidth + 1);
    }
    if (VERBOSE) {
      log(currentBag.size + " vertices split by "
          + safeSeparators.size() + " safe separators");
    }
    ArrayList<Bag> bagsToDecompose = new ArrayList<>();
    bagsToDecompose.add(currentBag.addNestedBag(g.all));

    for (VertexSet separatorSet: safeSeparators) {

      // find the bag containing the separator
      Bag bagToSplit = null;
      for (Bag bag: bagsToDecompose) {
        if (separatorSet.isSubset(bag.vertexSet)) {
          bagToSplit = bag;
          break;
        }
      }

      if (bagToSplit == null) {
//        System.out.println("cannot find bag to split for "  + separatorSet);
        continue;
      }

      Separator separator = currentBag.addSeparator(separatorSet);

//      System.out.println("incorporating safe separator: " + separatorSet);
//      System.out.println("splitting bag: " + bagToSplit.vertexSet);
      bagsToDecompose.remove(bagToSplit);
      currentBag.nestedBags.remove(bagToSplit);
      ArrayList<Bag> bagsToAdd = new ArrayList<>();

      ArrayList<VertexSet> components = g.getComponents(separatorSet);
      for (VertexSet compo: components) {
        Bag bag = null;
        MBlock mBlock = getMBlock(compo);
        if (mBlock != null) {
          if (mBlock.endorser.outbound.separator.equals(separatorSet)) {
            bag = currentBag.addNestedBag(mBlock.endorser.vertexSet);
//            System.out.println("carrying out decomposition on " + bag.vertexSet);
            mBlock.endorser.carryOutDecomposition(bag);
          }
        }
        if (bag != null) {
          separator.incidentBags.add(bag);
          bag.incidentSeparators.add(separator);
          continue;
        }
        VertexSet ns = g.neighborSet(compo).intersectWith(separatorSet);
        if (ns.equals(separatorSet)) {
          VertexSet intersection = 
              g.closedNeighborSet(compo).intersectWith(bagToSplit.vertexSet);
          if (!intersection.isEmpty()) {
            Bag bagToAdd = currentBag.addNestedBag(intersection);
//            System.out.println("added " + bagToAdd.vertexSet);
            bagsToDecompose.add(bagToAdd);
            bagsToAdd.add(bagToAdd);
            separator.incidentBags.add(bagToAdd);
            bagToAdd.incidentSeparators.add(separator);
          }
        }              
      }
      Bag bag0 = separator.incidentBags.get(0);
      for (VertexSet compo: components) {
        VertexSet ns = g.neighborSet(compo).intersectWith(separatorSet);
        if (!ns.equals(separatorSet)) {
          VertexSet intersection = 
              g.closedNeighborSet(compo).intersectWith(bagToSplit.vertexSet);
          if (!intersection.isEmpty()) {
            Bag bagToAdd = currentBag.addNestedBag(intersection);
            bagsToDecompose.add(bagToAdd);
            bagsToAdd.add(bagToAdd);
//            System.out.println("added " + bagToAdd.vertexSet);
            Separator separator1 = currentBag.addSeparator(ns);
            separator1.incidentBags.add(bagToAdd);
            separator1.incidentBags.add(bag0);
            bagToAdd.incidentSeparators.add(separator1);
            bag0.incidentSeparators.add(separator1);
          }
        }
      }

      // distribute the separators incident to the bag to split
      // to split bags
      for (Separator sep: bagToSplit.incidentSeparators) {
        sep.incidentBags.remove(bagToSplit);
        for (Bag bagToAdd: bagsToAdd) {
          if (sep.vertexSet.isSubset(bagToAdd.vertexSet)) {
            sep.incidentBags.add(bagToAdd);
            bagToAdd.incidentSeparators.add(sep);
            break;
          }
        }
      }
    }
    for (Bag bag: bagsToDecompose) {
//      System.out.println("incident separators of " + bag.vertexSet);
//      for (Separator s: bag.incidentSeparators) {
//        System.out.println("  " + s.vertexSet);
//        for (Bag b: s.incidentBags) {
//          System.out.println("        " + b.vertexSet);
//        }
//      }
      bag.makeRefinable();
//      bag.graph.writeTo(System.out);
      MTDecomposerHeuristic mtd = new MTDecomposerHeuristic(bag, targetWidth + 1, upperBound,
          logFile, timer, count, timeLimit);
      if(!mtd.decompose()){
        sumCount += (mtd.sumCount + mtd.count);
        abort |= mtd.isAborted();
        return false;
      }
      sumCount += (mtd.sumCount + mtd.count);
    }
    return true;
  }

  boolean crossesOrSubsumes(VertexSet separator1, VertexSet endorsed, VertexSet separator2) {
    ArrayList<VertexSet> components = g.getComponents(separator1);
    for (VertexSet compo: components) {
      if (endorsed.isSubset(compo)) {
        // subsumes
        return true;
      }
    }
    // test crossing
    VertexSet diff = separator2.subtract(separator1);
    for (VertexSet compo: components) {
      if (diff.isSubset(compo)) {
        return false;
      }
    }
    return true;
  }
  
  Block getBlock(VertexSet component) {
    Block block = blockCache.get(component);
    if (block == null) {
      block = new Block(component);
      blockCache.put(component, block);
    }
    return block;
  }

  void makeMBlock(VertexSet component, PMC endorser) {
    MBlock mBlock = mBlockCache.get(component);
    if (mBlock == null) {
      Block block = getBlock(component);
      mBlock = new MBlock(block, endorser);
      blockCache.put(component, block);
    }
  }

  MBlock getMBlock(VertexSet component) {
    return mBlockCache.get(component);
  }

  void checkAgainstDecompositionInFile(String path, String name) {
    TreeDecomposition referenceTd = TreeDecomposition.readDecomposition(path,
        name, g);
    checkAgainstDecomposition(referenceTd);
  }

  void checkAgainstDecomposition(TreeDecomposition referenceTd) {
    // referenceTd.minimalize();
    referenceTd.canonicalize();
    // System.out.println("reference decomposition minimalized");
    System.out.println("reference decomposition canonicalized");
    referenceTd.validate();

    System.out.println("is canonical: " + referenceTd.isCanonical());

    for (int i = 1; i <= referenceTd.nb; i++) {
      PMC endorser = new PMC(referenceTd.bagSets[i]);

      VertexSet target = null;
      if (endorser.outbound != null) {
        target = endorser.getTarget();
      }

      if (endorser.isReady() && target != null
          && getMBlock(target) == null) {
        System.out.println("endorser ready:\n" + endorser);
        System.out.println("but target not endorsed: " + target + "("
            + g.neighborSet(target) + ")\n");

        VertexSet inletsUnion = endorser.inletsInduced();

        VertexSet delta1 = endorser.vertexSet.subtract(inletsUnion);
        VertexSet delta2 = endorser.vertexSet
            .subtract(endorser.outbound.separator);
        System.out.println("delta1 = " + delta1);
        for (int v = delta1.nextSetBit(0); v >= 0; v = delta1
            .nextSetBit(v + 1)) {
          System.out.println("  " + v + "(" + g.neighborSet[v] + ")");
        }
        System.out.println("delta2 = " + delta2);
        for (int v = delta2.nextSetBit(0); v >= 0; v = delta2
            .nextSetBit(v + 1)) {
          System.out.println("  " + v + "(" + g.neighborSet[v] + ")");
        }

        TBlock tBlock = tBlockCache.get(inletsUnion);
        System.out.println(" underlying tBlock = " + tBlock);
      } else if (target == null) {
        System.out.println("endorser without target, isReady = "
            + (endorser.isReady()) + " :\n" + endorser);
      } else if (!endorser.isReady()) {
        System.out.println("endorser not ready:\n" + endorser);
        System.out.println("target = " + target);
      }
    }
  }

  boolean isFullComponent(VertexSet component, VertexSet sep) {
    for (int v = sep.nextSetBit(0); v >= 0; v = sep.nextSetBit(v + 1)) {
      if (component.isDisjoint(g.neighborSet[v])) {
        return false;
      }
    }
    return true;
  }

  ArrayList<Block> getBlocks(VertexSet separator) {
    ArrayList<Block> result = new ArrayList<Block>();
    VertexSet rest = g.all.subtract(separator);
    for (int v = rest.nextSetBit(0); v >= 0; v = rest.nextSetBit(v + 1)) {
      VertexSet c = g.neighborSet[v].subtract(separator);
      VertexSet toBeScanned = (VertexSet) c.clone();
      c.set(v);
      while (!toBeScanned.isEmpty()) {
        VertexSet save = (VertexSet) c.clone();
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
    VertexSet component;
    VertexSet separator;
    VertexSet outbound;

    Block(VertexSet component) {
      this.component = component;
      this.separator = g.neighborSet(component);
      
      VertexSet rest = g.all.subtract(component);
      rest.andNot(separator);
      
      int minCompo = component.nextSetBit(0);

      // the scanning order ensures that the first full component
      // encountered is the outbound one
      for (int v = rest.nextSetBit(0); v >= 0; v = rest.nextSetBit(v + 1)) {
        VertexSet c = (VertexSet) g.neighborSet[v].clone();
        VertexSet toBeScanned = c.subtract(separator);
        c.set(v);
        while (!toBeScanned.isEmpty()) {
          VertexSet save = (VertexSet) c.clone();
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

      ArrayList<VertexSet> tBlockSeparators = new ArrayList<>();
      tBlockSieve.collectSuperblocks(
          block.component, block.separator, tBlockSeparators);

      for (VertexSet tsep : tBlockSeparators) {
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
        tBlock = new TBlock(block.separator, block.outbound, 1);
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
    VertexSet separator;
    VertexSet openComponent;
    int multiplicity;

    TBlock(VertexSet separator, VertexSet openComponent) {
      this.separator = separator;
      this.openComponent = openComponent;
    }
    TBlock(VertexSet separator, VertexSet openComponent, int multiplicity) {
      this(separator, openComponent);
      this.multiplicity = multiplicity;
//      tbCount++;
//      if (supportInduced()) {
//        siCount++;
//      }
//      if (tbCount %10000 == 0) {
//        System.out.println("support-induced / total-tblocks "  + 
//            siCount + "/" + tbCount); 
//      }
    }

    void plugin(MBlock mBlock) {
      if (counting) {
        numberOfPlugins++;
      }

      ++count;

      if (DEBUG) {
        System.out.println("plugin " + mBlock);
        System.out.println("  to " + this);
      }

      VertexSet newsep = separator.unionWith(mBlock.block.separator);

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
          tBlock = new TBlock(newsep, fullBlock.component,
              multiplicity + 1);
          tBlockCache.put(newsep, tBlock);
          if (maxMultiplicity == 0 ||
              multiplicity < maxMultiplicity) {
            tBlockSieve.put(fullBlock.component, newsep);
          }
          tBlock.crown();
        }
      }
    }

    boolean supportInduced() {
      ArrayList<Block> blocks = getBlocks(separator);
      VertexSet outlet = new VertexSet(g.n);
      for (Block block: blocks) {
        if (block.isOutbound() &&
            !block.separator.equals(separator)) {
          if (outlet.isSubset(block.separator)) {
            outlet = block.separator;
          }
          else if (!block.separator.isSubset(outlet)) {
            return false;
          }
        }
      }
      VertexSet union = new VertexSet(g.n);
      for (Block block: blocks) {
        if (!block.isOutbound() &&
            !block.separator.isSubset(outlet)) {
          union.or(block.separator);
        }
      }
      return union.equals(separator);
    }
    
    void crown() {
      for (int v = separator.nextSetBit(0); v >= 0; 
          v = separator.nextSetBit(v + 1)) {
        if (DEBUG) {
          System.out.println("try crowing by " + v);
        }

        VertexSet newsep = separator.unionWith(
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
    VertexSet vertexSet;
    Block inbounds[];
    Block outbound;
    boolean isValid;

    PMC(VertexSet vertexSet) {
      this(vertexSet, getBlocks(vertexSet));
    }
    
    PMC(VertexSet vertexSet, ArrayList<Block> blockList) {
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
//              new VertexSet(new int[]{0, 1, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 38, 39, 40, 41, 42, 43, 44, 45, 55, 56, 57, 58, 59, 60, 61, 66, 69}))
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
        VertexSet rest = vertexSet.subtract(g.neighborSet[v]);
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

    VertexSet getTarget() {
      if (outbound == null) {
        return null;
      }
      VertexSet combined = vertexSet.subtract(outbound.separator);
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

      pmcCache.add(vertexSet);
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

    void endorse(VertexSet target) {
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

    private VertexSet inletsInduced() {
      VertexSet result = new VertexSet(g.n);
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
      log(logHeader, System.out);
    }
    if (logFile != null) {
      PrintStream ps;
      try {
        ps = new PrintStream(new FileOutputStream(logFile, true));

        log(logHeader, ps);
        ps.close();
      } catch (FileNotFoundException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
  }

  void log(String logHeader, PrintStream ps) {
    ps.print(logHeader);
    if (timer != null) {
      long time = timer.getTime();
      ps.print(", time = " + time);
    }
    ps.println();

    int sizes[] = tBlockSieve.getSizes();

    ps.print("n = " + g.n + " width = " + targetWidth + ", tBlocks = "
        + tBlockCache.size() + Arrays.toString(sizes));
    ps.print(", endorsed = " + mBlockCache.size());
    ps.print(", pendings = " + pendingEndorsers.size());
//    ps.print(", processed = " + processed.size());
    ps.println(", blocks = " + blockCache.size());
  }

  private static void count() {
    /*
   String path = "random";
   
   String[] instances = {
//       "gnm_20_40_1,6", 
       "gnm_20_60_1,8", 
       "gnm_20_80_1,11", 
       "gnm_20_100_1,11", 
//       "gnm_30_60_1,7", 
       "gnm_30_90_1,11", 
       "gnm_30_120_1,14", 
       "gnm_30_150_1,16", 
       "gnm_40_80_1,8", 
       "gnm_40_120_1,14", 
       "gnm_40_160_1,18", 
       "gnm_40_200_1,20", 
//       "gnm_50_100_1,10", 
       "gnm_50_150_1,16", 
       "gnm_50_200_1,20", 
       "gnm_50_250_1,24", 
   };
   
   for (String instance: instances) {
     String[] s = instance.split(",");
     String name = s[0];
     int width = Integer.parseInt(s[1]);
     
     Graph g = Graph.readGraph("instance/" + path, name);

     System.out.println("Graph " + name + " read");

     Bag rootBag = new Bag(g);

     rootBag.initializeForDecomposition();
     
     MTDecomposerHeuristic dec = new MTDecomposerHeuristic(rootBag, 
         width, width, null, null);

     dec.counting = true;
     
     dec.decompose();

//     dec.checkAgainstDecompositionInFile("result/" + path, name);
     
     System.out.println(name + " decomposed, flattening.. ");
     
     rootBag.flatten();
     rootBag.setWidth();

     System.out.println(name + " solved with width " + 
         rootBag.width + " with "
         + rootBag.nestedBags.size() + " bags");

     TreeDecomposition td = rootBag.toTreeDecomposition();
//     td.writeTo(System.out);
     td.validate();
     // td.analyze(1);
   }
   */
  }
  private static void test() {
    /*
//    String path = "coloring_gr2";
    // String path = "coloring-targets";
    // String name = "queen5_5";
//     String name = "queen6_6";
//     String name = "queen7_7";
//     String name = "queen8_8";
//     String name = "queen9_9";
    // String name = "queen8_12";
    // String name = "queen10_10";
//     String name = "mulsol.i.1";
    // String name = "mulsol.i.2";
//     String name = "anna";
//     String name = "david";
//     String name = "huck";
//     String name = "homer";
//     String name = "jean";
//     String name = "inithx.i.1_pp";
//    String name = "inithx.i.2_pp";
//     String name = "dimacs_inithx.i.2-pp";
    // String name = "dimacs_inithx.i.3-pp";
    // String name = "fpsol2.i.1";
//     String name = "fpsol2.i.2_pp";
//     String name = "mulsol.i.1_pp";
//     String name = "mulsol.i.2_pp";
    // String name = "dimacs_mulsol.i.2";

//     String name = "mulsol.i.2_pp";
    // String name = "fpsol2.i.2";
    // String name = "le450_5a";
    // String name = "le450_5b";
    // String name = "myciel3";
//     String name = "myciel4";
//     String name = "myciel5";
//     String name = "myciel6";
    // String name = "myciel7";
//     String name = "anna";
//     String path = "grid";
//     String name = "troidal3_3";
//     String name = "troidal4_4";
//     String name = "troidal5_5";
//     String name = "troidal6_6";
//     String name = "troidal7_7";
//     String path = "random";
//     String name = "gnm_50_250_1";
    // String path = "pace16/100";
    // String name = "dimacs_zeroin.i.3-pp";
    // String path = "pace16/1000";
    // String name = "4x12_torusGrid";
    // String name = "RandomBipartite_25_50_3";
    // String name = "RKT_300_75_30_0";
    // String name = "RandomBoundedToleranceGraph_80";
    // String path = "pace16/3600";
    // String name = "8x6_torusGrid";
    // String path = "pace16/unsolved";
    // String name = "6s10.gaifman";
//     String path = "test";
//     String name = "test1";
//     String name = "test2";
//     String name = "test3";
//     String name = "test4";
//     String name = "test5";
//     String name = "test6";
//    String path = "ex2017public";
//     String name = "ex001";
//     String name = "ex003";
//     String name = "ex005";
//     String name = "ex047";
//        String name = "ex129";
//     String name = "ex135";
//     String name = "ex153";
//     String name = "ex175";
    String path = "he_temp3";
//    String name = "he075_3";
//    String name = "he085_3";
//    String name = "he091_3";
    String name = "he095_3";
    
    Graph g = Graph.readGraph("instance/" + path, name);

    System.out.println("Graph " + name + " read");
    // for (int v = 0; v < g.n; v++) {
    // System.out.println(v + ": " + g.degree[v] + ", " + g.neighborSet[v]);
    // }

    long t0 = System.currentTimeMillis();
    Bag rootBag = new Bag(g);

    rootBag.initializeForDecomposition();
    
    MTDecomposerHeuristic dec = new MTDecomposerHeuristic(rootBag, 
        g.minDegree(), g.n - 1, null, null);
//        g.minDegree(), 50, null, null);

    dec.setMaxMultiplicity(1);
    
    dec.decompose();

//    dec.checkAgainstDecompositionInFile("result/" + path, name);
    
    System.out.println(name + " decomposed, flattening.. ");
    
    rootBag.flatten();
    rootBag.setWidth();

    long t = System.currentTimeMillis();
    System.out.println(name + " solved with width " + 
        rootBag.width + " with "
        + rootBag.nestedBags.size() + " bags in " + (t - t0) + " millisecs");

    TreeDecomposition td = rootBag.toTreeDecomposition();
//    td.writeTo(System.out);
    td.validate();
    // td.analyze(1);
    File outFile = new File("result/" + path + "/" + name + ".td");
    PrintStream ps;
    try {
      ps = new PrintStream(new FileOutputStream(outFile));
      ps.println("c width = " + td.width + ", time = " + (t - t0));
      td.writeTo(ps);
      ps.close();
    } catch (FileNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    */
  }

  static class MinComparator implements Comparator<VertexSet> {
    @Override
    public int compare(VertexSet o1, VertexSet o2) {
      return o1.nextSetBit(0) - o2.nextSetBit(0);
    }
  }

  public static void main(String args[]) {
    //test();
//    count();
  }
}
