/*
 * Copyright (c) 2017, Hiromu Ohtsuka
*/

package tw.heuristic;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.LinkedList;
import java.util.Set;
import java.util.HashSet;
import java.util.Random;
import java.util.Collections;

public class MainDecomposer{
  public static enum Mode{
    greedy, pathDecomposition, treeDecomposition
  }
  public static final long MAX_TIME = 1800000;
  public static final long INITIAL_TIME_MS = 4000;
  public static final int MAX_MULTIPLICITY = 1;
  public static final long CUT_D_TIME_MS = 300000;
  public static final long DETECT_TIME_MS = 10000;

  private static Random random;
  private static Graph wholeGraph;
  private static TreeDecomposition best;
  private static int[][] invs;
  private static Bag[] bags;
  private static long detectSum;
  private static long startTime;

  private static final boolean DEBUG = false;

  private static int countGD, countPD, countTD;

  private static final Comparator< Bag > WIDTH_DESCENDING_ORDER =
    new Comparator< Bag >(){
      @Override
        public int compare(Bag b1, Bag b2){
          return -(Integer.compare(b1.getWidth(), b2.getWidth()));
        }
    };

  public static TreeDecomposition getBestTreeDecompositionSoFar(){
    return best;
  }

  private static void commit(){
    if(bags == null){
      return;
    }

    if(DEBUG){
      comment("commit");
    }

    Bag[] copiedBags = new Bag[bags.length];
    for(int i = 0; i < copiedBags.length; i++){
      copiedBags[i] = (Bag)bags[i].clone();
    }

    if(bags.length == 1){
      // trivial tree decomposition
      if(copiedBags[0].nestedBags == null || copiedBags[0].nestedBags.isEmpty()){
        TreeDecomposition trivial =
          new TreeDecomposition(0, copiedBags[0].graph.n - 1, copiedBags[0].graph);
        trivial.addBag(copiedBags[0].graph.all.toArray());
        if(best == null || trivial.width < best.width){
          best = trivial;
          comment("width = " + best.width);
          printTime();
        }
        return;
      }

      copiedBags[0].flatten();
      TreeDecomposition td = copiedBags[0].toTreeDecomposition();
      setWidth(td);

      if(best == null || td.width < best.width){
        best = td;
        comment("width = " + best.width);
        printTime();
      }

      return;
    }

    TreeDecomposition td = new TreeDecomposition(0, 0, wholeGraph);
    for(int i = 0; i < copiedBags.length; i++){
      // trivial tree decomposition
      if(copiedBags[i].nestedBags == null || copiedBags[i].nestedBags.isEmpty()){
        TreeDecomposition trivial =
          new TreeDecomposition(0, copiedBags[i].graph.n - 1, copiedBags[i].graph);
        trivial.addBag(copiedBags[i].graph.all.toArray());
        td.combineWith(trivial, invs[i], null);
      }
      else{
        copiedBags[i].flatten();
        td.combineWith(copiedBags[i].toTreeDecomposition(), invs[i], null);
      }
    }
    setWidth(td);

    if(best == null || td.width < best.width){
      best = td;
      comment("width = " + best.width);
      printTime();
    }
  }

  private static void setWidth(TreeDecomposition td){
    if(td == null){
      return;
    }
    int width = -1;
    for(int i = 1; i <= td.nb; i++){
      width = Math.max(width, td.bags[i].length - 1);
    }
    td.width = width;
  }

  private static void comment(String comment){
    System.out.println("c " + comment);
  }

  private static void printTime(){
    comment("time = " + (System.currentTimeMillis() - startTime) + " ms");
  }

  private static void initializeForDecomposition(Graph graph, long seed){
    wholeGraph = graph;
    best = null;
    bags = null;
    invs = null;
    detectSum = 0;
    random = new Random(seed);
    startTime = System.currentTimeMillis();

    // trivial tree decomposition
    best = new TreeDecomposition(0, wholeGraph.n - 1, wholeGraph);
    best.addBag(wholeGraph.all.toArray());

    if(DEBUG){
      comment("seed = " + seed);
    }
  }

  public static TreeDecomposition decompose(Graph graph, long seed){
    initializeForDecomposition(graph, seed);

    if(graph.n == 0){
      best = new TreeDecomposition(0, -1, graph);
      return best;
    }

    ArrayList< VertexSet > components = graph.getComponents(new VertexSet());

    int nc = components.size();

    if(nc == 1){
      if(graph.n <= 2){
        best = new TreeDecomposition(0, graph.n - 1, graph);
        best.addBag(graph.all.toArray());
        return best;
      }

      bags = new Bag[1];
      bags[0] = new Bag(graph);

      if(decomposeWithSmallCuts(bags[0])){
        commit();
      }

      if(bags[0].countSafeSeparators() == 0){
        decomposeGreedy(bags[0]);
      }
      else{
        for(Bag nb : bags[0].nestedBags){
          nb.makeRefinable();
          decomposeGreedy(nb);
        }
        bags[0].flatten();
      }

      commit();

      while(!bags[0].optimal){
        improveWithSeparators(bags[0], bags[0].getWidth());
        commit();
        bags[0].flatten();
      }

      return getBestTreeDecompositionSoFar();
    }

    Graph[] graphs = new Graph[nc];
    invs = new int[nc][];
    for(int i = 0; i < nc; i++){
      VertexSet component = components.get(i);
      graphs[i] = new Graph(component.cardinality());
      invs[i] = new int[graphs[i].n];
      int[] conv = new int[graph.n];
      int k = 0;
      for(int v = 0; v < graph.n; v++){
        if(component.get(v)){
          conv[v] = k;
          invs[i][k] = v;
          ++k;
        }
        else{
          conv[v] = -1;
        }
      }
      graphs[i].inheritEdges(graph, conv, invs[i]);
    }

    bags = new Bag[nc];
    for(int i = 0; i < nc; i++){
      bags[i] = new Bag(graphs[i]);
    }

    commit();

    for(int i = 0; i < nc; i++){
      decomposeWithSmallCuts(bags[i]);
    }

    commit();

    for(int i = 0; i < nc; i++){
      if(bags[i].countSafeSeparators() == 0){
        decomposeGreedy(bags[i]);
      }
      else{
        for(Bag nb : bags[i].nestedBags){
          nb.makeRefinable();
          decomposeGreedy(nb);
        }
        bags[i].flatten();
      }
    }

    commit();

    PriorityQueue< Bag > queue =
      new PriorityQueue< >(nc, WIDTH_DESCENDING_ORDER);

    for(int i = 0; i < nc; i++){
      queue.offer(bags[i]);
    }

    while(!queue.isEmpty()){
      Bag b = queue.poll();
      improveWithSeparators(b, b.getWidth());
      commit();
      b.flatten();
      if(!b.optimal){
        queue.offer(b);
      }
    }

    return getBestTreeDecompositionSoFar();
  }

  private static void improveWithSeparators(Bag bag, int k){
    if(bag.parent != null){
      bag.makeLocalGraph();
    }

    if(bag.getWidth() <= k - 1){
      return;
    }

    if(bag.separators == null){
      improve(bag, k);
      return;
    }

    if(bag.countSafeSeparators() > 0){
      bag.pack();
      for(Bag b : bag.nestedBags){
        improveWithSeparators(b, k);
      }
      return;
    }

    if(detectSum < DETECT_TIME_MS){
      detectSum += bag.detectSafeSeparators(DETECT_TIME_MS - detectSum);
    }

    if(bag.countSafeSeparators() == 0){
      improve(bag, k);
    }
    else{
      bag.pack();
      for(Bag b : bag.nestedBags){
        improveWithSeparators(b, k);
      }
    }
  }

  private static boolean improve(Bag bag, int k){
    if(bag.parent != null){
      bag.makeLocalGraph();
    }

    if(bag.getWidth() <= k - 1){
      return true;
    }

    if(bag.nestedBags == null){
      tryDecomposeExactly(bag, bag.graph.minDegree(), k - 1, k - 1);
      return bag.getWidth() <= k - 1;
    }

    while(bag.getWidth() >= k){
      Bag maxBag = null;
      for(Bag nb : bag.nestedBags){
        if(maxBag == null || nb.size > maxBag.size){
          maxBag = nb;
        }
      }
      long timeMS = INITIAL_TIME_MS;
      int gdVS = maxBag.size, pdVS = maxBag.size, tdVS = maxBag.size;
      int count = 0;
      while(true){
        if(DEBUG){
          comment("timeMS = " + timeMS);
          comment("gdVS = " + gdVS);
          comment("pdVS = " + pdVS);
          comment("tdVS = " + tdVS);
          comment("countGD = " + countGD);
          comment("countPD = " + countPD);
          comment("countTD = " + countTD);
        }
        gdVS = tryImproveWith(Mode.greedy, 
            bag, maxBag, timeMS, gdVS, 10, 3);
        if(gdVS < 0){
          ++countGD;
          break;
        }
        pdVS = tryImproveWith(Mode.pathDecomposition, 
            bag, maxBag, timeMS, pdVS, 30, 2);
        if(pdVS < 0){
          ++countPD;
          break;
        }
        tdVS = tryImproveWith(Mode.treeDecomposition, 
            bag, maxBag, timeMS, tdVS, 3, 3);
        if(tdVS < 0){
          ++countTD;
          break;
        }
        refresh(bag, maxBag, Math.max(gdVS, Math.max(pdVS, tdVS)) + 30);
        break;
      }
    }

    return true;
  }

  private static void searchBagsToImproveLikeTree(Bag bag, Separator from, int max,
      int targetWidth, ArrayList< Separator > separatorsToCheck){
    Set< Bag > visitedBags = new HashSet< >();
    VertexSet vs = new VertexSet();

    visitedBags.add(bag);
    vs.or(bag.vertexSet);

    collectSubsetBags(visitedBags, vs);

    while(vs.cardinality() < max){
      if(!choiceBagAtRandom(visitedBags, vs)){
        break;
      }
    }

    collectBagsConnectingLargeSeparator(visitedBags, vs, targetWidth, 0);
    collectSeparatorsTocheck(visitedBags, separatorsToCheck);
  }

  private static void searchBagsToImproveLikePath(Bag bag, Separator from, int max,
      int targetWidth, ArrayList< Separator > separatorsToCheck){
    Set< Bag > visitedBags = new HashSet< >();
    VertexSet vs = new VertexSet();

    visitedBags.add(bag);
    vs.or(bag.vertexSet);

    collectBagsLikePath(bag, visitedBags, vs, 4 * max / 5);

    while(vs.cardinality() < max){
      if(!choiceBagAtRandom(visitedBags, vs)){
        break;
      }
    }

    collectBagsConnectingLargeSeparator(visitedBags, vs, targetWidth, 0);
    collectSeparatorsTocheck(visitedBags, separatorsToCheck);
  }

  private static void collectBagsLikePath(
      Bag bag, Set< Bag > visitedBags, VertexSet vs, int max){
    Bag s = bag, t = bag;
    while(vs.cardinality() < max){
      ArrayList< Bag > tBags = new ArrayList< >();
      for(Separator is : t.incidentSeparators){
        for(Bag ib : is.incidentBags){
          if(ib != t && ib != s && !visitedBags.contains(ib)){
            tBags.add(ib);
          }
        }
      }
      if(!tBags.isEmpty()){
        t = tBags.get(random.nextInt(tBags.size()));
        visitedBags.add(t);
        vs.or(t.vertexSet);
      }

      if(vs.cardinality() >= max){
        break;
      }

      ArrayList< Bag > sBags = new ArrayList< >();
      for(Separator is : s.incidentSeparators){
        for(Bag ib : is.incidentBags){
          if(ib != s && ib != t && !visitedBags.contains(ib)){
            sBags.add(ib);
          }
        }
      }
      if(!sBags.isEmpty()){
        s = sBags.get(random.nextInt(sBags.size()));
        visitedBags.add(s);
        vs.or(s.vertexSet);
      }

      if(tBags.isEmpty() && sBags.isEmpty()){
        break;
      }
    }

    collectSubsetBags(visitedBags, vs);
  }

  private static boolean choiceBagAtRandom(Set< Bag > visitedBags, VertexSet vs){
    ArrayList< Bag > outers = new ArrayList< >();
    for(Bag b : visitedBags){
      for(Separator is : b.incidentSeparators){
        for(Bag nb : is.incidentBags){
          if(nb != b && !visitedBags.contains(nb)){
            outers.add(nb);
          }
        }
      }
    }
    if(!outers.isEmpty()){
      Bag bag = outers.get(random.nextInt(outers.size()));
      visitedBags.add(bag);
      vs.or(bag.vertexSet);
      collectSubsetBags(visitedBags, vs);
      return true;
    }
    return false;
  }

  private static void collectSubsetBags(Set< Bag > visitedBags, VertexSet vs){
    ArrayList< Bag > toVisited = new ArrayList< >();
    while(true){
      for(Bag b : visitedBags){
        for(Separator is : b.incidentSeparators){
          for(Bag ib : is.incidentBags){
            if(ib != b && !visitedBags.contains(ib)
                && ib.vertexSet.isSubset(b.vertexSet)){
              toVisited.add(ib);
            }
          }
        }
      }
      if(toVisited.isEmpty()){
        return;
      }
      for(Bag b : toVisited){
        visitedBags.add(b);
        vs.or(b.vertexSet);
      }
      toVisited.clear();
    }
  }

  private static void collectBagsConnectingLargeSeparator(
      Set< Bag > visitedBags, VertexSet vs, int targetWidth, int d){
    ArrayList< Bag > toVisited = new ArrayList< >();
    while(true){
      for(Bag b : visitedBags){
        for(Separator is : b.incidentSeparators){
          if(Math.abs(targetWidth - is.size) <= d){
            for(Bag ib : is.incidentBags){
              if(!visitedBags.contains(ib)){
                toVisited.add(ib);
              }
            }
          }
        }
      }
      if(toVisited.isEmpty()){
        return;
      }
      for(Bag b : toVisited){
        visitedBags.add(b);
        vs.or(b.vertexSet);
        collectSubsetBags(visitedBags, vs);
      }
      toVisited.clear();
    }
  }

  private static void collectBagsFormingStar(
      Set< Bag > visitedBags, VertexSet vs){
    ArrayList< Bag > toVisited = new ArrayList< >();
    while(true){
      for(Bag b : visitedBags){
        for(Separator is : b.incidentSeparators){
          // star
          if(is.incidentBags.size() >= 3){
            for(Bag ib : is.incidentBags){
              if(!visitedBags.contains(ib)){
                toVisited.add(ib);
              }
            }
          }
        }
      }
      if(toVisited.isEmpty()){
        return;
      }
      for(Bag b : toVisited){
        visitedBags.add(b);
        vs.or(b.vertexSet);
        collectSubsetBags(visitedBags, vs);
      }
      toVisited.clear();
    }
  }

  private static void collectSeparatorsTocheck(
      Set< Bag > visitedBags, ArrayList< Separator > separatorsToCheck){
    for(Bag b : visitedBags){
      for(Separator is : b.incidentSeparators){
        for(Bag ib : is.incidentBags){
          if(ib != b && !visitedBags.contains(ib)){
            separatorsToCheck.add(is);
            break;
          }
        }
      }
    }
  }

  private static Bag findBagContaining(Bag bag, Bag whole){
    if(bag == whole){
      return whole;
    }

    for(Bag nb : whole.nestedBags){
      if(nb == bag){
        return nb;
      }
      if(nb.nestedBags == null){
        continue;
      }
      for(Bag b : nb.nestedBags){
        if(b == bag){
          return nb;
        }
      }
    }

    return null;
  }

  private static void decomposeGreedy(Bag bag){
    bag.initializeForDecomposition();
    GreedyDecomposer mfd = new GreedyDecomposer(bag);
    mfd.decompose();
  }

  private static boolean decomposeWithSmallCuts(Bag bag){
    bag.initializeForDecomposition();
    CutDecomposer cd = new CutDecomposer(bag);
    cd.decompose(CUT_D_TIME_MS);
    if(DEBUG){
      comment("finish cut decompose");
    }
    return bag.nestedBags != null && !bag.nestedBags.isEmpty();
  }

/*
  private static void decomposeGreedyWithSmallCuts(Bag bag){
    bag.initializeForDecomposition();
    CutDecomposer cd = new CutDecomposer(bag);
    cd.decompose();

    // [TODO]
    // commit();

    if(DEBUG){
      comment("finish cut decompose");
    }

    if(bag.countSafeSeparators() == 0){
      GreedyDecomposer gd = new GreedyDecomposer(bag);
      gd.decompose();
    }
    else{
      for(Bag nb : bag.nestedBags){
        nb.makeRefinable();
        GreedyDecomposer gd = new GreedyDecomposer(nb);
        gd.decompose();
      }
    }

    bag.flatten();
  }
  */

  private static void tryDecomposeExactly(Bag bag, int lowerBound, int upperBound, int targetWidth){
    if(lowerBound > upperBound){
      return;
    }

    Bag triedBag = (Bag)bag.clone();

    if(triedBag.parent != null){
      triedBag.makeLocalGraph();
    }

    decomposeGreedy(triedBag);
    if(triedBag.getWidth() <= targetWidth){
      replace(triedBag, bag);
      return;
    }

    triedBag.initializeForDecomposition();
    MTDecomposerHeuristic mtd = new MTDecomposerHeuristic(
        triedBag, lowerBound, upperBound, null, null, MAX_TIME);
    mtd.setMaxMultiplicity(MAX_MULTIPLICITY);
    if(!mtd.decompose()){
      return;
    }

    if(triedBag.getWidth() <= targetWidth){
      replace(triedBag, bag);
    }
  }

  private static int tryImproveWith(Mode mode,
      Bag whole, Bag maxBag, long time, int vsSize, int cycle, int d){
    if(DEBUG){
      comment("mode = " + mode);
      comment("cycle = " + cycle);
      comment("d = " + d);
      comment("timeLimit = " + time);
    }

    int k = whole.getWidth();
    int targetSize = vsSize;
    int count = 0;
    long sum = 0;
    while(true){
      if(DEBUG){
        comment("k = " + k);
        comment("vs = " + targetSize);
        comment("count = " + count);
        comment("sum = " + sum);
      }

      ArrayList< Separator > separatorsToCheck = new ArrayList< >();
      switch(mode){
        case greedy : case treeDecomposition :
          searchBagsToImproveLikeTree(
              maxBag, null, targetSize, k - 1, separatorsToCheck);
          break;
        case pathDecomposition :
          searchBagsToImproveLikePath(
              maxBag, null, targetSize, k - 1, separatorsToCheck);
          break;
      }
      for(Separator s : separatorsToCheck){
        s.wall = true;
      }
      if(!separatorsToCheck.isEmpty()){
        whole.pack();
      }

      Bag target;
      if(!separatorsToCheck.isEmpty()){
        target = findBagContaining(maxBag, whole);
      }
      else{
        target = whole;
      }

      if(DEBUG){
        comment("targetSize = " + target.size);
      }

      if(target.parent != null){
        target.makeLocalGraph();
      }

      Bag triedBag = (Bag)target.clone();
      triedBag.initializeForDecomposition();
      boolean success = false;
      switch(mode){
        case greedy :
          GreedyDecomposer gd = new GreedyDecomposer(triedBag);
          if(gd.decompose(time - sum)){
            success = true;
          }
          sum += gd.getTimeMS();
          break;

        case pathDecomposition :
          PathDecomposer pd = new PathDecomposer(triedBag, 
              triedBag.graph.minDegree(), k - 1);
          if(pd.decompose(time - sum)){
            success = true;
          }
          sum += pd.getTimeMS();
          break;

        case treeDecomposition :
          MTDecomposerHeuristic mtd = new MTDecomposerHeuristic(
              triedBag, triedBag.graph.minDegree(), k - 1, null, null, time - sum);
          mtd.setMaxMultiplicity(MAX_MULTIPLICITY);
          if(mtd.decompose()){
            success = true;
          }
          sum += mtd.getTimeMS();
          break;
      }

      for(Separator s : separatorsToCheck){
        s.wall = false;
      }

      if(success && triedBag.getWidth() <= k - 1){
        replace(triedBag, target);
        whole.flatten();
        return -1;
      }

      if(!separatorsToCheck.isEmpty()){
        whole.flatten();
      }

      if(sum >= time){
        break;
      }

      if(count % cycle == 0){
        targetSize += d;
      }

      ++count;
    }

    return targetSize;
  }

  private static void refresh(Bag whole, Bag maxBag, int vsSize){
    int k = whole.getWidth();
    ArrayList< Separator > separatorsToCheck = new ArrayList< >();
    searchBagsToImproveLikeTree(
        maxBag, null, vsSize, k - 1, separatorsToCheck);

    for(Separator s : separatorsToCheck){
      s.wall = true;
    }

    if(!separatorsToCheck.isEmpty()){
      whole.pack();
    }

    Bag target;
    if(!separatorsToCheck.isEmpty()){
      target = findBagContaining(maxBag, whole);
    }
    else{
      target = whole;
    }

    if(target.parent != null){
      target.makeLocalGraph();
    }
    target.initializeForDecomposition();
    GreedyDecomposer gd = new GreedyDecomposer(target);
    gd.decompose();

    for(Separator s : separatorsToCheck){
      s.wall = false;
    }

    whole.flatten();
  }

  private static void replace(Bag from, Bag to){
    to.graph = from.graph;
    to.nestedBags = from.nestedBags;
    to.separators = from.separators;
    to.incidentSeparators = from.incidentSeparators;

    for(Bag b : to.nestedBags){
      b.parent = to;
    }
    for(Separator s : to.separators){
      s.parent = to;
    }
  }

  private MainDecomposer(){}

  public static void main(String[] args){
    Runtime.getRuntime().addShutdownHook(new Thread(){
        @Override
        public void run(){
        TreeDecomposition result = getBestTreeDecompositionSoFar();
        if(result == null){
        comment("no solution");
        return;
        }
        //if(result.isValid(System.err)){
        comment("width = " + result.width);
        printTime();
        result.writeTo(System.out);
        //}
        //if(result.isValid(System.err)){
        //  comment("validation ok");
        //}
        }
        });

    long seed = 42;
    if(args.length >= 2 && "-s".equals(args[0])){
      seed = Long.parseLong(args[1]);
    }

    Graph graph = Graph.readGraph(System.in);

    comment("read Graph");

    decompose(graph, seed);

    printTime();
  }
}
