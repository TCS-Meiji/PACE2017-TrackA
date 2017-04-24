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
  public static final int C = 3;
  public static final int D = 10;
  public static final int TIME_LIMIT = 300;
  public static final int MAX_MULTIPLICITY = 1;

  private static Random random;
  private static Graph wholeGraph;
  private static TreeDecomposition best;
  private static int[][] invs;
  private static Bag[] bags;
  private static long startTime;

  private static final boolean DEBUG = false;

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

    Bag[] copiedBags = new Bag[bags.length];
    for(int i = 0; i < copiedBags.length; i++){
      copiedBags[i] = (Bag)bags[i].clone();
    }

    if(bags.length == 1){
      copiedBags[0].flatten();
      best = copiedBags[0].toTreeDecomposition();

      if(DEBUG){
        comment("width = " + best.width);
        printTime();
      }

      return;
    }

    TreeDecomposition td = new TreeDecomposition(0, 0, wholeGraph);
    for(int i = 0; i < copiedBags.length; i++){
      copiedBags[i].flatten();
      td.combineWith(copiedBags[i].toTreeDecomposition(), invs[i], null);
    }
    best = td;

    if(DEBUG){
      comment("width = " + best.width);
      printTime();
    }
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
    random = new Random(seed);
    startTime = System.currentTimeMillis();

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

      decomposeGreedyWithSmallCuts(bags[0]);
      //decomposeGreedy(bags[0]);

      commit();

      if(DEBUG){
        comment("decomposed by greedy");
        bags[0].validate();
        printTime();
      }

      while(!bags[0].optimal){
        improveWithSeparators(bags[0], bags[0].getWidth());
        commit();
        bags[0].flatten();
      }

      if(DEBUG){
        comment("got optimal solution");
        bags[0].validate();
        printTime();
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

    for(int i = 0; i < nc; i++){
      decomposeGreedyWithSmallCuts(bags[i]);
      //decomposeGreedy(bags[i]);
    }

    commit();

    if(DEBUG){
      comment("decomposed by greedy");
      printTime();
    }

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

    if(DEBUG){
      comment("got optimal solution");
      printTime();
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

    bag.detectSafeSeparators();

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
      Bag max = null;
      for(Bag nb : bag.nestedBags){
        if(max == null || nb.size > max.size){
          max = nb;
        }
      }

      int r = max.size;
      int count = 1;
      for(;;){
        ArrayList< Separator > separatorsToCheck = new ArrayList< >();
        searchBagsToImprove(max, null, r, separatorsToCheck);

        for(Separator s : separatorsToCheck){
          s.wall = true;
        }

        Bag target;
        if(!separatorsToCheck.isEmpty()){
          bag.pack();
          target = findBagContaining(max, bag);
        }
        else{
          target = bag;
        }

        r = target.size;

        if(target.parent != null){
          target.makeLocalGraph();
        }

        tryDecomposeExactly(target, target.graph.minDegree(), k - 1, k - 1);

        for(Separator s : separatorsToCheck){
          s.wall = false;
        }

        if(!separatorsToCheck.isEmpty()){
          bag.flatten();
        }

        if(target.getWidth() <= k - 1){
          break;
        }

        if(count == 1 || count % C == 0){
          r += D;
        }

        ++count;
      }
    }

    return true;
  }

  private static void searchBagsToImprove(Bag bag, Separator from, int max,
      ArrayList< Separator > separatorsToCheck){
    Set< Separator > visitedSeps = new HashSet< >();
    Set< Bag > visitedBags = new HashSet< >();
    VertexSet vs = new VertexSet();

    visitedBags.add(bag);
    vs.or(bag.vertexSet);

    while(vs.cardinality() < max){
      ArrayList< Bag > outers = new ArrayList< >();
      ArrayList< Bag > choicedBags = new ArrayList< >();
      for(Bag b : visitedBags){
        for(Separator is : b.incidentSeparators){
          for(Bag nb : is.incidentBags){
            if(nb == b || visitedBags.contains(nb)){
              continue;
            }
            if(nb.vertexSet.isSubset(b.vertexSet)){
              choicedBags.add(nb);
            }
            else{
              outers.add(nb);
            }
          }
        }
      }

      if(!outers.isEmpty()){
        choicedBags.add(outers.get(random.nextInt(outers.size())));
      }

      for(Bag b : choicedBags){
        visitedBags.add(b);
        vs.or(b.vertexSet);
        for(Separator is : b.incidentSeparators){
          for(Bag nb : is.incidentBags){
            if(nb != b && visitedBags.contains(nb)){
              visitedSeps.add(is);
              break;
            }
          }
        }
      }
    }

    for(Bag b : visitedBags){
      for(Separator is : b.incidentSeparators){
        if(!visitedSeps.contains(is)){
          separatorsToCheck.add(is);
        }
        else if(is.incidentBags.size() >= 3){
          boolean all = true;
          for(Bag ib : is.incidentBags){
            if(!visitedBags.contains(ib)){
              all = false;
              break;
            }
          }
          if(!all){
            separatorsToCheck.add(is);
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

  private static void decomposeGreedyWithSmallCuts(Bag bag){
    bag.initializeForDecomposition();
    CutDecomposer cd = new CutDecomposer(bag);
    cd.decompose();

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

  private static void tryDecomposeExactly(Bag bag, int lowerBound, int upperBound, int targetWidth){
    if(DEBUG){
      comment("try decompose exactly");
      comment("targetWidth = " + targetWidth + ", width = " + bag.getWidth() + ", size = " + bag.size);
      bag.validate();
    }

    Bag triedBag = (Bag)bag.clone();

    if(triedBag.parent != null){
      triedBag.makeLocalGraph();
    }

    decomposeGreedy(triedBag);
    //decomposeGreedyWithOneTwoCuts(triedBag);

    if(triedBag.getWidth() <= targetWidth){
      replace(triedBag, bag);
      return;
    }

    triedBag.detectSafeSeparators();

    if(triedBag.countSafeSeparators() == 0){
      triedBag.initializeForDecomposition();
      //MTDecomposer mtd = new MTDecomposer(triedBag, lowerBound, upperBound);
      CPUTimer timer = new CPUTimer();
      timer.setTimeout(TIME_LIMIT);
      MTDecomposerHeuristic mtd = new MTDecomposerHeuristic(triedBag, lowerBound, upperBound, null, timer);
      mtd.setMaxMultiplicity(MAX_MULTIPLICITY);
      if(!mtd.decompose()){
        return;
      }
    }
    else{
      triedBag.pack();
      for(Bag b : triedBag.nestedBags){
        b.makeRefinable();
        //MTDecomposer mtd = new MTDecomposer(b, lowerBound, upperBound);
        CPUTimer timer = new CPUTimer();
        timer.setTimeout(TIME_LIMIT);
        MTDecomposerHeuristic mtd = new MTDecomposerHeuristic(b, lowerBound, upperBound, null, timer);
        mtd.setMaxMultiplicity(MAX_MULTIPLICITY);
        if(!mtd.decompose()){
          return;
        }
      }
    }

    if(triedBag.getWidth() <= targetWidth){
      replace(triedBag, bag);
      bag.flatten();
      for(Separator s : bag.separators){
        s.safe = s.unsafe = false;
      }
    }
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
