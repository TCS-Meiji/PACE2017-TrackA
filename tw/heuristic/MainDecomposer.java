package tw.heuristic;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.PriorityQueue;

public class MainDecomposer{
  public static final int MAX_VERTEX_NUM = 64;

  private static Graph wholeGraph;
  private static TreeDecomposition best;
  private static int[][] invs;
  private static Bag[] bags;

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
      setWidth(best);
      return;
    }

    TreeDecomposition td = new TreeDecomposition(0, 0, wholeGraph);
    for(int i = 0; i < copiedBags.length; i++){
      copiedBags[i].flatten();
      td.combineWith(copiedBags[i].toTreeDecomposition(), invs[i], null);
    }
    setWidth(td);
    best = td;

    if(DEBUG){
      comment("width = " + best.width);
    }
  }

  private static void setWidth(TreeDecomposition td){
    if(td == null){
      return;
    }
    int width = 0;
    for(int i = 1; i <= td.nb; i++){
      width = Math.max(width, td.bags[i].length - 1);
    }
    td.width = width;
  }

  private static void comment(String comment){
    System.out.println("c " + comment);
  }

  private static void initializeForDecomposition(Graph graph){
    wholeGraph = graph;
    best = null;
    bags = null;
    invs = null;
  }

  public static TreeDecomposition decompose(Graph graph){
    initializeForDecomposition(graph);

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

      decomposeGreedy(bags[0]);

      commit();
      if(DEBUG){
        comment("decomposed by greedy");
      }

      while(!bags[0].optimal){
        improveWithSeparators(bags[0]);
        commit();
        bags[0].flatten();
      }

      if(DEBUG){
        comment("got optimal solution");
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
      decomposeGreedy(bags[i]);
    }
    commit();
    if(DEBUG){
      comment("decomposed by greedy");
    }

    PriorityQueue< Bag > queue =
      new PriorityQueue< >(nc, WIDTH_DESCENDING_ORDER);

    for(int i = 0; i < nc; i++){
      queue.offer(bags[i]);
    }

    while(!queue.isEmpty()){
      Bag b = queue.poll();
      improveWithSeparators(b);
      commit();
      b.flatten();
      if(!b.optimal){
        queue.offer(b);
      }
    }

    if(DEBUG){
      comment("got optimal solution");
    }

    return getBestTreeDecompositionSoFar();
  }

  private static void improveWithSeparators(Bag bag){
    int k = bag.getWidth();

    bag.detectSafeSeparators();

    if(bag.countSafeSeparators() == 0){
      improve(bag, k);
    }
    else{
      bag.pack();
      for(Bag b : bag.nestedBags){
        improve(b, k);
      }
    }

    if(bag.getWidth() == k){
      bag.optimal = true;
    }
  }

  private static boolean improve(Bag bag, int k){
    if(bag.parent != null){
      bag.makeLocalGraph();
    }

    if(bag.getWidth() <= k - 1){
      return true;
    }

    if(bag.size <= MAX_VERTEX_NUM){
      tryDecomposeExactly(bag, bag.graph.minDegree(), k - 1, k - 1);
      return bag.getWidth() <= k - 1;
    }

    Separator wall = bag.choiceWall(k);
    if(wall == null){
      tryDecomposeExactly(bag, bag.graph.minDegree(), k - 1, k - 1);
      return bag.getWidth() <= k - 1;
    }

    bag.pack();

    Bag[] queue =
      bag.nestedBags.toArray(new Bag[bag.nestedBags.size()]);

    Arrays.sort(queue, WIDTH_DESCENDING_ORDER);

    for(Bag b : queue){
      if(!improve(b, k)){
        wall.wall = false;
        tryDecomposeExactly(bag, bag.graph.minDegree(), k - 1, k - 1);
        return bag.getWidth() <= k - 1;
      }
    }

    wall.wall = false;
    return bag.getWidth() <= k - 1;
  }

  private static void decomposeGreedy(Bag bag){
    bag.initializeForDecomposition();
    GreedyDecomposer mfd = new GreedyDecomposer(bag);
    mfd.decompose();
  }

  private static void tryDecomposeExactly(Bag bag, int lowerBound, int upperBound, int targetWidth){
    Bag triedBag = (Bag)bag.clone();

    decomposeGreedy(triedBag);

    if(triedBag.getWidth() <= targetWidth){
      replace(triedBag, bag);
      return;
    }

    if(triedBag.countSafeSeparators() == 0){
      if(triedBag.parent != null){
        triedBag.makeRefinable();
      }
      else{
        triedBag.initializeForDecomposition();
      }

      MTDecomposer mtd = new MTDecomposer(triedBag, lowerBound, upperBound);

      if(!mtd.decompose()){
        return;
      }
    }
    else{
      triedBag.pack();

      for(Bag b : triedBag.nestedBags){
        b.makeRefinable();
        MTDecomposer mtd = new MTDecomposer(b, lowerBound, upperBound);
        if(!mtd.decompose()){
          return;
        }
      }
    }

    replace(triedBag, bag);
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
            result.writeTo(System.out);
            //}
            //if(result.isValid(System.err)){
            //  comment("validation ok");
            //}
          }
    });

    Graph graph = Graph.readGraph(System.in);

    comment("read Graph");

    long start = System.currentTimeMillis();
    decompose(graph);
    long end = System.currentTimeMillis();

    comment("time = " + (end - start) + " ms");
  }
}
