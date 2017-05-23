/*
 * Copyright (c) 2017, Hiromu Ohtsuka
*/

package tw.heuristic;

import java.util.Set;
import java.util.HashSet;

import java.util.Arrays;

public class PathDecomposer{
  private Bag whole;
  private Graph graph;
  private int n;
  private int lowerBound, upperBound;

  private int width;
  private Set< VertexSet > failureTable;
  private int[] separationSequence;

  private static final long STEPS_PER_MS = 1000;
  private long TIME_LIMIT;
  private long count;
  private boolean abort;

  private static final boolean DEBUG = false;

  public PathDecomposer(Bag bag,
      int lowerBound, int upperBound){
    this.whole = bag;
    this.graph = bag.graph;
    this.n = bag.graph.n;
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;

    if(!graph.isConnected(graph.all)){
      System.err.println("graph must be connected");
    }

    assert(lowerBound <= upperBound);
  }

  public PathDecomposer(Bag bag){
    this(bag, bag.graph.minDegree(), bag.graph.n - 1);
  }

  public boolean decompose(long timeMS){
    abort = false;
    count = 0;
    TIME_LIMIT = STEPS_PER_MS * timeMS;

    failureTable = new HashSet< >();

    boolean exist = false;
    width = upperBound;
    while(true){
      if(DEBUG){
        comment("currentwidth = " + width);
      }
      if(vsSearch(width, 0, new VertexSet())){
        makeSeparationSequence();
        exist = true;
      }
      else{
        ++width;
        break;
      }
      if(width == lowerBound){
        break;
      }
      --width;
    }

    if(DEBUG){
      comment("in path count = " + count);
    }

    if(!exist || abort){
      return false;
    }

    makePathDecompositionWithSeparationSequence();

    if(DEBUG){
      validate();
    }

    return true;
  }

  public boolean isAborted(){
    return abort;
  }

  public long getTimeMS(){
    return count / STEPS_PER_MS;
  }

  private boolean vsSearch(int w, int i, VertexSet vs){
    if(abort){
      return false;
    }

    if(i == n){
      return true;
    }

    if(failureTable.contains(vs)){
      return false;
    }

    for(int v = 0; v < n; v++){
      if(abort){
        return false;
      }
      ++count;
      if(count > TIME_LIMIT){
        abort = true;
      }
      if(vs.get(v)){
        continue;
      }
      int ns0 = graph.neighborSet(vs).cardinality();
      vs.set(v);
      int ns = graph.neighborSet(vs).cardinality();
      if(ns > w){
        vs.clear(v);
        continue;
      }
      if(ns <= ns0){
        return vsSearch(w, i + 1, vs);
      }
      if(vsSearch(w, i + 1, vs)){
        return true;
      }
      vs.clear(v);
    }

    failureTable.add((VertexSet)vs.clone());
    return false;
  }

  private void makeSeparationSequence(){
    separationSequence = new int[n];

    VertexSet vs = new VertexSet();
    for(int i = 0; i < n; i++){
      for(int v = 0; v < n; v++){
        if(vs.get(v)){
          continue;
        }
        vs.set(v);
        if(graph.neighborSet(vs).cardinality() <= width
            && !failureTable.contains(vs)){
          separationSequence[i] = v;
          break;
        }
        else{
          vs.clear(v);
        }
      }
    }
  }

  private void makePathDecompositionWithSeparationSequence(){
    VertexSet vs = new VertexSet();
    VertexSet vs1 = new VertexSet();
    Separator s0 = null;
    for(int i = 0; i < n; i++){
      int v = separationSequence[i];
      vs.set(v);

      VertexSet ns = graph.neighborSet(vs);
      VertexSet bvs = ns.unionWith(new VertexSet(new int[]{v}));

      if(s0 != null && bvs.isSubset(s0.vertexSet)){
        continue;
      }

      Bag b = whole.addNestedBag(bvs);

      if(s0 != null){
        s0.vertexSet.and(b.vertexSet);
        s0.addIncidentBag(b);
        b.addIncidentSeparator(s0);
      }

      vs1.or(bvs);
      if(vs1.equals(graph.all)){
        break;
      }

      Separator s = whole.addSeparator(ns);
      b.addIncidentSeparator(s);
      s.addIncidentBag(b);

      s0 = s;
    }
  }

  private static void comment(String comment){
    System.out.println("c " + comment);
  }

  private void validate(){
    if(DEBUG){
      whole.validate();

      for(Separator s : whole.separators){
        // path
        assert(s.incidentBags.size() == 2);
      }

      for(Separator s : whole.separators){
        for(Bag ib : s.incidentBags){
          // not redundant
          assert(!ib.vertexSet.equals(s.vertexSet));
          assert(s.vertexSet.isSubset(ib.vertexSet));
        }
      }

      for(Separator s : whole.separators){
        assert(graph.getComponents(s.vertexSet).size() >= 2);
      }
    }
  }

  private static void randomTest(){
    int c = 100;
    for(int i = 0; i < c; i++){
      Graph graph = Graph.randomGraph(100, 800, i);

      if(!graph.isConnected(graph.all)){
        continue;
      }

      Bag whole = new Bag(graph);
      whole.initializeForDecomposition();
      PathDecomposer pd = new PathDecomposer(whole);
      pd.decompose(10);

      TreeDecomposition path = whole.toTreeDecomposition();

      if(!path.isValid(System.err)){
        System.err.println("invalid solution");
        return;
      }

      path.writeTo(System.out);
    }
  }

  public static void main(String[] args){
    Graph graph = Graph.readGraph(System.in);

    Bag whole = new Bag(graph);
    whole.initializeForDecomposition();
    PathDecomposer pd = new PathDecomposer(whole);
    pd.decompose(5);

    TreeDecomposition path = whole.toTreeDecomposition();
    path.writeTo(System.out);

    //randomTest();
  }
}
