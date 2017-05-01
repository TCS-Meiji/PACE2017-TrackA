/*
 * Copyright (c) 2017, Hisao Tamaki
 */

package tw.exact;

import java.io.File;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

public class GreedyDecomposer {

//  static final boolean VERBOSE = true;
  private static final boolean VERBOSE = false;
  // private static boolean DEBUG = true;
  static boolean DEBUG = false;

  Graph g;

  Bag whole;
  
  Mode mode;
  
  ArrayList<Separator> frontier;
  XBitSet remaining;
  
  Set<XBitSet> unsafes;
  Set<XBitSet> safes;
  SafeSeparator ss;
  
  Random random;

  public enum Mode {
    fill, defect, degree, safeFirst
//    fill, defect, degree
  }
  
  public GreedyDecomposer(Bag whole) {
    this(whole, Mode.fill);
  }

  public GreedyDecomposer(Bag whole, Mode mode) {
    this.whole = whole;
    this.mode = mode;

    // need a copy as we fill edges
    this.g = whole.graph.copy();
    if (mode == Mode.safeFirst) {
      safes = new HashSet<>();
      unsafes = new HashSet<>();
      ss = new SafeSeparator(whole.graph);
    }
  }

  public void decompose() {
    whole.initializeForDecomposition();
    frontier = new ArrayList<>();
    remaining = (XBitSet) g.all.clone();
    
    while (!remaining.isEmpty()) {
      int vmin = remaining.nextSetBit(0);
      int minCost = costOf(vmin);
      
//      ArrayList<Integer> minFillVertices = new ArrayList<>();
//      minFillVertices.add(vmin);
      
      for (int v = remaining.nextSetBit(vmin + 1);
          v >= 0; v = remaining.nextSetBit(v + 1)) {
        int cost = costOf(v);
        if (cost < minCost) {
          minCost = cost;
          vmin = v;
        }
      }

      ArrayList<Separator> joined = new ArrayList<>();
      
      XBitSet toBeAClique = new XBitSet(g.n);
      toBeAClique.set(vmin);
      
      for (Separator s: frontier) {
        XBitSet vs = s.vertexSet;
        if (vs.get(vmin)) {
          joined.add(s);
          toBeAClique.or(vs);
        }
      }
      
//      System.out.println(joined.size() + " joined");
      
      if (joined.isEmpty()) {
        toBeAClique.set(vmin);
      }
      else if (joined.size() == 1) {
        Separator uniqueSeparator = joined.get(0);
        if (g.neighborSet[vmin].intersectWith(remaining)
          .isSubset(uniqueSeparator.vertexSet)) {
            uniqueSeparator.removeVertex(vmin);
            if (uniqueSeparator.vertexSet.isEmpty()) {
              whole.separators.remove(uniqueSeparator);
              for (Bag b: uniqueSeparator.incidentBags) {
                b.incidentSeparators.remove(uniqueSeparator);
              }
              frontier.remove(uniqueSeparator);
            }
            remaining.clear(vmin);
            if (VERBOSE) {
              System.out.println("cleared " + vmin + " from" +
                  uniqueSeparator);
            }
            continue;
          }
      }

      toBeAClique.or(g.neighborSet[vmin].intersectWith(remaining));

      Bag bag = whole.addNestedBag(toBeAClique);

      if (VERBOSE) {
        System.out.println("added bag with " + vmin + ", " + bag);
      }

      g.fill(toBeAClique);
      
      XBitSet sep = toBeAClique.subtract(
          new XBitSet(new int[]{vmin}));
      
      if (!sep.isEmpty()) {
        Separator separator = 
            whole.addSeparator(sep);
        
        if (VERBOSE) {
          System.out.println("added separator " + separator +
              " with " + vmin + " absorbed");
        }

        separator.addIncidentBag(bag);
        bag.addIncidentSeparator(separator);
        
        frontier.add(separator);
      }
      
      if (VERBOSE) {
        System.out.println("adding incidences to bag: " + bag);
      }

      for (Separator s: joined) {
        assert !s.vertexSet.isEmpty();
        s.addIncidentBag(bag);
        bag.addIncidentSeparator(s);
        if (VERBOSE) {
          System.out.println("   " + s);
        }
        frontier.remove(s);
      }
      
      remaining.clear(vmin);
    }
    
    whole.setWidth();
  }

  int costOf(int v) {
    switch (mode) {
    case fill: return countFill(v);
    case defect: return defectCount(v);
    case degree: return degreeOf(v);
    case safeFirst: {
      XBitSet ns = g.neighborSet[v];
      ns.set(v);
      if (safes.contains(ns)) {
        return countFill(v);
      }
      else if (unsafes.contains(ns)) {
        return g.n * g.n + countFill(v);
      }
      else if (ss.isSafeSeparator(ns)) {
        safes.add(ns);
        return countFill(v);
      }
      else {
        unsafes.add(ns);
        return g.n * g.n + countFill(v);
      }
    }
    default: return 0;
    }
  }
  
  int defectCount(int v) {
    int count = 0;
    
    XBitSet ns = g.neighborSet[v].intersectWith(remaining);
    for (int w = ns.nextSetBit(0); w >= 0; 
        w = ns.nextSetBit(w + 1)) {
      if (ns.subtract(g.neighborSet[w]).cardinality() > 1) {
        count++;
      }
    }
    return count;
  }

  int countFill(int v) {
    int count = 0;
    XBitSet ns = g.neighborSet[v].intersectWith(remaining);
    for (int w = ns.nextSetBit(0); w >= 0; 
        w = ns.nextSetBit(w + 1)) {
      count += ns.subtract(g.neighborSet[w]).cardinality() - 1;
    }
    return count / 2;
  }

  int degreeOf(int v) {
    XBitSet ns = g.neighborSet[v].intersectWith(remaining);
    return ns.cardinality();
  }
}
