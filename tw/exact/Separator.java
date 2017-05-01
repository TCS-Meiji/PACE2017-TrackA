/*
 * Copyright (c) 2017, Hisao Tamaki
 */

package tw.exact;

import java.util.ArrayList;

public class Separator {
  Bag parent;
  Graph graph;
  XBitSet vertexSet;
  int size;
  ArrayList<Bag> incidentBags;
  boolean safe;
  boolean unsafe;
  boolean wall;
  
  int[] parentVertex;

  public Separator(Bag parent) {
    this.parent = parent;
    graph = parent.graph;
    incidentBags = new ArrayList<>();
  }

  public Separator(Bag parent, XBitSet vertexSet) {
    this(parent);
    this.vertexSet = vertexSet;
    size = vertexSet.cardinality();
  }
  
  public void addIncidentBag(Bag bag) {
    incidentBags.add(bag);
  }
  
  public void removeVertex(int v) {
    if (vertexSet.get(v)) {
       size--;
    }
    vertexSet.clear(v);
  }
  
  public void invert() {
    vertexSet = convert(vertexSet, parent.inv);
    parent = parent.parent;
  }

  public void convert() {
    vertexSet = convert(vertexSet, parent.conv);
  }
  
  private XBitSet convert(XBitSet s, int[] conv) {
    XBitSet result = new XBitSet();
    for (int v = s.nextSetBit(0); v >= 0;
        v = s.nextSetBit(v + 1)) {
      result.set(conv[v]);
    }
    return result;
  }

  public void collectBagsToPack(ArrayList<Bag> list, Bag from) {
    for (Bag bag: incidentBags) {
      if (bag !=from) {
        bag.collectBagsToPack(list,  this);
      }
    }
  }

  public void figureOutSafety(SafeSeparator ss) {
    if (!safe && !unsafe) {
      safe = ss.isSafeSeparator(vertexSet);
      unsafe = !safe;
    }
  }
  
  public void figureOutSafetyBySPT() {
    if (!safe && !unsafe) {
      safe = isSafe();
      unsafe = !safe;
    }
  }
  
  public boolean isSafe() {
    return isSafeBySPT();
  }
  
  public boolean isSafeBySPT() {
    parentVertex = new int[graph.n];
    ArrayList<XBitSet> components = 
        graph.getComponents(vertexSet);
    for (XBitSet compo: components) {
      if (!isSafeComponentBySPT(compo)) {
        return false;
      }
    }
    return true;
  }
  
  private boolean isSafeComponentBySPT(XBitSet component) {
    XBitSet neighborSet = graph.neighborSet(component);
    XBitSet rest = graph.all.subtract(neighborSet).subtract(component);

    for (int v = neighborSet.nextSetBit(0); v >= 0;
        v = neighborSet.nextSetBit(v + 1)) {
      XBitSet missing = neighborSet.subtract(graph.neighborSet[v]);
      
      for (int w = missing.nextSetBit(0); w >= 0 && w <= v;
          w = missing.nextSetBit(w + 1)) {
        missing.clear(w);
      }

      if (!missing.isEmpty()) {
        XBitSet spt = shortestPathTree(v, missing, rest);
        if (spt == null) {
          return false;
        }
        rest.andNot(spt);
      }
    }
    return true;
  }

  private XBitSet shortestPathTree(int v, XBitSet targets,
      XBitSet available) {
    XBitSet union = available.unionWith(targets);
    
    XBitSet reached = new XBitSet(graph.n);
    reached.set(v);
    XBitSet leaves = (XBitSet) reached.clone();
    while (!targets.isSubset(reached) && !leaves.isEmpty()) {
      XBitSet newLeaves = new XBitSet(graph.n);
      for (int u = leaves.nextSetBit(0); u >= 0;
          u = leaves.nextSetBit(u + 1)) {
        XBitSet children = 
            graph.neighborSet[u].intersectWith(union).subtract(reached);
        for (int w = children.nextSetBit(0); w >= 0;
            w = children.nextSetBit(w + 1)) {
          reached.set(w);
          parentVertex[w] = u;
          if (available.get(w)) {
            newLeaves.set(w);
          }
        }
      }
      leaves = newLeaves;
    }
    
    if (!targets.isSubset(reached)) {
      return null;
    }

    XBitSet spt = new XBitSet(graph.n);
    for (int u = targets.nextSetBit(0); u >= 0;
        u = targets.nextSetBit(u + 1)) {
        int w = parentVertex[u];
        while (w != v) {
          spt.set(w);
          w = parentVertex[w];
        }
    }
    return spt;
  }


  public void dump(String indent) {
    System.out.println(indent + "sep:" + toString());
  }
  
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(vertexSet);
    sb.append("(");
    for (Bag bag: incidentBags){
      if (bag == null) {
        sb.append("null bag ");
      }
      else {
        sb.append(parent.nestedBags.indexOf(bag) + ":" + bag.vertexSet);
        sb.append(" ");
      }
    }
    sb.append(")");
    
    return sb.toString();
  }
  
}
