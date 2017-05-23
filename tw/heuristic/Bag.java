/*
 * Copyright (c) 2017, Hisao Tamaki and Hiromu Ohtsuka, Keitaro Makii
*/

package tw.heuristic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;
import java.util.HashMap;

public class Bag implements Cloneable{
  Bag parent;
  VertexSet vertexSet;
  int size;
  Graph graph;
  int conv[];
  int inv[];
  ArrayList<Bag> nestedBags;
  ArrayList<Separator> separators;
  ArrayList<Separator> incidentSeparators;
  int width;
  int separatorWidth;
  int lowerBound;
  int inheritedLowerBound;
  boolean optimal; 

  static final boolean DEBUG = false;

  public Bag(Graph graph) {
    this(null, graph.all);
    this.graph = graph;
  }

  public Bag(Bag parent, VertexSet vertexSet) {
    this.parent = parent;
    this.vertexSet = vertexSet;
    size = vertexSet.cardinality();
    incidentSeparators = new ArrayList<>();
  }

  public void initializeForDecomposition() {
    if (graph == null) {
      if (parent == null) {
        throw new RuntimeException("graph not available for decomposition");
      }
      else {
        makeLocalGraph();
      }
    }
    nestedBags = new ArrayList<>();
    separators = new ArrayList<>();
    width = 0;
    separatorWidth = 0;
  }

  public void attachSeparator(Separator separator) {
    incidentSeparators.add(separator);
  }

  public void makeRefinable() {
    makeLocalGraph();
    nestedBags = new ArrayList<>();
    separators = new ArrayList<>();
  }

  public int maxNestedBagSize() {
    if (nestedBags != null) {
      int max = 0;
      for (Bag bag:nestedBags) {
        if (bag.size > max) {
          max = bag.size;
        }
      }
      return max;
    }
    return -1;
  }

  public Bag addNestedBag(VertexSet vertexSet) {
    Bag bag = new Bag(this, vertexSet);
    nestedBags.add(bag);
    return bag;
  }

  public Separator addSeparator(VertexSet vertexSet) {
    Separator separator = new Separator(this, vertexSet);
    separators.add(separator);
    return separator;
  }

  public void addIncidentSeparator(Separator separator) {
    incidentSeparators.add(separator);
  }

  public void makeLocalGraph() {
    graph = new Graph(size);
    conv = new int[parent.size];
    inv = new int[size];

    VertexSet vertexSet = this.vertexSet;

    int k = 0;
    for (int v = 0; v < parent.size; v++) {
      if (vertexSet.get(v)) {
        conv[v] = k;
        inv[k++] = v;
      }
      else {
        conv[v] = -1;
      }
    }

    graph.inheritEdges(parent.graph, conv, inv);

    //    System.out.println("filling all, " + incidentSeparators.size() + " incident separators");
    for (Separator separator: incidentSeparators) {
      //      System.out.println("filling " + separator);
      graph.fill(convert(separator.vertexSet, conv));
    }
  }

  public int getWidth() {
    if (nestedBags == null) {
      return size - 1;
    }
    int max = 0;
    for (Bag bag: nestedBags) {
      int w = bag.getWidth();
      if (w > max) {
        max = w;
      }
    }
    /*
    for (Separator separator: separators) {
      int w = separator.vertexSet.cardinality();
      if (w > max) {
        max = w;
      }
    }
    */
    return max;

  }

  public void setWidth() {
    // assumes that the bag is flat

    //    System.out.println("setWidth for " + this.vertexSet);
    //    System.out.println("nestedBags = " + nestedBags);

    if (nestedBags == null) {
      width = size - 1;
      separatorWidth = 0;
      return;
    }

    width = 0;
    separatorWidth = 0;

    for (Bag bag: nestedBags) {
      if (bag.size - 1 > width) {
        width = bag.size - 1;
      }
    }

    for (Separator separator: separators) {
      if (separator.size > separatorWidth) {
        separatorWidth = separator.size;
      }
    }

    if (separatorWidth > width) {
      width = separatorWidth;
    }
  }

  public void flatten() {
    if (nestedBags == null) {
      return;
    }

    validate();
    for (Bag bag: nestedBags) {
      if (bag.nestedBags != null) {
        bag.flatten();
      }
    }
    validate();
    ArrayList<Separator> newSeparatorList = new ArrayList<>();
    for (Separator separator: separators) {
      //      System.out.println(separator.incidentBags.size() + " incident bags of " + 
      //          separator);
      ArrayList<Bag> newIncidentBags = new ArrayList<>();
      for (Bag bag: separator.incidentBags) {
        if (bag.parent == this && bag.nestedBags != null &&
            !bag.nestedBags.isEmpty()) {
          Bag nested = bag.findNestedBagContaining(
              convert(separator.vertexSet, bag.conv));
          nested.addIncidentSeparator(separator);
          if (nested == null) {
            bag.dump();
            System.out.println(" does not have a bag containing " + 
                convert(separator.vertexSet, bag.conv) + " which is originally " + 
                separator.vertexSet);
            this.dump();
          }

          newIncidentBags.add(nested);

        }
        else {
          newIncidentBags.add(bag);
        }
      }
      if (!newIncidentBags.isEmpty()) {
        separator.incidentBags = newIncidentBags;
        newSeparatorList.add(separator);
      }
      //      System.out.println("processed separator :" + separator);
    }
    separators = newSeparatorList;

    ArrayList<Bag> temp = nestedBags;
    nestedBags = new ArrayList<>();
    for (Bag bag: temp) {
      if (bag.nestedBags != null && !bag.nestedBags.isEmpty()) {
        for (Bag nested: bag.nestedBags) {
          //          System.out.println("inverting " + nested);
          nested.invert();
          nestedBags.add(nested);
          //          System.out.println("inverted " + nested);
        }
        for (Separator separator: bag.separators) {
          //          System.out.println("inverting sep " + separator);
          separator.invert();
          this.separators.add(separator);
          //          System.out.println("inverted sep " + separator);
        }
      }
      else {
        //        System.out.println("adding original bag " + bag.vertexSet);
        nestedBags.add(bag);
      }
    }
    setWidth();
    //    System.out.println("bag of size " + size + " flattened into " + nestedBags.size() + " bags and width " +
    //        width);
    //    for (Bag bag: nestedBags) {
    //      System.out.println("incident separators of " + bag.vertexSet);
    //      for (Separator s: bag.incidentSeparators) {
    //        System.out.println("  " + s.vertexSet);
    //        for (Bag b: s.incidentBags) {
    //          System.out.println("        " + b.vertexSet);
    //        }
    //      }
    //    }
  }

  public Bag findNestedBagContaining(VertexSet vertexSet) {
    for (Bag bag: nestedBags) {
      if (vertexSet.isSubset(bag.vertexSet)) {
        return bag;
      }
    }
    return null;
  }

  public void invert() {
    vertexSet = convert(vertexSet, parent.inv);
    parent = parent.parent;
  }

  public void convert() {
    vertexSet = convert(vertexSet, parent.conv);
  }

  public VertexSet convert(VertexSet s) {
    return convert(s, conv);
  }

  private VertexSet convert(VertexSet s, int[] conv) {
    if (conv.length < s.length()) {
      return null;
    }
    VertexSet result = new VertexSet();
    for (int v = s.nextSetBit(0); v >= 0;
        v = s.nextSetBit(v + 1)) {
      result.set(conv[v]);
    }
    return result;
  }

  public TreeDecomposition toTreeDecomposition() {
    setWidth();
    TreeDecomposition td = new TreeDecomposition(0, width, graph);
    for (Bag bag: nestedBags) {
      td.addBag(bag.vertexSet.toArray());
    }

    for (Separator separator: separators) {
      VertexSet vs = separator.vertexSet;
      Bag full = null;
      for (Bag bag: separator.incidentBags) {
        if (vs.isSubset(bag.vertexSet)) {
          full = bag;
          break;
        }
      }

      if (full != null) {
        int j = nestedBags.indexOf(full) + 1;
        for (Bag bag: separator.incidentBags) {

          if (bag != full) {
            td.addEdge(j, nestedBags.indexOf(bag) + 1);
          }
        }
      }
      else {
        int j = td.addBag(separator.vertexSet.toArray());
        for (Bag bag: separator.incidentBags) {
          td.addEdge(j, nestedBags.indexOf(bag) + 1);
        }
      }
    }

    return td;
  }

  public void detectSafeSeparators() {
    for (Separator separator: separators) {
      separator.figureOutSafetyBySPT();
    }
  }

  public long detectSafeSeparators(long timeMS) {
    long sum = 0;
    for (Separator separator: separators) {
      if(sum > timeMS){
        return sum;
      }
      separator.figureOutSafetyBySPT();
      sum += separator.getSteps() * graph.n / 10000;
      separator.safeSteps = 1;
    }
    return sum;
  }

  public Separator choiceWall(int k){
    if(separators == null){
      return null;
    }
    Separator separator = null;
    // greedy
    for(Separator s : separators){
      if(separator == null || 
          s.size < separator.size){
        separator = s;
      }
    }
    if(separator != null && separator.size < k){
      separator.wall = true;
      return separator;
    }
    return null;
  }

  public void pack() {
    ArrayList<Bag> newBagList = new ArrayList<>();
    for (Bag bag: nestedBags) {
      if (bag.parent == this) {
        ArrayList<Bag> bagsToPack = new ArrayList<>();
        bag.collectBagsToPack(bagsToPack, null);
        //        System.out.println("bags to pack: " + bagsToPack);
        if (bagsToPack.size() >= 2) {
          VertexSet vertexSet = new VertexSet(graph.n);
          for (Bag toPack: bagsToPack) {
            vertexSet.or(toPack.vertexSet);
          }
          Bag packed = new Bag(this, vertexSet);
          packed.initializeForDecomposition();
          packed.nestedBags = bagsToPack;
          for (Bag toPack: bagsToPack) {
            toPack.parent = packed;
            toPack.convert();
          }
          newBagList.add(packed);
        }
        else {
          newBagList.add(bag);
        }
      }
    }
    nestedBags = newBagList;

    ArrayList<Separator> newSeparatorList = new ArrayList<>();

    for (Separator separator: separators) {
      boolean internal = true;
      Bag parent = null;
      for (Bag b: separator.incidentBags) {
        if (b.parent == this) {
          internal = false;
          break;
        }
        else if (parent == null) {
          parent = b.parent;
        }
        else if (b.parent != parent) {
          internal = false;
          break;
        }
      }
      if (internal) {
        separator.parent = parent;
        separator.convert();
        parent.separators.add(separator);
      }
      else {
        ArrayList<Bag> newIncidentBags = new ArrayList<>();
        for (Bag b: separator.incidentBags) {
          if (b.parent == this) {
            newIncidentBags.add(b);
          }
          else {
            newIncidentBags.add(b.parent);
            b.parent.incidentSeparators.add(separator);
            b.incidentSeparators.remove(separator);
          }
        }
        separator.incidentBags = newIncidentBags;
        newSeparatorList.add(separator);    
      }
    }

    separators = newSeparatorList;

    for (Bag bag: nestedBags) {
      bag.setWidth();
    }
    setWidth();
  }

  void collectBagsToPack(ArrayList<Bag> list, Separator from) {
    list.add(this);
    for (Separator separator: incidentSeparators) {
      //      System.out.println(" safe = " + separator.safe);
      if (separator == from || separator.safe || separator.wall) {
        continue;
      }
      separator.collectBagsToPack(list,  this);
    }
  }

  public int countSafeSeparators() {
    int count = 0;
    for (Separator separator: separators) {
      if (separator.safe) {
        count++;
      }
    }
    return count;
  }

  public void dump() {
    dump("");
  }

  public void validate() {
    if(!DEBUG){
      return;
    }

    if (nestedBags != null) {
      //      assert !nestedBags.isEmpty() : "no nested bags " + this; 
      for (Bag b: nestedBags) {
        b.validate();
        assert !b.vertexSet.isEmpty(): "empty bag " + b;
        assert b.parent == this: "parent of " + b + 
          "\n which is " + b.parent +
          "\n is supposed to be " + this;
      }
      for (Separator s: separators) {
        assert !s.vertexSet.isEmpty(): "empty seprator " + s;
        assert s.parent == this: "parent of " + s + 
          "\n which is " + s.parent +
          "\n is supposed to be " + this;
      }
      for (Bag b: nestedBags) {
        for (Separator s: b.incidentSeparators) {
          assert !s.vertexSet.isEmpty(): "empty seprator " + s + 
                                          "\n incident to " + b;
          assert s.parent == this: "parent of " + s + 
            "\n which is " + s.parent +
            "\n is supposed to be " + this + 
            "\n where the separator is incident to bag " + b;
          assert s.vertexSet.isSubset(b.vertexSet): "separator vertex set " + s.vertexSet + 
                                                     "\n is not a subset of the bag vertex set " + b.vertexSet;
        }
      }
      for (Separator separator: separators) {
        for (Bag b: separator.incidentBags) {
          assert b != null;
          assert b.parent == this: "parent of " + b + 
            "\n which is " + b.parent +
            "\n is supposed to be " + this + 
            "\n where the bag is incident to separator " + separator;
          assert separator.vertexSet.isSubset(b.vertexSet): "separator vertex set " + 
                                                             separator.vertexSet + 
                                                             "\n is not a subset of the bag vertex set " + b.vertexSet;
        }
      }
    }
  }

  private void dump(String indent) {
    System.out.println(indent + "bag:" + vertexSet);
    System.out.print(indent + "width = " + width + ", conv = ");
    System.out.println(Arrays.toString(conv));
    if (nestedBags != null) {
      System.out.println(indent + nestedBags.size() + " subbags:"); 
      for (Bag bag: nestedBags) {
        bag.dump(indent + "  ");
      }
      for (Separator separator: separators) {
        separator.dump(indent + "  ");
      }
    }
  }

  public String toString() {
    StringBuilder sb = new StringBuilder();
    if (parent != null) {
      sb.append("bag" + parent.nestedBags.indexOf(this) + ":");
    }
    else {
      sb.append("root bag :");
    }
    sb.append(vertexSet);
    return sb.toString();
  }

  @Override
    public Bag clone(){
      try{
        Bag result = (Bag)super.clone();

        if(conv != null){
          result.conv = Arrays.copyOf(conv, conv.length);
        }
        if(inv != null){
          result.inv = Arrays.copyOf(inv, inv.length);
        }

        Map< Bag, Bag > newBagOf = new HashMap< >();
        if(nestedBags != null){
          result.nestedBags = new ArrayList< >(nestedBags.size());
          for(Bag b : nestedBags){
            Bag cb = (Bag)b.clone();
            cb.parent = result;
            result.nestedBags.add(cb);
            newBagOf.put(b, cb);
          }
        }

        Map< Separator, Separator > newSeparatorOf = new HashMap< >();
        if(separators != null){
          result.separators = new ArrayList< >(separators.size());
          for(Separator s : separators){
            Separator cs = (Separator)s.clone();
            cs.parent = result;
            result.separators.add(cs);
            newSeparatorOf.put(s, cs);
          }
        }

        if(incidentSeparators != null){
          result.incidentSeparators = new ArrayList< >(incidentSeparators);
        }

        if(nestedBags != null){
          for(Bag b : result.nestedBags){
            ArrayList< Separator > newIncidentSeparatorList =
              new ArrayList< >(b.incidentSeparators.size());
            for(Separator s : b.incidentSeparators){
              newIncidentSeparatorList.add(newSeparatorOf.get(s));
            }
            b.incidentSeparators = newIncidentSeparatorList;
          }
        }

        if(separators != null){
          for(Separator s : result.separators){
            ArrayList< Bag > newIncidentBagList =
              new ArrayList< >(s.incidentBags.size());
            for(Bag b : s.incidentBags){
              newIncidentBagList.add(newBagOf.get(b));
            }
            s.incidentBags = newIncidentBagList;
          }
        }

        return result;
      }
      catch(CloneNotSupportedException cnse){
        throw new AssertionError();
      }
    }
}
