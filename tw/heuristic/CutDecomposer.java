package tw.heuristic;

import java.util.ArrayList;
import java.util.BitSet;

public class CutDecomposer{
  public static final int LN = 2000;
  public static final int HN = 100000;
  public static final int HM = 1000000;
  public static int now;
  public static int cu;
  public static int compSize;
  private Bag whole;

  private static final boolean DEBUG = false;

  private class CutDivide{
    Separator sep;
    VertexSet c1,c2;
    CutDivide(Separator s,VertexSet a,VertexSet b){
      sep = s;
      c1 = a;
      c2 = b;
    }
  }
    private class NextBag{
      Bag bag;
      int start;
      NextBag(Bag b,int s){
        bag = b;
        start = s;
      }
    }

  public CutDecomposer(Bag whole){
    this.whole = whole;
  }

  public void decompose(){
//    whole.initializeForDecomposition();
    decomposeWithOneCuts();
    if(whole.graph.n <= LN){

      decomposeWithTwoCuts();
      whole.flatten();
      whole.setWidth();

      for(int i=3;i<=4;i++){
        decomposeWithSmallCuts(i);
        whole.flatten();
        whole.setWidth();
      }
      if(DEBUG){
        whole.toTreeDecomposition();
        whole.validate();
      }
    }
    else if(whole.graph.n <= HN  && whole.graph.numberOfEdges() <= HM){
      decomposeWithSmallCuts(2);
      whole.flatten();
      whole.setWidth();
      if(whole.graph.n <= 20000){
        decomposeWithSmallCuts(3);
        whole.flatten();
        whole.setWidth();
      }
      if(whole.graph.n <= 10000){
        decomposeWithSmallCuts(4);
        whole.flatten();
        whole.setWidth();
      }
    }
    else{
      whole.flatten();
      whole.setWidth();
    }

    if(DEBUG){
      whole.validate();
    }
  }

  private static void comment(String comment){
    System.out.println("c " + comment);
  }

  private void decomposeWithOneCuts(){
    VertexSet articulationSet = new VertexSet();
    ArrayList< VertexSet > bcc =
      whole.graph.getBiconnectedComponents(articulationSet);

    if(articulationSet.isEmpty()){
      return;
    }

    if(DEBUG){
      comment("detected 1-cuts");
    }

    whole.initializeForDecomposition();

    for(int a = articulationSet.nextSetBit(0);
      a >= 0; a = articulationSet.nextSetBit(a + 1)){
      Separator s = whole.addSeparator(new VertexSet(new int[]{a}));
      s.safe = true;
    }

    for(VertexSet bc : bcc){
      whole.addNestedBag(bc);
    }

    for(Separator s : whole.separators){
      for(Bag b : whole.nestedBags){
        if(s.vertexSet.isSubset(b.vertexSet)){
          b.addIncidentSeparator(s);
          s.addIncidentBag(b);
        }
      }
    }

    if(DEBUG){
      comment("decomposes with 1-cuts");
      comment("1-cutsSize:" + articulationSet.cardinality());
    }
  }

  private void decomposeWithSmallCuts(int c){
    if(whole.nestedBags != null && !whole.nestedBags.isEmpty()){
      for(Bag nb : whole.nestedBags){
        decomposeWithSmallCuts(nb,c);
      }
    }
    else{
      decomposeWithSmallCuts(whole,c);
    }
    if(DEBUG){
      comment("decompose with small-cuts");
    }
  }

  private void decomposeWithSmallCuts(Bag bag,int c){
    if(bag != whole){
      bag.makeLocalGraph();
    }
    Graph lg = bag.graph;

    cu = c;

    compSize = 6+cu;

    NextBag nb = new NextBag(bag,0);

    while(true){
      nb = decomposeWithSmallCuts(nb.bag,nb.start,lg.n);
//      nb = decomposeWithSmallCuts(nb.bag,0,lg.n);
      if (nb == null){
        return;
      }
      nb.bag.makeLocalGraph();
      lg = nb.bag.graph;

      compSize = 6+cu;

    }
  }

  private NextBag decomposeWithSmallCuts(Bag bag,int start,int end){
    for(int i=start;i<end;i++){
      now = i;
      VertexSet v = new VertexSet(new int[]{i});
      VertexSet left = bag.graph.neighborSet(v);
      CutDivide cd = decomposeWithSmallCuts(bag,v,new VertexSet(),left);
      if(cd != null){
        Bag nest1 = bag.addNestedBag(cd.c1);
        nest1.addIncidentSeparator(cd.sep);
        cd.sep.addIncidentBag(nest1);

        Bag nest2 = bag.addNestedBag(cd.c2);
        nest2.addIncidentSeparator(cd.sep);
        cd.sep.addIncidentBag(nest2);

        return new NextBag(nest2,start);
      }
      else{
        start++;
      }
    }
    return null;
  }

  private CutDivide decomposeWithSmallCuts(Bag bag,VertexSet comp,VertexSet cand,VertexSet left){
    int addSize = comp.cardinality() + left.cardinality();
    int candSize = cand.cardinality();
    if(addSize > compSize || bag.graph.n <= (addSize + candSize)){
      return null;
    }
    if(left.isEmpty()){
      bag.initializeForDecomposition();
      Separator sep = bag.addSeparator(cand);
      sep.figureOutSafetyBySPT();
      if(sep.safe){
        VertexSet big = bag.graph.all.clone();
        big.andNot(comp);
        comp.or(cand);
        return new CutDivide(sep,comp,big);
      }
      else{
        if(bag == whole){
          bag.nestedBags.clear();
          bag.separators.remove(sep);
        }
        else{
          bag.nestedBags = null;
          bag.separators = null;
        }
      }
      return null;
    }

    int next = left.nextSetBit(0);
    if(next == -1){
      return null;
    }
    if(candSize < cu){
      cand.set(next);
      left.clear(next);
      CutDivide cd = decomposeWithSmallCuts(bag,comp,cand,left);
      if(cd != null){
        return cd;
      }
      cand.clear(next);
      left.set(next);
    }
    if(next < now){
      return null;
    }

    comp.set(next);
    left = bag.graph.neighborSet(comp);
    left = left.subtract(cand);
    CutDivide cd = decomposeWithSmallCuts(bag,comp,cand,left);
    if(cd != null){
      return cd;
    }
    return null;
  }

  private void decomposeWithTwoCuts(){
    if(whole.nestedBags != null && !whole.nestedBags.isEmpty()){
      for(Bag nb : whole.nestedBags){
        nb.makeLocalGraph();
        decomposeWithTwoCuts(nb);
      }
    }
    else{
      decomposeWithTwoCuts(whole);
    }

    if(DEBUG){
      comment("decomposed with 2-cuts");
    }
  }

  // implemented by makii
  private void decomposeWithTwoCuts(Bag parent){
    ArrayList<VertexSet> art = new ArrayList<VertexSet>();
    Graph lg = parent.graph;
    if(lg.n <= 1){
      return;
    }
    for(int i=0;i<lg.n;i++){
      VertexSet vs = new VertexSet(lg.n);
      vs.set(i);
      BitSet almostAll = new BitSet(lg.n);
      almostAll.set(0,lg.n);
      almostAll.clear(i);
      VertexSet twoArt = lg.articulations(almostAll);
      for(int j=twoArt.nextSetBit(i+1);j!=-1;j=twoArt.nextSetBit(j+1)){
        VertexSet twoVs = vs.clone();
        twoVs.set(j);
        art.add(twoVs);
      }
    }

    if(art.size() == 0){
      parent.validate();
      return;
    }

    if(DEBUG){
      comment("detected 2-cuts");
    }

    parent.initializeForDecomposition();

    VertexSet sep = art.get(0);
    ArrayList<VertexSet> comp = lg.getComponents(sep);
    Separator s = parent.addSeparator(sep);
    s.safe = true;

    art.remove(0);

    for(VertexSet ver:comp){
      ver.or(sep);
      Bag b = parent.addNestedBag(ver);
      b.initializeForDecomposition();
      b.addIncidentSeparator(s);
      s.addIncidentBag(b);
      b.makeLocalGraph();
      b.validate();
      ArrayList<VertexSet> nextart = new ArrayList<VertexSet>();
      for(VertexSet oldart:art){
        if(oldart.isSubset(ver)){
          VertexSet na = new VertexSet();
          for(int i=oldart.nextSetBit(0);i!=-1;i=oldart.nextSetBit(i+1)){
            na.set(b.conv[i]);
          }
          nextart.add(na);
        }
      }
      decomposeWithTwoCuts(b,nextart);
    }
  }

  // implemented by makii
  private void decomposeWithTwoCuts(Bag parent,ArrayList<VertexSet> art){
    if(art.size() == 0){
      if(DEBUG){
        parent.validate();
      }
      parent.nestedBags = null;
      parent.separators = null;
      return;
    }

    VertexSet sep = art.get(0);
    ArrayList<VertexSet> comp = parent.graph.getComponents(sep);
    Separator s = parent.addSeparator(sep);
    s.safe = true;

    art.remove(0);

    for(VertexSet ver:comp){
      ver.or(sep);;
      Bag b = parent.addNestedBag(ver);
      b.initializeForDecomposition();
      b.addIncidentSeparator(s);
      s.addIncidentBag(b);
      b.makeLocalGraph();
      ArrayList<VertexSet> nextart = new ArrayList<VertexSet>();
      for(VertexSet oldart:art){
        if(oldart.isSubset(ver)){
          VertexSet na = new VertexSet();
          for(int i=oldart.nextSetBit(0);i!=-1;i=oldart.nextSetBit(i+1)){
            na.set(b.conv[i]);
          }
          nextart.add(na);
        }
      }
      decomposeWithTwoCuts(b,nextart);
    }
  }



  static private void printTreeWidth(Bag b){
    endTime = System.currentTimeMillis();
    System.out.print("," + b.width + "," + (endTime-startTime));
  }

  static long startTime;
  static long endTime;

  public static void main(String[] args){
    Graph graph = Graph.readGraph(System.in);

    Bag whole = new Bag(graph);

    if(true){
      startTime = System.currentTimeMillis();
    }

    CutDecomposer mtd = new CutDecomposer(whole);
    mtd.decompose();

    System.out.println(whole.width);
    if(true){
      printTreeWidth(whole);
      System.out.println();
    }

  }
}
