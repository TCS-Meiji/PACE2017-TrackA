/*
 * Copyright (c) 2017, Keitaro Makii and Hiromu Ohtsuka
*/

package tw.heuristic;

import java.util.ArrayList;
import java.util.BitSet;

public class CutDecomposer{
  public static final int LN = 2000;
  public static final int HN = 100000;
  public static final int HM = 1000000;
  public static final int ONET = 400000;
  public static final int STEP = 1000;
  public static final long DEFAULTMAXSTEP = 500000;
  public static int now;
  public static int cu;
  public static int compSize;
  public static long count;
  public static boolean abort;
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
    decompose(DEFAULTMAXSTEP);
  }

  public boolean decompose(long timeMS){
    abort = false;
    count = 0;
    if(whole.graph.n > ONET){
      return true;
    }

    decomposeWithOneCuts();
    if(getTimeMS() > timeMS){
      whole.flatten();
      whole.setWidth();
      abort = true;
      return false;
    }
    whole.flatten();

    if(whole.graph.n <=  LN){
      decomposeWithTwoCuts();
      if(getTimeMS() > timeMS){
        whole.flatten();
        whole.setWidth();
        abort = true;
        return false;
      }
    }
    else if(whole.graph.n <= HN  && whole.graph.numberOfEdges() <= HM){
      if(!decomposeWithSmallCuts(2,timeMS)){
        whole.flatten();
        whole.setWidth();
        abort = true;
        return false;
      }
    }

    if(whole.graph.n <= 30000){
      whole.flatten();
      if(!decomposeWithSmallCuts(3,timeMS)){
        whole.flatten();
        whole.setWidth();
        abort = true;
        return false;
      }
    }
    if(whole.graph.n <= 20000){
      whole.flatten();
      if(!decomposeWithSmallCuts(4,timeMS)){
        whole.flatten();
        whole.setWidth();
        abort = true;
        return false;
      }
    }


    whole.flatten();
    whole.setWidth();

    return true;
  }

  private static void comment(String comment){
    System.out.println("c " + comment);
  }

  private void decomposeWithOneCuts(){
    VertexSet articulationSet = new VertexSet();
    ArrayList< VertexSet > bcc =
      whole.graph.getBiconnectedComponents(articulationSet);

    count += (whole.graph.n + whole.graph.numberOfEdges());

    if(articulationSet.isEmpty()){
      return;
    }

    if(DEBUG){
      comment("detected 1-cuts");
    }

    whole.initializeForDecomposition();

    for(int a = articulationSet.nextSetBit(0);
      a >= 0; a = articulationSet.nextSetBit(a + 1)){
      count++;
      Separator s = whole.addSeparator(new VertexSet(new int[]{a}));
      s.safe = true;
    }

    for(VertexSet bc : bcc){
      count++;
      whole.addNestedBag(bc);
    }

    for(Separator s : whole.separators){
      for(Bag b : whole.nestedBags){
        count++;
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

    return;
  }

  private boolean decomposeWithSmallCuts(int c,long timeMS){
    if(whole.nestedBags != null && !whole.nestedBags.isEmpty()){
      for(Bag nb : whole.nestedBags){
        if(!decomposeWithSmallCuts(nb,c,timeMS)){
          return false;
        }
      }
    }
    else{
      if(!decomposeWithSmallCuts(whole,c,timeMS)){
        return false;
      }
    }
    if(DEBUG){
      comment("decompose with small-cuts");
    }
    return true;
  }

  private boolean decomposeWithSmallCuts(Bag bag,int c,long timeMS){
    if(bag != whole){
      bag.makeLocalGraph();
      count += bag.graph.n * (Math.log(bag.graph.n)+1) + bag.graph.numberOfEdges() * 1.2;
    }
    Graph lg = bag.graph;

    cu = c;
    compSize = 6+cu;

    NextBag nb = new NextBag(bag,0);

    while(true){
      nb = decomposeWithSmallCuts(nb.bag,nb.start,lg.n);
      if(getTimeMS() > timeMS){
        return false;
      }
      if (nb == null){
        return true;
      }
      nb.bag.makeLocalGraph();
      lg = nb.bag.graph;
      count += nb.bag.graph.n * (Math.log(nb.bag.graph.n)+1) + nb.bag.graph.numberOfEdges() * 1.2;

      compSize = 6+cu;
    }
  }

  private NextBag decomposeWithSmallCuts(Bag bag,int start,int end){
    for(int i=start;i<end;i++){
      count++;
      now = i;
      VertexSet v = new VertexSet(new int[]{i});
      VertexSet left = bag.graph.neighborSet(v);
      count += Math.log(bag.graph.n);
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
    count += addSize + candSize;
    if(addSize > compSize || bag.graph.n <= (addSize + candSize)){
      return null;
    }
    if(left.isEmpty()){
      bag.initializeForDecomposition();
      Separator sep = bag.addSeparator(cand);
      sep.figureOutSafetyBySPT();
      count += sep.getSteps() + bag.graph.n / 15;
      if(sep.safe){
        count += bag.graph.n;
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
      count++;
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

    count++;
    comp.set(next);
    left = bag.graph.neighborSet(comp);
    left = left.subtract(cand);
    count += (bag.graph.n / (Math.log(bag.graph.n)+1));
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
        count += nb.graph.n;
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

  private void decomposeWithTwoCuts(Bag parent){
    ArrayList<VertexSet> art = new ArrayList<VertexSet>();
    Graph lg = parent.graph;
    if(lg.n <= 1){
      return;
    }
//    count += lg.n * Math.log(lg.n) + lg.numberOfEdges();
    count += lg.n * lg.n / Math.log(lg.n) + lg.numberOfEdges();
    for(int i=0;i<lg.n;i++){
      count++;
      VertexSet vs = new VertexSet(lg.n);
      vs.set(i);
      BitSet almostAll = new BitSet(lg.n);
      almostAll.set(0,lg.n);
      almostAll.clear(i);
      VertexSet twoArt = lg.articulations(almostAll);
//      count += lg.n + lg.numberOfEdges();
      for(int j=twoArt.nextSetBit(i+1);j!=-1;j=twoArt.nextSetBit(j+1)){
        count++;
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
    count += lg.n;

    art.remove(0);

    for(VertexSet ver:comp){
      ver.or(sep);
      Bag b = parent.addNestedBag(ver);
      b.initializeForDecomposition();
      b.addIncidentSeparator(s);
      s.addIncidentBag(b);
      b.makeLocalGraph();

      ArrayList<VertexSet> nextart = new ArrayList<VertexSet>();
      for(VertexSet oldart:art){
        count++;
        if(oldart.isSubset(ver)){
          count++;
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

  private void decomposeWithTwoCuts(Bag parent,ArrayList<VertexSet> art){
    if(art.size() == 0){
      count++;
      if(DEBUG){
        parent.validate();
      }
      parent.nestedBags = null;
      parent.separators = null;
      return;
    }

    VertexSet sep = art.get(0);
    ArrayList<VertexSet> comp = parent.graph.getComponents(sep);
    count += parent.graph.n;
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
//      count += Math.log(parent.graph.n);
      ArrayList<VertexSet> nextart = new ArrayList<VertexSet>();
      for(VertexSet oldart:art){
        count++;
        if(oldart.isSubset(ver)){
          count++;
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

  public long getTimeMS(){
    return count/1000;
  }

  public boolean isAborted(){
    return abort;
  }

  public static void main(String[] args){

  }
}
