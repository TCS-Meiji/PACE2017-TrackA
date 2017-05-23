/*
 * Copyright (c) 2017, Hiromu Ohtsuka
*/

package tw.heuristic;

public class VertexSet
implements Comparable< VertexSet >, Cloneable{
  private int TH1 = 256;
  public static enum Type{
    ARRAYSET, XBITSET
  };
  private XBitSet xbitset;
  private ArraySet arrayset;
  private Type type = Type.ARRAYSET;

  public VertexSet(){
    arrayset = new ArraySet();
  }

  public VertexSet(int n){
    this();
    TH1 = n / 100;
  }

  public VertexSet(int n, int[] a){
    TH1 = n / 100;
    if(a.length <= TH1){
      arrayset = new ArraySet(a);
    }
    else{
      type = Type.XBITSET;
      xbitset = new XBitSet(a);
    }
  }

  public VertexSet(int[] a){
    if(a.length <= TH1){
      arrayset = new ArraySet(a);
    }
    else{
      type = Type.XBITSET;
      xbitset = new XBitSet(a);
    }
  }

  private VertexSet(ArraySet as){
    arrayset = as;
    ensureType();
  }

  private VertexSet(XBitSet xbs){
    xbitset = xbs;
    type = Type.XBITSET;
    ensureType();
  }

  private void toArraySet(){
    if(type == Type.ARRAYSET){
      return;
    }
    arrayset = arraySetOf(xbitset);
    type = Type.ARRAYSET;
    xbitset = null;
  }

  private void toXBitSet(){
    if(type == Type.XBITSET){
      return;
    }
    xbitset = xBitSetOf(arrayset);
    type = Type.XBITSET;
    arrayset = null;
  }

  private static XBitSet xBitSetOf(ArraySet as){
    return new XBitSet(as.toArray());
  }

  private static ArraySet arraySetOf(XBitSet xbs){
    return new ArraySet(xbs.toArray());
  }

  private void ensureType(){
    int size = (type == Type.ARRAYSET) ?
      arrayset.cardinality() : xbitset.cardinality();
    if(size <= TH1){
      toArraySet();
    }
    else{
      toXBitSet();
    }
  }

  public void and(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      arrayset.and(set.arrayset);
      ensureType();
      return;
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      xbitset.and(set.xbitset);
      ensureType();
      return;
    }
    if(type == Type.ARRAYSET){
      toXBitSet();
    }
    else{
      set.toXBitSet();
    }
    xbitset.and(set.xbitset);
    set.ensureType();
    ensureType();
  }

  public void andNot(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      arrayset.andNot(set.arrayset);
      ensureType();
      return;
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      xbitset.andNot(set.xbitset);
      ensureType();
      return;
    }
    if(type == Type.ARRAYSET){
      toXBitSet();
    }
    else{
      set.toXBitSet();
    }
    xbitset.andNot(set.xbitset);
    set.ensureType();
    ensureType();
  }

  public int cardinality(){
    if(type == Type.ARRAYSET){
      return arrayset.cardinality();
    }
    else{
      return xbitset.cardinality();
    }
  }

  public void clear(){
    if(type == Type.ARRAYSET){
      arrayset.clear();
    }
    else{
      type = Type.ARRAYSET;
      xbitset = null;
      arrayset = new ArraySet();
    }
  }

  public void clear(int i){
    if(type == Type.ARRAYSET){
      arrayset.clear(i);
    }
    else{
      xbitset.clear(i);
    }
    ensureType();
  }

  public void clear(int fromIndex, int toIndex){
    if(type == Type.ARRAYSET){
      arrayset.clear(fromIndex, toIndex);
    }
    else{
      xbitset.clear(fromIndex, toIndex);
    }
    ensureType();
  }

  @Override
    public VertexSet clone(){
      try{
        VertexSet result = (VertexSet)super.clone();
        if(type == Type.ARRAYSET){
          result.arrayset = (ArraySet)arrayset.clone();
        }
        else{
          result.xbitset = (XBitSet)xbitset.clone();
        }
        return result;
      }
      catch(CloneNotSupportedException e){
        throw new AssertionError();
      }
    }

  @Override
    public boolean equals(Object obj){
      if(!(obj instanceof VertexSet)){
        return false;
      }
      VertexSet vs = (VertexSet)obj;
      if(type == Type.ARRAYSET && vs.type == Type.ARRAYSET){
        return arrayset.equals(vs.arrayset);
      }
      if(type == Type.XBITSET && vs.type == Type.XBITSET){
        return xbitset.equals(vs.xbitset);
      }
      if(type == Type.ARRAYSET){
        return xBitSetOf(arrayset).equals(vs.xbitset);
      }
      else{
        return xbitset.equals(xBitSetOf(vs.arrayset));
      }
    }

  public void flip(int i){
    if(type == Type.ARRAYSET){
      arrayset.flip(i);
    }
    else{
      xbitset.flip(i);
    }
    ensureType();
  }

  public void flip(int fromIndex, int toIndex){
    if(type == Type.ARRAYSET){
      arrayset.flip(fromIndex, toIndex);
    }
    else{
      xbitset.flip(fromIndex, toIndex);
    }
    ensureType();
  }

  public boolean get(int i){
    if(type == Type.ARRAYSET){
      return arrayset.get(i);
    }
    else{
      return xbitset.get(i);
    }
  }

  public VertexSet get(int fromIndex, int toIndex){
    throw new UnsupportedOperationException();
  }

  @Override
    public int hashCode(){
      int hash = 1;
      if(type == Type.ARRAYSET){
        for(int i = 0; i < arrayset.size; i++){
          hash = 31 * hash + arrayset.a[i];
        }
      }
      else{
        for(int i = xbitset.nextSetBit(0);
          i >= 0; i = xbitset.nextSetBit(i + 1)){
          hash = 31 * hash + i;
        }
      }
      return hash;
    }

  public boolean hasSmaller(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return arrayset.hasSmaller(set.arrayset);
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return xbitset.hasSmaller(set.xbitset);
    }
    if(type == Type.ARRAYSET){
      return xBitSetOf(arrayset).hasSmaller(set.xbitset);
    }
    else{
      return xbitset.hasSmaller(xBitSetOf(set.arrayset));
    }
  }

  public boolean hasSmallerVertexThan(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return arrayset.hasSmallerVertexThan(set.arrayset);
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return xbitset.hasSmallerVertexThan(set.xbitset);
    }
    if(type == Type.ARRAYSET){
      return xBitSetOf(arrayset).hasSmallerVertexThan(set.xbitset);
    }
    else{
      return xbitset.hasSmallerVertexThan(xBitSetOf(set.arrayset));
    }
  }

  public boolean intersects(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return arrayset.intersects(set.arrayset);
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return xbitset.intersects(set.xbitset);
    }
    if(type == Type.ARRAYSET){
      return xBitSetOf(arrayset).intersects(set.xbitset);
    }
    else{
      return xbitset.intersects(xBitSetOf(set.arrayset));
    }
  }

  public VertexSet intersectWith(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return new VertexSet(arrayset.intersectWith(set.arrayset));
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return new VertexSet(xbitset.intersectWith(set.xbitset));
    }
    if(type == Type.ARRAYSET){
      return new VertexSet(xBitSetOf(arrayset).intersectWith(set.xbitset));
    }
    else{
      return new VertexSet(xbitset.intersectWith(xBitSetOf(set.arrayset)));
    }
  }

  public boolean isSubset(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return arrayset.isSubset(set.arrayset);
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return xbitset.isSubset(set.xbitset);
    }
    if(type == Type.ARRAYSET){
      return xBitSetOf(arrayset).isSubset(set.xbitset);
    }
    else{
      return xbitset.isSubset(xBitSetOf(set.arrayset));
    }
  }

  public boolean isDisjoint(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return arrayset.isDisjoint(set.arrayset);
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return xbitset.isDisjoint(set.xbitset);
    }
    if(type == Type.ARRAYSET){
      return xBitSetOf(arrayset).isDisjoint(set.xbitset);
    }
    else{
      return xbitset.isDisjoint(xBitSetOf(set.arrayset));
    }
  }

  public boolean isEmpty(){
    if(type == Type.ARRAYSET){
      return arrayset.isEmpty();
    }
    else{
      return xbitset.isEmpty();
    }
  }

  public boolean isSuperset(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return arrayset.isSuperset(set.arrayset);
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return xbitset.isSuperset(set.xbitset);
    }
    if(type == Type.ARRAYSET){
      return xBitSetOf(arrayset).isSuperset(set.xbitset);
    }
    else{
      return xbitset.isSuperset(xBitSetOf(set.arrayset));
    }
  }

  public int length(){
    if(type == Type.ARRAYSET){
      return arrayset.length();
    }
    else{
      return xbitset.length();
    }
  }

  public int nextClearBit(int fromIndex){
    if(type == Type.ARRAYSET){
      return arrayset.nextClearBit(fromIndex);
    }
    else{
      return xbitset.nextClearBit(fromIndex);
    }
  }

  public int nextSetBit(int fromIndex){
    if(type == Type.ARRAYSET){
      return arrayset.nextSetBit(fromIndex);
    }
    else{
      return xbitset.nextSetBit(fromIndex);
    }
  }

  public void or(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      arrayset.or(set.arrayset);
      ensureType();
      return;
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      xbitset.or(set.xbitset);
      ensureType();
      return;
    }
    if(type == Type.ARRAYSET){
      toXBitSet();
    }
    else{
      set.toXBitSet();
    }
    xbitset.or(set.xbitset);
    set.ensureType();
    ensureType();
  }

  public int previousClearBit(int fromIndex){
    throw new UnsupportedOperationException();
  }

  public int previousSetBit(int fromIndex){
    throw new UnsupportedOperationException();
  }

  public void set(int i){
    if(type == Type.ARRAYSET){
      arrayset.set(i);
    }
    else{
      xbitset.set(i);
    }
    ensureType();
  }

  public void set(int i, boolean value){
    if(type == Type.ARRAYSET){
      arrayset.set(i, value);
    }
    else{
      xbitset.set(i, value);
    }
    ensureType();
  }

  public void set(int fromIndex, int toIndex){
    if(type == Type.ARRAYSET){
      arrayset.set(fromIndex, toIndex);
    }
    else{
      xbitset.set(fromIndex, toIndex);
    }
    ensureType();
  }

  public void set(int fromIndex, int toIndex, boolean value){
    if(type == Type.ARRAYSET){
      arrayset.set(fromIndex, toIndex, value);
    }
    else{
      xbitset.set(fromIndex, toIndex, value);
    }
    ensureType();
  }

  public int size(){
    throw new UnsupportedOperationException();
  }

  public VertexSet subtract(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return new VertexSet(arrayset.subtract(set.arrayset));
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return new VertexSet(xbitset.subtract(set.xbitset));
    }
    if(type == Type.ARRAYSET){
      return new VertexSet(xBitSetOf(arrayset).subtract(set.xbitset));
    }
    else{
      return new VertexSet(xbitset.subtract(xBitSetOf(set.arrayset)));
    }
  }

  public int[] toArray(){
    if(type == Type.ARRAYSET){
      return arrayset.toArray();
    }
    else{
      return xbitset.toArray();
    }
  }

  public byte[] toByteArray(){
    if(type == Type.ARRAYSET){
      return arrayset.toByteArray();
    }
    else{
      return xbitset.toByteArray();
    }
  }

  public long[] toLongArray(){
    if(type == Type.ARRAYSET){
      return arrayset.toLongArray();
    }
    else{
      return xbitset.toLongArray();
    }
  }

  @Override
    public String toString(){
      if(type == Type.ARRAYSET){
        return arrayset.toString();
      }
      else{
        return xbitset.toString();
      }
    }

  public VertexSet unionWith(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      return new VertexSet(arrayset.unionWith(set.arrayset));
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      return new VertexSet(xbitset.unionWith(set.xbitset));
    }
    if(type == Type.ARRAYSET){
      return new VertexSet(xBitSetOf(arrayset).unionWith(set.xbitset));
    }
    else{
      return new VertexSet(xbitset.unionWith(xBitSetOf(set.arrayset)));
    }
  }

  public static VertexSet valueOf(byte[] bytes){
    throw new UnsupportedOperationException();
  }

  public static VertexSet valueOf(long[] longs){
    throw new UnsupportedOperationException();
  }

  public void xor(VertexSet set){
    if(type == Type.ARRAYSET && set.type == Type.ARRAYSET){
      arrayset.xor(set.arrayset);
      ensureType();
      return;
    }
    if(type == Type.XBITSET && set.type == Type.XBITSET){
      xbitset.xor(set.xbitset);
      ensureType();
      return;
    }
    if(type == Type.ARRAYSET){
      toXBitSet();
    }
    else{
      set.toXBitSet();
    }
    xbitset.xor(set.xbitset);
    set.ensureType();
    ensureType();
  }

  @Override
    public int compareTo(VertexSet vs){
      if(type == Type.ARRAYSET && vs.type == Type.ARRAYSET){
        return arrayset.compareTo(vs.arrayset);
      }
      if(type == Type.XBITSET && vs.type == Type.XBITSET){
        return xbitset.compareTo(vs.xbitset);
      }
      if(type == Type.ARRAYSET){
        return xBitSetOf(arrayset).compareTo(vs.xbitset);
      }
      else{
        return xbitset.compareTo(xBitSetOf(vs.arrayset));
      }
    }

  public void checkTypeValidity(){
    if(type == Type.ARRAYSET){
      assert(arrayset != null);
      assert(xbitset == null);
      assert(arrayset.cardinality() <= TH1);
    }
    else{
      assert(xbitset != null);
      assert(arrayset == null);
      assert(xbitset.cardinality() > TH1);
    }
  }
}
