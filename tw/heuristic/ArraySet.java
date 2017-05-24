/*
 * Copyright (c) 2017, Hiromu Ohtsuka
*/

package tw.heuristic;

import java.util.Arrays;
import java.util.Comparator;

public class ArraySet
implements Comparable< ArraySet >, Cloneable{
  public static final int DEFAULT_INITIAL_CAPACITY = 64;
  int size;
  int[] a;
  int hash = 1;

  int index0;

  public ArraySet(){
    this(DEFAULT_INITIAL_CAPACITY);
  }

  public ArraySet(int[] a){
    this.size = a.length;
    this.a = Arrays.copyOf(a, a.length);
    Arrays.sort(this.a);
    rehash();
  }

  public ArraySet(int initialCapacity){
    this.a = new int[initialCapacity];
    rehash();
  }

  public ArraySet(int initialCapacity, int[] a){
    this(initialCapacity);
    for(int i = 0; i < a.length; i++){
      this.a[i] = a[i];
    }
    Arrays.sort(this.a, 0, a.length);
    rehash();
  }

  public boolean isSubset(ArraySet set){
    int i = 0, j = 0;
    while(i < size && j < set.size){
      if(a[i] < set.a[j]){
        return false;
      }
      else if(a[i] > set.a[j]){
        ++j;
      }
      else{
        ++i;  ++j;
      }
    }
    return i == size;
  }

  public boolean isDisjoint(ArraySet set){
    return !intersects(set);
  }

  public boolean intersects(ArraySet set){
    int i = 0, j = 0;
    while(i < size && j < set.size){
      if(a[i] < set.a[j]){
        ++i;
      }
      else if(a[i] > set.a[j]){
        ++j;
      }
      else{
        return true;
      }
    }
    return false;
  }

  public boolean isSuperset(ArraySet set){
    return set.isSubset(this);
  }

  public ArraySet unionWith(ArraySet set){
    int i = 0, j = 0, k = 0;
    while(i < size && j < set.size){
      if(a[i] < set.a[j]){
        ++i;
      }
      else if(a[i] > set.a[j]){
        ++j;
      }
      else{
        ++k; ++i; ++j;
      }
    }

    int[] result = new int[size + set.size - k];
    i = j = k = 0;
    while(i < size && j < set.size){
      if(a[i] < set.a[j]){
        result[k++] = a[i++];
      }
      else if(a[i] > set.a[j]){
        result[k++] = set.a[j++];
      }
      else{
        result[k++] = a[i];
        ++i; ++j;
      }
    }
    while(i < size){
      result[k++] = a[i++];
    }
    while(j < set.size){
      result[k++] = set.a[j++];
    }

    return new ArraySet(result);
  }

  public ArraySet intersectWith(ArraySet set){
    int i = 0, j = 0, k = 0;
    while(i < size && j < set.size){
      if(a[i] < set.a[j]){
        ++i;
      }
      else if(a[i] > set.a[j]){
        ++j;
      }
      else{
        ++i;  ++j;
        ++k;
      }
    }

    int[] result = new int[k];
    i = j = k = 0;
    while(i < size && j < set.size){
      if(a[i] < set.a[j]){
        ++i;
      }
      else if(a[i] > set.a[j]){
        ++j;
      }
      else{
        result[k++] = a[i];
        ++i;  ++j;
      }
    }

    return new ArraySet(result);
  }

  public ArraySet subtract(ArraySet set){
    ArraySet result = (ArraySet)this.clone();
    result.andNot(set);
    return result;
  }

  public boolean hasSmaller(ArraySet set){
    return a[0] < set.a[0];
  }

  public int[] toArray(){
    return Arrays.copyOf(a, size);
  }

  public boolean hasSmallerVertexThan(ArraySet set){
    if(isEmpty()){
      return false;
    }
    if(set.isEmpty()){
      return true;
    }
    return a[0] < set.a[0];
  }

  public int cardinality(){
    return size;
  }

  public void and(ArraySet set){
    int i = 0, j = 0, k = 0;
    int[] cpa = Arrays.copyOf(a, size);
    int cpsize = size;

    clear();

    while(i < cpsize && j < set.size){
      if(cpa[i] < set.a[j]){
        ++i;
      }
      else if(cpa[i] > set.a[j]){
        ++j;
      }
      else{
        a[size++] = cpa[i];
        ++i; ++j;
      }
    }

    rehash();
  }

  public void andNot(ArraySet set){
    int i = 0, j = 0, k = 0;
    int[] cpa = Arrays.copyOf(a, size);
    int cpsize = size;

    clear();

    while(i < cpsize && j < set.size){
      if(cpa[i] < set.a[j]){
        a[size++] = cpa[i];
        ++i;
      }
      else if(cpa[i] > set.a[j]){
        ++j;
      }
      else{
        ++i;  ++j;  ++k;
      }
    }
    while(i < cpsize){
      a[size++] = cpa[i++];
    }

    rehash();
  }

  public void clear(){
    size = 0;
    rehash();
  }

  public void clear(int i){
    int j = Arrays.binarySearch(a, 0, size, i);
    if(j >= 0){
      for(int k = j; k + 1 < size; k++){
        a[k] = a[k + 1];
      }
      --size;
      rehash();
    }
  }

  public void clear(int fromIndex, int toIndex){
    for(int i = fromIndex; i < toIndex; i++){
      clear(i);
    }
  }

  public void flip(int i){
    set(i, !get(i));
  }

  public void flip(int fromIndex, int toIndex){
    for(int i = fromIndex; i < toIndex; i++){
      flip(i);
    }
  }

  public boolean get(int i){
    return Arrays.binarySearch(a, 0, size, i) >= 0;
  }

  private int insertionPointOf(int i){
    int j = Arrays.binarySearch(a, 0, size, i);
    if(j >= 0){
      return -1;
    }
    return -j - 1;
  }

  public ArraySet get(int fromIndex, int toIndex){
    throw new UnsupportedOperationException();
  }

  @Override
    public int hashCode(){
      int seed = 1234;
      return seed ^ hash;
    }

  private void rehash(){
    hash = 1;
    for(int i = 0; i < size; i++){
      hash = 31 * hash + a[i];
    }
  }

  public int length(){
    if(isEmpty()){
      return 0;
    }
    return a[size - 1] + 1;
  }

  public int nextClearBit(int fromIndex){
    int lb = lowerBound(fromIndex);
    if(lb == size || a[lb] > fromIndex){
      return fromIndex;
    }
    return nextClearBit(fromIndex + 1);
  }

  public int nextSetBit(int fromIndex){
    /*
       if(isEmpty()){
       return -1;
       }
       int lb = lowerBound(fromIndex);
       if(lb == size){
       return -1;
       }
       return a[lb];
     */
    if(isEmpty() || (fromIndex > a[size - 1])){
      index0 = 0;
      return -1;
    }
    if(index0 + 1 < size && 
        (fromIndex > a[index0] && fromIndex <= a[index0 + 1])){
      return a[++index0];
    }
    else{
      index0 = lowerBound(fromIndex);
      return a[index0];
    }
  }

  private int lowerBound(int i){
    int j = Arrays.binarySearch(a, 0, size, i);
    if(j >= 0){
      return j;
    }
    return -j - 1;
  }

  public void or(ArraySet set){
    int[] cpa = Arrays.copyOf(a, size);
    int cpsize = size;

    clear();

    int i = 0, j = 0;
    while(i < cpsize && j < set.size){
      ensureCapasity();
      if(cpa[i] < set.a[j]){
        a[size++] = cpa[i++];
      }
      else if(cpa[i] > set.a[j]){
        a[size++] = set.a[j++];
      }
      else{
        a[size++] = cpa[i];
        ++i; ++j;
      }
    }
    while(i < cpsize){
      ensureCapasity();
      a[size++] = cpa[i++];
    }
    while(j < set.size){
      ensureCapasity();
      a[size++] = set.a[j++];
    }

    rehash();
  }

  public int previousClearBit(int fromIndex){
    throw new UnsupportedOperationException();
  }

  public int previousSetBit(int fromIndex){
    throw new UnsupportedOperationException();
  }

  public void set(int i){
    int j = insertionPointOf(i);
    if(j >= 0){
      ensureCapasity();
      for(int k = size; k - 1 >= j; k--){
        a[k] = a[k - 1];
      }
      a[j] = i;
      ++size;
      rehash();
    }
  }

  public void set(int i, boolean value){
    if(value){
      set(i);
    }
    else{
      clear(i);
    }
  }

  public void set(int fromIndex, int toIndex){
    for(int i = fromIndex; i < toIndex; i++){
      set(i);
    }
  }

  public void set(int fromIndex, int toIndex, boolean value){
    for(int i = fromIndex; i < toIndex; i++){
      set(i, value);
    }
  }

  public int size(){
    throw new UnsupportedOperationException();
  }

  @Override
    public String toString(){
      StringBuilder sb = new StringBuilder();
      sb.append("{");
      for(int i = 0; i < size; i++){
        sb.append(a[i]);
        if(i != size - 1){
          sb.append(", ");
        }
      }
      sb.append("}");
      return sb.toString();
    }

  public void xor(ArraySet set){
    int i = 0, j = 0;
    int[] cpa = Arrays.copyOf(a, size);
    int cpsize = size;

    clear();

    while(i < cpsize && j < set.size){
      ensureCapasity();
      if(cpa[i] < set.a[j]){
        a[size++] = cpa[i++];
      }
      else if(cpa[i] > set.a[j]){
        a[size++] = set.a[j++];
      }
      else{
        ++i;  ++j;
      }
    }
    while(i < cpsize){
      ensureCapasity();
      a[size++] = cpa[i++];
    }
    while(j < set.size){
      ensureCapasity();
      a[size++] = set.a[j++];
    }

    rehash();
  }

  public boolean isEmpty(){
    return size == 0;
  }

  @Override
    public int compareTo(ArraySet set){
      if(isEmpty() || set.isEmpty()){
        if(isEmpty() && !set.isEmpty()){
          return -1;
        }
        else if(!isEmpty() && set.isEmpty()){
          return 1;
        }
        else{
          return 0;
        }
      }

      int i = size - 1, j = set.size - 1;
      while(i >= 0 && j >= 0){
        if(a[i] < set.a[j]){
          return -1;
        }
        else if(a[i] > set.a[j]){
          return 1;
        }
      }

      return 0;
    }

  @Override
    public boolean equals(Object obj){
      if(!(obj instanceof ArraySet)){
        return false;
      }
      ArraySet set = (ArraySet)obj;
      if(size != set.size){
        return false;
      }
      return size == set.size &&
        equals(a, set.a, 0, size);
    }

  private void ensureCapasity(){
    if(a.length == size){
      a = Arrays.copyOf(a, 2 * size + 1);
    }
  }

  private static boolean equals(
      int[] a1, int[] a2, int fromIndex, int toIndex){
    for(int i = fromIndex; i < toIndex; i++){
      if(a1[i] != a2[i]){
        return false;
      }
    }
    return true;
  }

  @Override
    public ArraySet clone(){
      try{
        ArraySet result = (ArraySet)super.clone();
        result.a = Arrays.copyOf(a, a.length);
        return result;
      }
      catch(CloneNotSupportedException e){
        throw new AssertionError();
      }
    }

  public byte[] toByteArray(){
    if(isEmpty()){
      return new byte[0];
    }

    byte[] result = new byte[a[size - 1] / 8 + 1];
    for(int i = 0; i < size; i++){
      result[a[i] / 8] |= 1 << (a[i] % 8);
    }

    return result;
  }

  public long[] toLongArray(){
    if(isEmpty()){
      return new long[0];
    }

    long[] result = new long[a[size - 1] / 64 + 1];
    for(int i = 0; i < size; i++){
      result[a[i] / 64] |= 1L << (a[i] % 64);
    }

    return result;
  }

  public static final Comparator< ArraySet >
    descendingComparator = new Comparator< ArraySet >(){
      @Override
        public int compare(ArraySet set1, ArraySet set2){
          if(set1.isEmpty() || set2.isEmpty()){
            if(set1.isEmpty() && !set2.isEmpty()){
              return -1;
            }
            else if(!set1.isEmpty() && set2.isEmpty()){
              return 1;
            }
            else{
              return 0;
            }
          }

          int i = set1.size - 1, j = set2.size - 1;
          while(i >= 0 && j >= 0){
            if(set1.a[i] < set2.a[j]){
              return -1;
            }
            else if(set1.a[i] > set2.a[j]){
              return 1;
            }
          }

          return 0;
        }
    };

  public static final Comparator< ArraySet >
    ascendingComparator = new Comparator< ArraySet >(){
      @Override
        public int compare(ArraySet set1, ArraySet set2){
          if(set1.isEmpty() || set2.isEmpty()){
            if(set1.isEmpty() && !set2.isEmpty()){
              return -1;
            }
            else if(!set1.isEmpty() && set2.isEmpty()){
              return 1;
            }
            else{
              return 0;
            }
          }

          int i = 0, j = 0;
          while(i < set1.size && j < set2.size){
            if(set1.a[i] < set2.a[j]){
              return 1;
            }
            else if(set1.a[i] > set2.a[j]){
              return -1;
            }
          }

          return Integer.compare(
              set1.a[set1.size - 1], set2.a[set2.size - 1]);
        }
    };

  public static final Comparator< ArraySet >
    cardinalityComparator = new Comparator< ArraySet >(){
      @Override
        public int compare(ArraySet set1, ArraySet set2){
          int c1 = set1.cardinality();
          int c2 = set2.cardinality();
          if(c1 != c2){
            return Integer.compare(c1, c2);
          }
          return ascendingComparator.compare(set1, set2);
        }
    };
}
