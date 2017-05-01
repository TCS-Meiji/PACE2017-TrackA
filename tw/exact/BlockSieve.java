/*
 * Copyright (c) 2017, Hisao Tamaki and Hiromu Otsuka
 */

package tw.exact;

import java.io.PrintStream;

import java.util.ArrayList;
import java.util.Arrays;

public class BlockSieve{
  private static final String spaces64 =
    "                                                                ";
  public static final int MAX_CHILDREN_SIZE = 512;
  private Node root;
  private int n;
  private int last;
  private int targetWidth;
  private int margin;
  private int size;

  private abstract class Node{
    protected int index;
    protected int width;
    protected int ntz;
    protected Node[] children;
    protected XBitSet[] values;
    protected int[] cardinalities;

    protected Node(int index, int width, int ntz){
      this.index = index;
      this.width = width;
      this.ntz = ntz;
    }

    public abstract int indexOf(long label);
    public abstract int add(long label);
    public abstract int size();
    public abstract long getLabelAt(int i);

    public long getMask(){
      return Unsigned.consecutiveOneBit(ntz, ntz + width);
    }

    public int add(long label, Node child){
      int i = add(label);
      if(children != null){
        children = Arrays.copyOf(children, children.length + 1);
        for(int j = children.length - 1; j - 1 >= i; j--){
          children[j] = children[j - 1];
        }
        children[i] = child;
        return i;
      }
      else{
        children = new Node[1];
        children[0] = child;
        return 0;
      }
    }

    public int add(long label, XBitSet value){
      return add(label, value, value.cardinality());
    }

    public int add(long label, XBitSet value, int cardinality){
      int i = add(label);
      if(values != null && cardinalities != null){
        values = Arrays.copyOf(values, values.length + 1);
        for(int j = values.length - 1; j - 1 >= i; j--){
          values[j] = values[j - 1];
        }
        values[i] = value;
        cardinalities =
          Arrays.copyOf(cardinalities, cardinalities.length + 1);
        for(int j = cardinalities.length - 1; j - 1 >= i; j--){
          cardinalities[j] = cardinalities[j - 1];
        }
        cardinalities[i] = cardinality;
        return i;
      }
      else{
        values = new XBitSet[1];
        values[0] = value;
        cardinalities = new int[1];
        cardinalities[0] = cardinality;
        return 0;
      }
    }

    public boolean isLeaf(){
      return index == last && isLastInInterval();
    }

    public boolean isLastInInterval(){
      return ntz + width == 64;
    }

    public abstract void filterSuperblocks(long[] longs, long[] neighbors, 
        int intersects, ArrayList< XBitSet > list);

    public abstract void filterSubblocks(long[] longs, long[] neighbors,
        int intersects, ArrayList< XBitSet > list);

    public abstract void dump(PrintStream ps, String indent);
  }

  private class ByteNode extends Node{
    private byte[] labels;

    public ByteNode(int index, int width, int ntz){
      super(index, width, ntz);
      assert(width <= 8);
      labels = new byte[0];
    }

    @Override
      public int size(){
        return labels.length;
      }

    @Override
      public long getLabelAt(int i){
        return Unsigned.toUnsignedLong(labels[i]) << ntz;
      }

    @Override
      public int indexOf(long label){
        return Unsigned.binarySearch(labels, 
            Unsigned.byteValue((label & getMask()) >>> ntz));
      }

    @Override
      public int add(long label){
        int i = -(indexOf(label)) - 1;
        labels = Arrays.copyOf(labels, labels.length + 1);
        for(int j = labels.length - 1; j - 1 >= i; j--){
          labels[j] = labels[j - 1];
        }
        labels[i] = Unsigned.byteValue((label & getMask()) >>> ntz);
        return i;
      }

    @Override
      public void dump(PrintStream ps, String indent){
        for(int i = 0; i < labels.length; i++){
          ps.println(indent + Long.toBinaryString(labels[i]));
          if(!isLeaf()){
            children[i].dump(ps, indent + spaces64);
          }
        }
      }

    @Override
      public void filterSuperblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list){
        long mask = getMask();
        int bits = 0;
        if(index < longs.length){
          bits = Unsigned.intValue(((longs[index] & mask) >>> ntz));
        }

        int neighb = 0;
        if(index < neighbors.length){
          neighb = Unsigned.intValue((neighbors[index] & mask) >>> ntz);
        }

        if(isLeaf()){
          for(int i = labels.length - 1; i >= 0; i--){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = labels.length - 1; i >= 0; i--){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSuperblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }

    @Override
      public void filterSubblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list) {
        long mask = getMask();
        int bits = 0;
        if(index < longs.length){
          bits = Unsigned.intValue((longs[index] & mask) >>> ntz);
        }

        int neighb = 0;
        if(index < neighbors.length){
          neighb = Unsigned.intValue((neighbors[index] & mask) >>> ntz);
        }

        if(isLeaf()){
          for(int i = 0; i < labels.length; i++){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = 0; i < labels.length; i++){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSubblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }
  }

  private class ShortNode extends Node{
    private short[] labels;

    public ShortNode(int index, int width, int ntz){
      super(index, width, ntz);
      assert(width <= 16);
      labels = new short[0];
    }

    @Override
      public int size(){
        return labels.length;
      }

    @Override
      public long getLabelAt(int i){
        return Unsigned.toUnsignedLong(labels[i]) << ntz;
      }

    @Override
      public int indexOf(long label){
        return Unsigned.binarySearch(labels, 
            Unsigned.shortValue((label & getMask()) >>> ntz));
      }

    @Override
      public int add(long label){
        int i = -(indexOf(label)) - 1;
        labels = Arrays.copyOf(labels, labels.length + 1);
        for(int j = labels.length - 1; j - 1 >= i; j--){
          labels[j] = labels[j - 1];
        }
        labels[i] = Unsigned.shortValue(((label & getMask()) >>> ntz));
        return i;
      }

    @Override
      public void dump(PrintStream ps, String indent){
        for (int i = 0; i < labels.length; i++) {
          ps.println(indent + Long.toBinaryString(labels[i]));
          if (!isLeaf()) {
            children[i].dump(ps, indent + spaces64);
          }
        }
      }

    @Override
      public void filterSuperblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list){
        long mask = getMask();
        int bits = 0;
        if(index < longs.length){
          bits = Unsigned.intValue((longs[index] & mask) >>> ntz);
        }

        int neighb = 0;
        if(index < neighbors.length){
          neighb = Unsigned.intValue((neighbors[index] & mask) >>> ntz);
        }

        if(isLeaf()){
          for(int i = labels.length - 1; i >= 0; i--){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = labels.length - 1; i >= 0; i--){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSuperblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }

    @Override
      public void filterSubblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list) {
        long mask = getMask();
        int bits = 0;
        if(index < longs.length){
          bits = Unsigned.intValue((longs[index] & mask) >>> ntz);
        }

        int neighb = 0;
        if(index < neighbors.length){
          neighb = Unsigned.intValue((neighbors[index] & mask) >>> ntz);
        }

        if(isLeaf()){
          for(int i = 0; i < labels.length; i++){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = 0; i < labels.length; i++){
            int label = Unsigned.toUnsignedInt(labels[i]);
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSubblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }
  }

  private class IntegerNode extends Node{
    private int[] labels;

    public IntegerNode(int index, int width, int ntz){
      super(index, width, ntz);
      assert(width <= 32);
      labels = new int[0];
    }

    @Override
      public int size(){
        return labels.length;
      }

    @Override
      public long getLabelAt(int i){
        return Integer.toUnsignedLong(labels[i]) << ntz;
      }

    @Override
      public int indexOf(long label){
        return Unsigned.binarySearch(labels, 
            Unsigned.intValue((label & getMask()) >>> ntz));
      }

    @Override
      public int add(long label){
        int i = -(indexOf(label)) - 1;
        labels = Arrays.copyOf(labels, labels.length + 1);
        for(int j = labels.length - 1; j - 1 >= i; j--){
          labels[j] = labels[j - 1];
        }
        labels[i] = Unsigned.intValue((label & getMask()) >>> ntz);
        return i;
      }

    @Override
      public void dump(PrintStream ps, String indent){
        for (int i = 0; i < labels.length; i++) {
          ps.println(indent + Long.toBinaryString(labels[i]));
          if (!isLeaf()) {
            children[i].dump(ps, indent + spaces64);
          }
        }
      }

    @Override
      public void filterSuperblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list){
        long mask = getMask();
        int bits = 0;
        if(index < longs.length){
          bits = Unsigned.intValue((longs[index] & mask) >>> ntz);
        }

        int neighb = 0;
        if(index < neighbors.length){
          neighb = Unsigned.intValue((neighbors[index] & mask) >>> ntz);
        }

        if(isLeaf()){
          for(int i = labels.length - 1; i >= 0; i--){
            int label = labels[i];
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = labels.length - 1; i >= 0; i--){
            int label = labels[i];
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSuperblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }

    @Override
      public void filterSubblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list) {
        long mask = getMask();
        int bits = 0;
        if(index < longs.length){
          bits = Unsigned.intValue((longs[index] & mask) >>> ntz);
        }

        int neighb = 0;
        if(index < neighbors.length){
          neighb = Unsigned.intValue((neighbors[index] & mask) >>> ntz);
        }

        if(isLeaf()){
          for(int i = 0; i < labels.length; i++){
            int label = labels[i];
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = 0; i < labels.length; i++){
            int label = labels[i];
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Integer.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSubblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }
  }

  private class LongNode extends Node{
    private long[] labels;

    public LongNode(int index){
      this(index, 64, 0);
    }

    private LongNode(int index, int width, int ntz){
      super(index, width, ntz);
      assert(width <= 64);
      labels = new long[0];
    }

    @Override
      public int size(){
        return labels.length;
      }

    @Override
      public long getLabelAt(int i){
        return labels[i] << ntz;
      }

    @Override
      public int indexOf(long label){
        return Unsigned.binarySearch(labels, (label & getMask()) >>> ntz);
      }

    @Override
      public int add(long label){
        int i = -(indexOf(label)) - 1;
        labels = Arrays.copyOf(labels, labels.length + 1);
        for(int j = labels.length - 1; j - 1 >= i; j--){
          labels[j] = labels[j - 1];
        }
        labels[i] = ((label & getMask()) >>> ntz);
        return i;
      }

    @Override
      public void dump(PrintStream ps, String indent){
        for(int i = 0; i < labels.length; i++){
          ps.println(indent + Long.toBinaryString(labels[i]));
          if(!isLeaf()){
            children[i].dump(ps, indent + spaces64);
          }
        }
      }

    @Override
      public void filterSuperblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list){
        long mask = getMask();
        long bits = 0;
        if(index < longs.length){
          bits = (longs[index] & mask) >>> ntz;
        }

        long neighb = 0;
        if(index < neighbors.length){
          neighb = (neighbors[index] & mask) >>> ntz;
        }

        if(isLeaf()){
          for(int i = labels.length - 1; i >= 0; i--){
            long label = labels[i];
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Long.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = labels.length - 1; i >= 0; i--){
            long label = labels[i];
            if(Unsigned.compare(bits, label) > 0){
              break;
            }
            if((bits & ~label) == 0){
              int intersects1 = intersects +
                Long.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSuperblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }

    @Override
      public void filterSubblocks(long[] longs, long[] neighbors, 
          int intersects, ArrayList< XBitSet > list) {
        long mask = getMask();
        long bits = 0;
        if(index < longs.length){
          bits = (longs[index] & mask) >>> ntz;
        }

        long neighb = 0;
        if(index < neighbors.length){
          neighb = (neighbors[index] & mask) >>> ntz;
        }

        if(isLeaf()){
          for(int i = 0; i < labels.length; i++){
            long label = labels[i];
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Long.bitCount(label & neighb);
              if(intersects1 + cardinalities[i] 
                  <= targetWidth + 1){
                list.add(values[i]);
              }
            }
          }
        }
        else{
          for(int i = 0; i < labels.length; i++){
            long label = labels[i];
            if(Unsigned.compare(bits, label) < 0){
              break;
            }
            if((~bits & label) == 0){
              int intersects1 = intersects +
                Long.bitCount(label & neighb);
              if(intersects1 <= margin){
                children[i].filterSubblocks(
                    longs, neighbors, intersects1, list);
              }
            }
          }
        }
      }
  }

  public BlockSieve(int n, int targetWidth, int margin){
    this.n = n;
    this.targetWidth = targetWidth;
    this.margin = margin;
    root = new LongNode(0);
    last = (n - 1) / 64;
  }

  public XBitSet put(XBitSet bs, XBitSet value){
    long longs[] = bs.toLongArray();
    Node node = root, parent = null;

    int i = 0, j1 = 0;
    long bits = 0;
    for(;;){
      bits = 0;
      if(i < longs.length){
        bits = longs[i];
      }
      int j = node.indexOf(bits);
      if(j < 0){
        break;
      }
      if(node.isLeaf()){
        return node.values[j];
      }
      parent = node;
      node = node.children[j];
      i = node.index;
      j1 = j;
    }

    if(node.isLeaf()){
      node.add(bits, value);
    }
    else if(node.isLastInInterval()){
      node.add(bits, newPath(i + 1, longs, value));
    }
    else{
      Node header = newNode(
          i, 64 - (node.ntz + node.width), node.ntz + node.width);
      if(!header.isLeaf()){
        header.add(bits, newPath(i + 1, longs, value));
      }
      else{
        header.add(bits, value);
      }
      node.add(bits, header);
    }

    ++size;
    if(parent != null){
      parent.children[j1] = tryWidthResizing(node);
    }
    else{
      root = tryWidthResizing(node);
    }

    return null;
  }

  private Node tryWidthResizing(Node node){
    if(node.size() > MAX_CHILDREN_SIZE){
      Node node1 = resizeWidth(node);
      for(int i = 0; i < node1.children.length; i++){
        node1.children[i] = tryWidthResizing(node1.children[i]);
      }
      return node1;
    }
    return node;
  }

  private Node resizeWidth(Node node){
    int w = node.width, leng = node.size();
    long m = node.getMask();

    long[] l = new long[leng];
    int ntz = Long.numberOfTrailingZeros(m);
    int t = ntz + node.width;
    while(l.length > MAX_CHILDREN_SIZE){
      t = (ntz + t) / 2;
      m = Unsigned.consecutiveOneBit(ntz, t);
      int p = 0;
      for(int i = 0; i < leng; i++){
        long label = ((node.getLabelAt(i) & m) >>> ntz);
        int j = Unsigned.binarySearch(l, 0, p, label);
        if(j < 0){
          j = -j - 1;
          for(int k = p; k - 1 >= j; k--){
            l[k] = l[k - 1];
          }
          l[j] = label;
          ++p;
        }
      }
      l = Arrays.copyOfRange(l, 0, p);
    }

    Node[] c = new Node[l.length];
    for(int i = 0; i < c.length; i++){
      long msk = node.getMask() & ~m;
      c[i] = newNode(node.index, 
          Long.bitCount(msk), Long.numberOfTrailingZeros(msk));
    }

    for(int i = 0; i < leng; i++){
      long label = node.getLabelAt(i);
      int j = Unsigned.binarySearch(l, ((label & m) >>> ntz));
      if(!node.isLeaf()){
        c[j].add(label, node.children[i]);
      }
      else{
        c[j].add(label,
            node.values[i], node.cardinalities[i]);
      }
    }

    Node n1 = newNode(node.index, 
        Long.bitCount(m), Long.numberOfTrailingZeros(m));

    for(int i = 0; i < l.length; i++){
      n1.add(l[i] << ntz, c[i]);
    }

    return n1;
  }

  private Node newNode(int index, int width, int ntz){
    if(width > 32){
      return new LongNode(index, width, ntz);
    }
    else if(width > 16){
      return new IntegerNode(index, width, ntz);
    }
    else if(width > 8){
      return new ShortNode(index, width, ntz);
    }
    else{
      return new ByteNode(index, width, ntz);
    }
  }

  private Node newPath(int index, long[] longs, XBitSet value){
    Node node = new LongNode(index);

    long bits = 0;
    if(index < longs.length){
      bits = longs[index];
    }

    if(index == last){
      node.add(bits, value);
    }
    else{
      node.add(bits, newPath(index + 1, longs, value));
    }

    return node;
  }

  public void collectSuperblocks(
      XBitSet component, XBitSet neighbors, ArrayList< XBitSet > list){
    root.filterSuperblocks(component.toLongArray(), 
        neighbors.toLongArray(), 0, list);
  }

  public void collectSubblocks(
      XBitSet component, XBitSet neighbors, ArrayList< XBitSet > list){
    root.filterSubblocks(component.toLongArray(), 
        neighbors.toLongArray(), 0, list);
  }

  public int size(){
    return size;
  }

  public void dump(PrintStream ps){
    root.dump(ps, "");
  }

  public static void main(String args[]){
  }
}
