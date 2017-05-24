/*
 * Copyright (c) 2017, Hiromu Otsuka
*/

package tw.heuristic;

public class Unsigned{
  private Unsigned(){}

  public static final long ALL_ONE_BIT = 0xFFFFFFFFFFFFFFFFL;

  public static long consecutiveOneBit(int i, int j){
    return (ALL_ONE_BIT >>> (64 - j)) & (ALL_ONE_BIT << i);
  }

  public static byte byteValue(long value){
    return (byte)value;
  }

  public static short shortValue(long value){
    return (short)value;
  }

  public static int intValue(long value){
    return (int)value;
  }

  public static int toUnsignedInt(byte b){
    return Byte.toUnsignedInt(b);
  }

  public static int toUnsignedInt(short s){
    return Short.toUnsignedInt(s);
  }

  public static long toUnsignedLong(byte b){
    return Byte.toUnsignedLong(b);
  }

  public static long toUnsignedLong(short s){
    return Short.toUnsignedLong(s);
  }

  public static long toUnsignedLong(int i){
    return Integer.toUnsignedLong(i);
  }

  public static int binarySearch(byte[] a, byte key){
    return binarySearch(a, 0, a.length, key);
  }

  public static int binarySearch(short[] a, short key){
    return binarySearch(a, 0, a.length, key);
  }

  public static int binarySearch(int[] a, int key){
    return binarySearch(a, 0, a.length, key);
  }

  public static int binarySearch(long[] a, long key){
    return binarySearch(a, 0, a.length, key);
  }

  public static int compare(byte a, byte b){
    return Integer.compareUnsigned(
        toUnsignedInt(a), toUnsignedInt(b));
  }

  public static int compare(short a, short b){
    return Integer.compareUnsigned(
        toUnsignedInt(a), toUnsignedInt(b));
  }

  public static int compare(int a, int b){
    return Integer.compareUnsigned(a, b);
  }

  public static int compare(long a, long b){
    return Long.compareUnsigned(a, b);
  }

  public static int binarySearch(byte[] a,
      int fromIndex, int toIndex, byte key){
    int low = fromIndex;
    int high = toIndex - 1;

    while(low <= high) {
      int mid = (low + high) >>> 1;
      byte midVal = a[mid];
      int cmp = compare(midVal, key);

      if(cmp < 0){
        low = mid + 1;
      }
      else if(cmp > 0){
        high = mid - 1;
      }
      else{
        return mid;
      }
    }

    return -(low + 1);
  }

  public static int binarySearch(short[] a,
      int fromIndex, int toIndex, short key){
    int low = fromIndex;
    int high = toIndex - 1;

    while(low <= high) {
      int mid = (low + high) >>> 1;
      short midVal = a[mid];
      int cmp = compare(midVal, key);

      if(cmp < 0){
        low = mid + 1;
      }
      else if(cmp > 0){
        high = mid - 1;
      }
      else{
        return mid;
      }
    }

    return -(low + 1);
  }

  public static int binarySearch(int[] a,
      int fromIndex, int toIndex, int key){
    int low = fromIndex;
    int high = toIndex - 1;

    while(low <= high) {
      int mid = (low + high) >>> 1;
      int midVal = a[mid];
      int cmp = compare(midVal, key);

      if(cmp < 0){
        low = mid + 1;
      }
      else if(cmp > 0){
        high = mid - 1;
      }
      else{
        return mid;
      }
    }

    return -(low + 1);
  }

  public static int binarySearch(long[] a, 
      int fromIndex, int toIndex, long key){
    int low = fromIndex;
    int high = toIndex - 1;

    while(low <= high) {
      int mid = (low + high) >>> 1;
      long midVal = a[mid];
      int cmp = compare(midVal, key);

      if(cmp < 0){
        low = mid + 1;
      }
      else if(cmp > 0){
        high = mid - 1;
      }
      else{
        return mid;
      }
    }

    return -(low + 1);
  }
}
