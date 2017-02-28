/*
 * Copyright (c) 2016, Hisao Tamaki
 */
package tw.exact;

import java.io.BufferedReader;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Random;

/**
 * This class provides a representation of undirected simple graphs.
 * The vertices are identified by non-negative integers
 * smaller than {@code n} where {@code n} is the number
 * of vertices of the graph.
 * The degree (the number of adjacent vertices) of each vertex
 * is stored in an array {@code degree} indexed by the vertex number
 * and the adjacency lists of each vertex
 * is also referenced from an array {@code neighbor} indexed by
 * the vertex number. These arrays as well as the int variable {@code n}
 * are public to allow easy access to the graph content.
 * Reading from and writing to files as well as some basic
 * graph algorithms, such as decomposition into connected components,
 * are provided.
 *
 * @author  Hisao Tamaki
 */
public class Graph {
  /**
   * number of vertices
   */
  public int n;

  /**
   * array of vertex degrees
   */
  public int[] degree;

  /**
   * array of adjacency lists each represented by an integer array
   */
  public int[][] neighbor;

  /**
   * set representation of the adjacencies.
   * {@code neighborSet[v]} is the set of vertices
   * adjacent to vertex {@code v}
   */
  public XBitSet[] neighborSet;

  /**
   * the set of all vertices, represented as an all-one
   * bit vector
   */
  public XBitSet all;

  /*
   * variables used in the DFS aglgorithms fo
   * connected componetns and
   * biconnected components.
   */
  private int nc;
  private int mark[];
  private int dfn[];
  private int low[];
  private int dfCount;
  private XBitSet articulationSet;

  /**
   * Construct a graph with the specified number of
   * vertices and no edges.  Edges will be added by
   * the {@code addEdge} method
   * @param n the number of vertices
   */
  public Graph(int n) {
    this.n = n;
    this.degree = new int[n];
    this.neighbor = new int[n][];
    this.neighborSet = new XBitSet[n];
    for (int i = 0; i < n; i++) {
      neighborSet[i] = new XBitSet(n);
    }
    this.all = new XBitSet(n);
    for (int i = 0; i < n; i++) {
      all.set(i);
    }
  }

  /**
   * Add an edge between two specified vertices.
   * This is done by adding each vertex to the adjacent list
   * of the other.
   * No effect if the specified edge is already present.
   * @param u vertex (one end of the edge)
   * @param v vertex (the other end of the edge)
   */
  public void addEdge(int u, int v) {
    addToNeighbors(u, v);
    addToNeighbors(v, u);
  }

  /**
   * Add vertex {@code v} to the adjacency list of {@code u}
   * @param u vertex number
   * @param v vertex number
   */
  private void addToNeighbors(int u, int v) {
    if (indexOf(v, neighbor[u]) >= 0) {
      return;
    }
    degree[u]++;
    if (neighbor[u] == null) {
      neighbor[u] = new int[]{v};
    }
    else {
      neighbor[u] = Arrays.copyOf(neighbor[u], degree[u]);
      neighbor[u][degree[u] - 1] = v;
    }

    if (neighborSet[u] == null) {
      neighborSet[u] = new XBitSet(n);
    }
    neighborSet[u].set(v);
  }

  /**
   * Returns the number of edges of this graph
   * @return the number of edges
   */
  public int numberOfEdges() {
    int count = 0;
    for (int i = 0; i < n; i++) {
      count += degree[i];
    }
    return count / 2;
  }

  /**
   * Inherit edges of the given graph into this graph,
   * according to the conversion tables for vertex numbers.
   * @param g graph
   * @param conv vertex conversion table from the given graph to
   * this graph: if {@code v} is a vertex of graph {@code g}, then
   * {@code conv[v]} is the corresponding vertex in this graph;
   * {@code conv[v] = -1} if {@code v} does not have a corresponding vertex
   * in this graph
   * @param inv vertex conversion table from this graph to
   * the argument graph: if {@code v} is a vertex of this graph,
   * then {@code inv[v]} is the corresponding vertex in graph {@code g};
   * it is assumed that {@code v} always have a corresponding vertex in
   * graph g.
   *
   */
  public void inheritEdges(Graph g, int conv[], int inv[]) {
    for (int v = 0; v < n; v++) {
      int x = inv[v];
      for (int i = 0; i < g.degree[x]; i++) {
        int y = g.neighbor[x][i];
        int u = conv[y];
        if (u >= 0) {
            addEdge(u,  v);
        }
      }
    }
  }

  /**
   * Read a graph from the specified file in {@code dgf} format and
   * return the resulting {@code Graph} object.
   * @param path the path of the directory containing the file
   * @param name the file name without the extension ".dgf"
   * @return the resulting {@code Graph} object; null if the reading fails
   */
  public static Graph readGraphDgf(String path, String name) {
    File file = new File(path + "/" + name + ".dgf");
    return readGraphDgf(file);
  }

  /**
   * Read a graph from the specified file in {@code dgf} format and
   * return the resulting {@code Graph} object.
   * @param file file from which to read
   * @return the resulting {@code Graph} object; null if the reading fails
   */
  public static Graph readGraphDgf(File file) {
    try {
      BufferedReader br = new BufferedReader(new FileReader(file));
      String line = br.readLine();
      while (line.startsWith("c")) {
        line = br.readLine();
      }
      if (line.startsWith("p")) {
        String s[] = line.split(" ");
        int n = Integer.parseInt(s[2]);
        // m is twice the number of edges explicitly listed
        int m = Integer.parseInt(s[3]);
        Graph g = new Graph(n);

        for (int i = 0; i < m; i++) {
          line = br.readLine();
          while (!line.startsWith("e")) {
            line = br.readLine();
          }
          s = line.split(" ");
          int u = Integer.parseInt(s[1]) - 1;
          int v = Integer.parseInt(s[2]) - 1;
          g.addEdge(u, v);
        }
        return g;
      }
      else {
        throw new RuntimeException("!!No problem descrioption");
      }

    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    return null;
  }

  /**
   * Read a graph from the specified file in {@code col} format and
   * return the resulting {@code Graph} object.
   * @param path the path of the directory containing the file
   * @param name the file name without the extension ".col"
   * @return the resulting {@code Graph} object; null if the reading fails
   */
  public static Graph readGraphCol(String path, String name) {
    File file = new File(path + "/" + name + ".col");
    try {
      BufferedReader br = new BufferedReader(new FileReader(file));
      String line = br.readLine();
      while (line.startsWith("c")) {
        line = br.readLine();
      }
      if (line.startsWith("p")) {
        String s[] = line.split(" ");
        int n = Integer.parseInt(s[2]);
        // m is twice the number of edges in this format
        int m = Integer.parseInt(s[3]);
        Graph g = new Graph(n);

        for (int i = 0; i < m; i++) {
          line = br.readLine();
          while (line != null && !line.startsWith("e")) {
            line = br.readLine();
          }
          if (line == null) {
            break;
          }
          s = line.split(" ");
          int u = Integer.parseInt(s[1]);
          int v = Integer.parseInt(s[2]);
          g.addEdge(u - 1, v - 1);
        }
        return g;
      }
      else {
        throw new RuntimeException("!!No problem descrioption");
      }

    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    return null;
  }

  /**
   * Read a graph from the specified file in {@code gr} format and
   * return the resulting {@code Graph} object.
   * The vertex numbers 1~n in the gr file format are
   * converted to 0~n-1 in the internal representation.
   * @param file graph file in {@code gr} format
   * @return the resulting {@code Graph} object; null if the reading fails
   */
  public static Graph readGraph(String path, String name) {
    File file = new File(path + "/" + name + ".gr");
    return readGraph(file);
  }

  /**
   * Read a graph from the specified file in {@code gr} format and
   * return the resulting {@code Graph} object.
   * The vertex numbers 1~n in the gr file format are
   * converted to 0~n-1 in the internal representation.
   * @param path the path of the directory containing the file
   * @param name the file name without the extension ".gr"
   * @return the resulting {@code Graph} object; null if the reading fails
   */
  public static Graph readGraph(File file) {
    try {
      BufferedReader br = new BufferedReader(new FileReader(file));
      String line = br.readLine();
      while (line.startsWith("c")) {
        line = br.readLine();
      }
      if (line.startsWith("p")) {
        String s[] = line.split(" ");
        if (!s[1].equals("tw")) {
          throw new RuntimeException("!!Not treewidth instance");
        }
        int n = Integer.parseInt(s[2]);
        int m = Integer.parseInt(s[3]);
        Graph g = new Graph(n);

        for (int i = 0; i < m; i++) {
          line = br.readLine();
          while (line.startsWith("c")) {
            line = br.readLine();
          }
          s = line.split(" ");
          int u = Integer.parseInt(s[0]);
          int v = Integer.parseInt(s[1]);
          g.addEdge(u - 1, v - 1);
        }
        return g;
      }
      else {
        throw new RuntimeException("!!No problem descrioption");
      }

    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    return null;
  }

  /**
   * Read a graph from the specified input stream in {@code gr} format and
   * return the resulting {@code Graph} object.
   * The vertex numbers 1~n in the gr file format are
   * converted to 0~n-1 in the internal representation.
   * @param is the input stream representing the graph
   * @return the resulting {@code Graph} object; null if the reading fails
   */
  public static Graph readGraph(InputStream is) {
    try {
      BufferedReader br = new BufferedReader(
          new InputStreamReader(is));
      String line = br.readLine();
      while (line.startsWith("c")) {
        line = br.readLine();
      }
      if (line.startsWith("p")) {
        String s[] = line.split(" ");
        if (!s[1].equals("tw")) {
          throw new RuntimeException("!!Not treewidth instance");
        }
        int n = Integer.parseInt(s[2]);
        int m = Integer.parseInt(s[3]);
        Graph g = new Graph(n);

        for (int i = 0; i < m; i++) {
          line = br.readLine();
          while (line.startsWith("c")) {
            line = br.readLine();
          }
          s = line.split(" ");
          int u = Integer.parseInt(s[0]);
          int v = Integer.parseInt(s[1]);
          g.addEdge(u - 1, v - 1);
        }
        
        br.close();
        return g;
      }
      else {
        throw new RuntimeException("!!No problem descrioption");
      }

    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    return null;
  }

  /**
   * finds the first occurence of the
   * given integer in the given int array
   * @param x value to be searched
   * @param a array
   * @return the smallest {@code i} such that
   * {@code a[i]} = {@code x};
   * -1 if no such {@code i} exists
   */
  private static int indexOf(int x, int a[]) {
    if (a == null) {
      return -1;
    }
    for (int i = 0; i < a.length; i++) {
      if (x == a[i]) {
        return i;
      }
    }
    return -1;
  }

  /**
   * returns true if two vetices are adjacent to each other
   * in this targat graph
   * @param u a vertex
   * @param v another vertex
   * @return {@code true} if {@code u} is adjcent to {@code v};
   * {@code false} otherwise
   */
  public boolean areAdjacent(int u, int v) {
    return indexOf(v, neighbor[u]) >= 0;
  }

  /**
   * returns the minimum degree, the smallest d such that
   * there is some vertex {@code v} with {@code degree[v]} = d,
   * of this target graph
   * @return the minimum degree
   */
  public int minDegree() {
    if (n == 0) {
      return 0;
    }
    int min = degree[0];
    for (int v = 0; v < n; v++) {
      if (degree[v] < min) min = degree[v];
    }
    return min;
  }

  /**
   * Computes the neighbor set for a given set of vertices
   * @param set set of vertices
   * @return an {@code XBitSet} reprenting the neighbor set of
   * the given vertex set
   */
  public XBitSet neighborSet(XBitSet set) {
    XBitSet result = new XBitSet(n);
    for (int v = set.nextSetBit(0); v >= 0;
        v = set.nextSetBit(v + 1)) {
      result.or(neighborSet[v]);
    }
    result.andNot(set);
    return result;
  }

  /**
   * Computes the closed neighbor set for a given set of vertices
   * @param set set of vertices
   * @return an {@code XBitSet} reprenting the closed neighbor set of
   * the given vertex set
   */
  public XBitSet closedNeighborSet(XBitSet set) {
    XBitSet result = (XBitSet) set.clone();
    for (int v = set.nextSetBit(0); v >= 0;
        v = set.nextSetBit(v + 1)) {
      result.or(neighborSet[v]);
    }
    return result;
  }

  /**
   * Compute connected components of this target graph after
   * the removal of the vertices in the given separator,
   * using Depth-First Search
   * @param separator set of vertices to be removed
   * @return the arrayList of connected components,
   * the vertex set of each component represented by a {@code XBitSet}
   */
  public ArrayList<XBitSet> getComponentsDFS(XBitSet separator) {
    ArrayList<XBitSet> result = new ArrayList<XBitSet>();
    mark = new int[n];
    for (int v = 0; v < n; v++) {
      if (separator.get(v)) {
        mark[v] = -1;
      }
    }

    nc = 0;

    for (int v = 0; v < n; v++) {
      if (mark[v] == 0) {
        nc++;
        markFrom(v);
      }
    }

    for (int c = 1; c <= nc; c++) {
      result.add(new XBitSet(n));
    }

    for (int v = 0; v < n; v++) {
      int c = mark[v];
      if (c >= 1) {
        result.get(c - 1).set(v);
      }
    }
    return result;
  }

  /**
   * Recursive method for depth-first search
   * vertices reachable from the given vertex,
   * passing through only unmarked vertices (vertices
   * with the mark[] value being 0 or -1),
   * are marked by the value of {@code nc} which
   * is a positive integer
   * @param v vertex to be visited
   */
  private void markFrom(int v) {
    if (mark[v] != 0) return;
    mark[v] = nc;
    for (int i = 0; i < degree[v]; i++) {
      int w = neighbor[v][i];
      markFrom(w);
    }
  }

  /**
   * Compute connected components of this target graph after
   * the removal of the vertices in the given separator,
   * by means of iterated bit operations
   * @param separator set of vertices to be removed
   * @return the arrayList of connected components,
   * the vertex set of each component represented by a {@code XBitSet}
   */
  public ArrayList<XBitSet> getComponents(XBitSet separator) {
    ArrayList<XBitSet> result = new ArrayList<XBitSet>();
    XBitSet rest = all.subtract(separator);
    for (int v = rest.nextSetBit(0); v >= 0;
        v = rest.nextSetBit(v + 1)) {
      XBitSet c = (XBitSet) neighborSet[v].clone();
      XBitSet toBeScanned = c.subtract(separator);
      c.set(v);
      while (!toBeScanned.isEmpty()) {
        XBitSet save = (XBitSet) c.clone();
        for (int w = toBeScanned.nextSetBit(0); w >= 0;
            w = toBeScanned.nextSetBit(w + 1)) {
          c.or(neighborSet[w]);
        }
        toBeScanned = c.subtract(save);
        toBeScanned.andNot(separator);
      }
      result.add(c.subtract(separator));
      rest.andNot(c);
    }

    return result;
  }

  /**
   * Compute the full components associated with the given separator,
   * by means of iterated bit operations
   * @param separator set of vertices to be removed
   * @return the arrayList of full components,
   * the vertex set of each component represented by a {@code XBitSet}
   */
  public ArrayList<XBitSet> getFullComponents(XBitSet separator) {
    ArrayList<XBitSet> result = new ArrayList<XBitSet>();
    XBitSet rest = all.subtract(separator);
    for (int v = rest.nextSetBit(0); v >= 0;
        v = rest.nextSetBit(v + 1)) {
      XBitSet c = (XBitSet) neighborSet[v].clone();
      XBitSet toBeScanned = c.subtract(separator);
      c.set(v);
      while (!toBeScanned.isEmpty()) {
        XBitSet save = (XBitSet) c.clone();
        for (int w = toBeScanned.nextSetBit(0); w >= 0;
          w = toBeScanned.nextSetBit(w + 1)) {
          c.or(neighborSet[w]);
        }
        toBeScanned = c.subtract(save);
        toBeScanned.andNot(separator);
      }
      if (separator.isSubset(c)) {
        result.add(c.subtract(separator));
      }
      rest.andNot(c);
    }
    return result;
  }

  /**
   * Checks if the given induced subgraph of this target graph is connected.
   * @param vertices the set of vertices inducing the subraph
   * @return {@code true} if the subgrpah is connected; {@code false} otherwise
   */

  public boolean isConnected(XBitSet vertices) {
    int v = vertices.nextSetBit(0);
    if (v < 0) {
      return true;
    }

    XBitSet c = (XBitSet) neighborSet[v].clone();
    XBitSet toScan = c.intersectWith(vertices);
    c.set(v);
    while (!toScan.isEmpty()) {
      XBitSet save = (XBitSet) c.clone();
      for (int w = toScan.nextSetBit(0); w >= 0;
        w = toScan.nextSetBit(w + 1)) {
        c.or(neighborSet[w]);
      }
      toScan = c.subtract(save);
      toScan.and(vertices);
    }
    return vertices.isSubset(c);
  }

  /**
   * Checks if the given induced subgraph of this target graph is biconnected.
   * @param vertices the set of vertices inducing the subraph
   * @return {@code true} if the subgrpah is biconnected; {@code false} otherwise
   */
  public boolean isBiconnected(BitSet vertices) {
//    if (!isConnected(vertices)) {
//      return false;
//    }
    dfCount = 1;
    dfn = new int[n];
    low = new int[n];

    for (int v = 0; v < n; v++) {
      if (!vertices.get(v)) {
        dfn[v] = -1;
      }
    }

    int s = vertices.nextSetBit(0);
    dfn[s] = dfCount++;
    low[s] = dfn[s];

    boolean first = true;
    for (int i = 0; i < degree[s]; i++) {
      int v = neighbor[s][i];
      if (dfn[v] != 0) {
        continue;
      }
      if (!first) {
        return false;
      }
      boolean b = dfsForBiconnectedness(v);
      if (!b) return false;
      else {
        first = false;
      }
    }
    return true;
  }

  /**
   * Depth-first search for deciding biconnectivigy.
   * @param v vertex to be visited
   * @return {@code true} if articulation point is found
   * in the search starting from {@cod v}, {@false} otherwise
   */
  private boolean dfsForBiconnectedness(int v) {
    dfn[v] = dfCount++;
    low[v] = dfn[v];
    for (int i = 0; i < degree[v]; i++) {
      int w = neighbor[v][i];
      if (dfn[w] > 0 && dfn[w] < low[v]) {
        low[v] = dfn[w];
      }
      else if (dfn[w] == 0) {
        boolean b = dfsForBiconnectedness(w);
        if (!b) {
          return false;
        }
        if (low[w] >= dfn[v]) {
          return false;
        }
        if (low[w] < low[v]) {
          low[v] = low[w];
        }
      }
    }
    return true;
  }


  /**
   * Checks if the given induced subgraph of this target graph is triconnected.
   * This implementation is naive and call isBiconnected n times, where n is
   * the number of vertices
   * @param vertices the set of vertices inducing the subraph
   * @return {@code true} if the subgrpah is triconnected; {@code false} otherwise
   */
  public boolean isTriconnected(BitSet vertices) {
    if (!isBiconnected(vertices)) {
      return false;
    }

    BitSet work = (BitSet) vertices.clone();
    int prev = -1;
    for (int v = vertices.nextSetBit(0); v >= 0;
        v = vertices.nextSetBit(v + 1)) {
      if (prev >= 0) {
        work.set(prev);
      }
      prev = v;
      work.clear(v);
      if (!isBiconnected(work)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Compute articulation vertices of the subgraph of this
   * target graph induced by the given set of vertices
   * Assumes this subgraph is connected; otherwise, only
   * those articulation vertices in the first connected component
   * are obtained.
   *
   * @param vertices the set of vertices of the subgraph
   * @return the set of articulation vertices
   */
  public XBitSet articulations(BitSet vertices) {
    articulationSet = new XBitSet(n);
    dfCount = 1;
    dfn = new int[n];
    low = new int[n];

    for (int v = 0; v < n; v++) {
      if (!vertices.get(v)) {
        dfn[v] = -1;
      }
    }

    depthFirst(vertices.nextSetBit(0));
    return articulationSet;
  }

  /**
   * Depth-first search for listing articulation vertices.
   * The articulations found in the search are
   * added to the {@code XBitSet articulationSet}.
   * @param v vertex to be visited
   */
  private void depthFirst(int v) {
    dfn[v] = dfCount++;
    low[v] = dfn[v];
    for (int i = 0; i < degree[v]; i++) {
      int w = neighbor[v][i];
      if (dfn[w] > 0) {
        low[v] = Math.min(low[v], dfn[w]);
      }
      else if (dfn[w] == 0) {
        depthFirst(w);
        if (low[w] >= dfn[v] &&
            (dfn[v] > 1 || !lastNeighborIndex(v, i))){
          articulationSet.set(v);
        }
        low[v] = Math.min(low[v], low[w]);
      }
    }
  }

  /**
   * Decides if the given index is the effectively
   * last index of the neighbor array of the given vertex,
   * ignoring vertices not in the current subgraph
   * considered, which is known by their dfn being -1.
   * @param v the vertex in question
   * @param i the index in question
   * @return {@code true} if {@code i} is effectively
   * the last index of the neighbor array of vertex {@code v};
   * {@code false} otherwise.
   */

  private boolean lastNeighborIndex(int v, int i) {
    for (int j = i + 1; j < degree[v]; j++) {
      int w = neighbor[v][j];
      if (dfn[w] == 0) {
        return false;
      }
    }
    return true;
  }

  /** 
   * fill the specified vertex set into a clique
   * @param vertexSet vertex set to be filled 
   */
  public void fill(XBitSet vertexSet) {
    for (int v = vertexSet.nextSetBit(0); v >= 0;
        v = vertexSet.nextSetBit(v + 1)) {
      XBitSet missing = vertexSet.subtract(neighborSet[v]);
      for (int w = missing.nextSetBit(v + 1); w >= 0;
          w = missing.nextSetBit(w + 1)) {
        addEdge(v, w);
      }
    }
  }
  
  /** 
   * fill the specified vertex set into a clique
   * @param vertices int array listing the vertices in the set
   */
  public void fill(int[] vertices) {
    for (int i = 0; i < vertices.length; i++) {
      for (int j = i + 1; j < vertices.length; j++) {
        addEdge(vertices[i], vertices[j]);
      }
    }
  }
  
  /** list all maximal cliques of this graph
   * Naive implementation, should be replaced by a better one
   * @return
   */
  public ArrayList<XBitSet> listMaximalCliques() {
    ArrayList<XBitSet> list = new ArrayList<>();
    XBitSet subg = new XBitSet(n);
    XBitSet cand = new XBitSet(n);
    XBitSet qlique = new XBitSet(n);
    subg.set(0,n);
    cand.set(0,n);
    listMaximalCliques(subg, cand, qlique, list);
    return list;
  }

  /**
   * Auxiliary recursive method for listing maximal cliques
   * Adds to {@code list} all maximal cliques
   * @param subg
   * @param cand
   * @param clique
   * @param list
   */
  private void listMaximalCliques(XBitSet subg, XBitSet cand,
      XBitSet qlique, ArrayList<XBitSet> list) {
      if(subg.isEmpty()){
        list.add((XBitSet)qlique.clone());
        return;
      }
      int max = -1;
      XBitSet u = new XBitSet(n);
      for(int i=subg.nextSetBit(0);i>=0;i=subg.nextSetBit(i+1)){
        XBitSet tmp = new XBitSet(n);
        tmp.set(i);
        tmp = neighborSet(tmp);
        tmp.and(cand);
        if(tmp.cardinality() > max){
          max = tmp.cardinality();
          u = tmp;
        }
      }
      XBitSet candu = (XBitSet) cand.clone();
      candu.andNot(u);
      while(!candu.isEmpty()){
        int i = candu.nextSetBit(0);
        XBitSet tmp = new XBitSet(n);
        tmp.set(i);
        qlique.set(i);
        XBitSet subgq = (XBitSet) subg.clone();
        subgq.and(neighborSet(tmp));
        XBitSet candq = (XBitSet) cand.clone();
        candq.and(neighborSet(tmp));
        listMaximalCliques(subgq,candq,qlique,list);
        cand.clear(i);
        candu.clear(i);
        qlique.clear(i);
      }
  }

  /**
   * Saves this target graph in the file specified by a path string,
   * in .gr format.
   * A stack trace will be printed if the file is not available for writing
   * @param path the path-string
   */
  public void save(String path) {
    File outFile = new File(path);
    PrintStream ps;
    try {
      ps = new PrintStream(new FileOutputStream(outFile));
      writeTo(ps);
      ps.close();
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    }
  }
  /**
   * Write this target graph in .gr format to the given
   * print stream.
   * @param ps print stream
   */
  public void writeTo(PrintStream ps) {
    int m = 0;
    for (int i = 0; i < n; i++) {
      m += degree[i];
    }
    m = m / 2;
    ps.println("p tw " + n + " " + m);
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < degree[i]; j++) {
        int k = neighbor[i][j];
        if (i < k) {
          ps.println((i + 1) + " " + (k + 1));
        }
      }
    }
  }

  /**
   * Create a copy of this target graph
   * @return the copy of this graph
   */
  public Graph copy() {
    Graph tmp = new Graph(n);
    for (int v = 0; v < n; v++) {
      for (int j = 0; j < neighbor[v].length; j++) {
        int w = neighbor[v][j];
        tmp.addEdge(v, w);
      }
    }
    return tmp;
  }

  /**
   * Check consistency of this graph
   * 
   */
  public void checkConsistency() throws RuntimeException {
    for (int v = 0; v < n; v++) {
      for (int w = 0; w < n; w++) {
        if (v == w) continue;
        if (indexOf(v, neighbor[w]) >= 0 && 
            indexOf(w, neighbor[v]) < 0) {
          throw new RuntimeException("adjacency lists inconsistent " + v + ", " + w);
        }
        if (neighborSet[v].get(w) &&
            !neighborSet[w].get(v)) {
          throw new RuntimeException("neighborSets inconsistent " + v + ", " + w);
        }
      }
    }
  }
  /**
   * Create a random graph with the given number of vertices and
   * the given number of edges
   * @param n the number of vertices
   * @param m the number of edges
   * @param seed the seed for the pseudo random number generation
   * @return {@code Graph} instance constructed
   */
  public static Graph randomGraph(int n, int m, int seed) {
    Random random = new Random(seed);
    Graph g = new Graph(n);

    int k = 0;
    int j = 0;
    int m0 = n * (n - 1) / 2;
    for (int v = 0; v < n; v++) {
      for (int w = v + 1; w < n; w++) {
        int r = random.nextInt(m0 - j);
        if (r < m - k) {
          g.addEdge(v, w);
          g.addEdge(w, v);
          k++;
        }
        j++;
      }
    }
    return g;
  }

  public static void main(String args[]) {
    // an example of the use of random graph generation
    Graph g = randomGraph(80, 1000, 1);
    g.save("instance/random/gnm_80_1000_1.gr");
  }
}
