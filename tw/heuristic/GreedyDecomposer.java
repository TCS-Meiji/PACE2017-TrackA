/*
 * Copyright (c) 2017, Takuto Sato and Hiromu Ohtsuka
*/

package tw.heuristic;

import java.io.File;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import java.util.List;

public class GreedyDecomposer {
	//  static final boolean VERBOSE = true;
	private static final boolean VERBOSE = false;
	private static boolean DEBUG = false;
	//private static boolean DEBUG = false;

	private final static int GRAPH_EDGE_SIZE = 1_000_000;
	private final static int GRAPH_VERTEX_SIZE = 10_000;

	Graph g;

	Bag whole;

	Map<Integer, Set<Separator>> frontier;

	VertexSet remaining;

	TreeSet<Pair> minCostSet;

	Edge[] edges;
	int[] oldFill;

	boolean modeMinDegree;
	boolean modeExact;

  boolean timeOn;
  boolean abort;
  long step;
  long timeLimit;
  static final long STEPS_PER_MS = 1;

	public GreedyDecomposer(Bag whole) {
		this.whole = whole;
		this.g = whole.graph.copy();
	}

	public void decompose() {
    timeOn = false;
    abort = false;
    step = 0;

		selectDecompose();
	}

  public boolean decompose(long timeMS){
    timeOn = true;
    abort = false;
    step = 0;
    timeLimit = STEPS_PER_MS * timeMS;

		selectDecompose();

    if(abort){
      return false;
    }
    return true;
  }

  public boolean isAborted(){
    return timeOn && abort;
  }

  public long getTimeMS(){
    return step / STEPS_PER_MS;
  }

	private void selectDecompose() {
		int sum = 0;
		for(int v = 0; v < g.n; v++) {
			sum += g.degree[v];
		}
		sum /= 2;

		if(sum <= GRAPH_EDGE_SIZE) {
			modeMinDegree = false;
			//if(g.n <= GRAPH_VERTEX_SIZE) {
			if(sum <= GRAPH_VERTEX_SIZE) {
				modeExact = true;
			}
			else {
				modeExact = false;
			}
		}
		else {
			modeMinDegree = true;
			modeExact = false;
		}

		mainDecompose();
	}

	public void minFillDecompose() {
		modeMinDegree = false;
		mainDecompose();
	}

	public void minDegreeDecompose() {
		modeMinDegree = true;
		mainDecompose();
	}

	private void initialize() {
		whole.initializeForDecomposition();

		frontier = new HashMap<>();
		for(int i = 0; i < g.n; i++) {
			frontier.put(i, new HashSet<>());
		}

		remaining = (VertexSet) g.all.clone();

		minCostSet = new TreeSet<>();

		if(modeExact) {
			oldFill = new int[g.n];
		}

		for(int v = 0; v < g.n; v++) {
			int cost = 0;
			if(modeMinDegree) {
				cost = g.degree[v];
			}
			else {
				cost = costOf(v);
			}
			Pair p = new Pair(v, cost);
			minCostSet.add(p);
			if(modeExact) {
				oldFill[v] = cost;
			}
		}
	}

	private void mainDecompose() {
		initialize();

		while (!remaining.isEmpty()) {
      if(timeOn && step > timeLimit){
        abort = true;
        return;
      }

			int vmin;
			if(modeExact) {
				Pair p = minCostSet.first();
				minCostSet.remove(p);
				vmin = p.v;
				int cost = fillCount(vmin);
			}
			else {
				vmin = delayProcess();
			}

			Set<Separator> vminInSeparators = frontier.get(vmin);
			if(vminInSeparators.size() == 1) {
				VertexSet neighborSet = g.neighborSet[vmin].intersectWith(remaining);
				Separator	uniqueSeparator = null;
				for(Separator s : vminInSeparators) {
					uniqueSeparator = s;
				}

				if(neighborSet.isSubset(uniqueSeparator.vertexSet)) {
					uniqueSeparator.removeVertex(vmin);
					if(uniqueSeparator.vertexSet.isEmpty()) {
						whole.separators.remove(uniqueSeparator);
						for(Bag b : uniqueSeparator.incidentBags) {
							b.incidentSeparators.remove(uniqueSeparator);
						}
					}
					remaining.clear(vmin);

					if(!modeMinDegree && modeExact) {
						VertexSet vs = g.neighborSet[vmin].intersectWith(remaining);
						VertexSet updateSet = g.closedNeighborSet(vs);
						updateSet.and(remaining);
						updateProcess(updateSet);
					}
					continue;
				}
			}

			VertexSet toBeAClique = new VertexSet(g.n);
			toBeAClique.set(vmin);
			toBeAClique.or(g.neighborSet[vmin].intersectWith(remaining));
			Bag bag = whole.addNestedBag(toBeAClique);

			VertexSet sep = toBeAClique.subtract(new VertexSet(new int[]{vmin}));

			if(modeMinDegree) {
				for(int v = sep.nextSetBit(0); v >= 0; v = sep.nextSetBit(v + 1)) {
					g.neighborSet[v].or(sep);
					g.neighborSet[v].clear(v);
				}
			}
			else {
				if(edges != null) {
					for(Edge e : edges) {
						g.addEdge(e.v, e.w);
					}
				}
			}

			if (!sep.isEmpty()) {
				Separator separator = whole.addSeparator(sep);

				separator.addIncidentBag(bag);
				bag.addIncidentSeparator(separator);

				for(int v = separator.vertexSet.nextSetBit(0); v >= 0; v = separator.vertexSet.nextSetBit(v + 1)) {
					frontier.get(v).add(separator);
				}
			}

			for (Separator s : vminInSeparators) {
				s.addIncidentBag(bag);
				bag.addIncidentSeparator(s);

				for(int v = s.vertexSet.nextSetBit(0); v >= 0; v = s.vertexSet.nextSetBit(v + 1)) {
					if(v != vmin){
						frontier.get(v).remove(s);
					}
				}
			}
			frontier.remove(vmin, vminInSeparators);

			remaining.clear(vmin);

			if(!modeMinDegree && modeExact) {
				VertexSet vs = g.neighborSet[vmin].intersectWith(remaining);
				VertexSet updateSet = g.closedNeighborSet(vs);
				updateSet.and(remaining);
				updateProcess(updateSet);
			}
		}

		whole.setWidth();
	}

	private void updateProcess(VertexSet updateSet) {
		for(int v = updateSet.nextSetBit(0); v >= 0; v = updateSet.nextSetBit(v + 1)) {
			int fill = fillCount(v);

			Pair old = new Pair(v, oldFill[v]);
			Pair update = new Pair(v, fill);

			minCostSet.remove(old);
			minCostSet.add(update);
			oldFill[v] = fill;
		}
	}

	private int delayProcess() {
		Pair p = minCostSet.first();
		for(;;) {
			if(p.cost == 0) {
				minCostSet.remove(p);
				edges = null;
				break;
			}
			int cost = costOf(p.v);
			if(cost <= p.cost) {
				minCostSet.remove(p);
				break;
			}
			else {
				minCostSet.remove(p);
				Pair q = new Pair(p.v, cost);
				minCostSet.add(q);
				p = null;
				p = minCostSet.first();
			}
		}
		return p.v;
	}

	private int costOf(int v) {
    ++step;
		if(modeMinDegree) {
			return degreeOf(v);
		}
		else {
			return fillCount(v);
		}
	}

	private int degreeOf(int v) {
		VertexSet vs = g.neighborSet[v].intersectWith(remaining);
		return vs.cardinality();
	}

	private int fillCount(int v) {
		VertexSet vNeighborSet = remaining.intersectWith(g.neighborSet[v]);
		ArrayList<Edge> addEdges = new ArrayList<>();
		int count = 0;

		for(int w = vNeighborSet.nextSetBit(0); w >= 0; w = vNeighborSet.nextSetBit(w + 1)) {
			VertexSet noNeighborSet = vNeighborSet.subtract(vNeighborSet.intersectWith(g.neighborSet[w]));
			noNeighborSet.and(remaining);
			noNeighborSet.clear(w);
			for(int x = noNeighborSet.nextSetBit(w); x >= 0; x = noNeighborSet.nextSetBit(x + 1)) {
				Edge e = new Edge(w, x);
				addEdges.add(e);
				count++;
			}
		}
		edges = addEdges.toArray(new Edge[0]);
		return count;
	}

	private	class Pair implements Comparable<Pair> {
		int v;
		int cost;

		Pair(int v, int cost) {
			this.v = v;
			this.cost = cost;
		}

		@Override
			public int compareTo(Pair p){
				if(cost != p.cost){
					return Integer.compare(cost, p.cost);
				}
				return Integer.compare(v, p.v);
			}

		@Override
			public boolean equals(Object obj){
				if(!(obj instanceof Pair)){
					return false;
				}
				Pair p = (Pair)obj;
				return v == p.v &&
					cost == p.cost;
			}

		@Override
			public String toString() {
				return "v : " + v + ", cost : " + cost;
			}
	}

	private	class Edge {
		int v;
		int w;

		public Edge(int v, int w) {
			this.v = v;
			this.w = w;
		}

		@Override
			public boolean equals(Object obj) {
				if(!(obj instanceof Edge)){
					return false;
				}
				Edge e = (Edge) obj;
				return (v == e.v && w == e.w) || (v == e.w && w == e.v);
			}

		@Override
			public int hashCode() {
				int seed = 1234;
				return seed ^ v ^ w;
			}
	}

	private static void test() {
	}

	private static void targetTest() {
	}

	public static void main(String[] args) {
	}
}
