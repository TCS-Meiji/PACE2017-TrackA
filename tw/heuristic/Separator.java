/*
 * Copyright (c) 2017, Hisao Tamaki and Hiromu Ohtsuka, Keitaro Makii
*/

package tw.heuristic;

import java.util.ArrayList;
import java.util.Arrays;

public class Separator implements Cloneable{
	Bag parent;
	Graph graph;
	VertexSet vertexSet;
	int size;
	ArrayList<Bag> incidentBags;
	boolean safe;
	boolean unsafe;
	boolean wall;

	int[] parentVertex;
	int safeSteps;

	public Separator(Bag parent) {
		this.parent = parent;
		graph = parent.graph;
		incidentBags = new ArrayList<>();
	}

	public Separator(Bag parent, VertexSet vertexSet) {
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

	private VertexSet convert(VertexSet s, int[] conv) {
		VertexSet result = new VertexSet();
		for (int v = s.nextSetBit(0); v >= 0;
				v = s.nextSetBit(v + 1)) {
			result.set(conv[v]);
		}
		return result;
	}

	void collectBagsToPack(ArrayList<Bag> list, Bag from) {
		for (Bag bag: incidentBags) {
			if (bag !=from) {
				bag.collectBagsToPack(list,  this);
			}
		}
	}

	public void figureOutSafetyBySPT() {
		if (!safe && !unsafe) {
			safe = isSafe();
			unsafe = !safe;
		}
	}

	public boolean isSafe() {
		SafeSeparator ss = new SafeSeparator(parent.graph);
		//return isSafeBySPT();
		safeSteps = ss.decideSafeness(vertexSet);
		return safeSteps > 0;
		//return ss.isSafeSeparator(vertexSet);
	}

	public int getSteps(){
	  return Math.abs(safeSteps);
	}

	public boolean isSafeBySPT() {
		parentVertex = new int[graph.n];
		ArrayList<VertexSet> components = 
			graph.getComponents(vertexSet);
		for (VertexSet compo: components) {
			if (!isSafeComponentBySPT(compo)) {
				return false;
			}
		}
		return true;
	}

	private boolean isSafeComponentBySPT(VertexSet component) {
		VertexSet neighborSet = graph.neighborSet(component);
		VertexSet rest = graph.all.subtract(neighborSet).subtract(component);

		for (int v = neighborSet.nextSetBit(0); v >= 0;
				v = neighborSet.nextSetBit(v + 1)) {
			VertexSet missing = neighborSet.subtract(graph.neighborSet[v]);

			for (int w = missing.nextSetBit(0); w >= 0 && w <= v;
					w = missing.nextSetBit(w + 1)) {
				missing.clear(w);
			}

			if (!missing.isEmpty()) {
				VertexSet spt = shortestPathTree(v, missing, rest);
				if (spt == null) {
					return false;
				}
				rest.andNot(spt);
			}
		}
		return true;
	}

	private VertexSet shortestPathTree(int v, VertexSet targets,
			VertexSet available) {
		VertexSet union = available.unionWith(targets);

		VertexSet reached = new VertexSet(graph.n);
		reached.set(v);
		VertexSet leaves = (VertexSet) reached.clone();
		while (!targets.isSubset(reached) && !leaves.isEmpty()) {
			VertexSet newLeaves = new VertexSet(graph.n);
			for (int u = leaves.nextSetBit(0); u >= 0;
					u = leaves.nextSetBit(u + 1)) {
				VertexSet children = 
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

		VertexSet spt = new VertexSet(graph.n);
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

	@Override
		public Separator clone(){
			try{
				Separator result = (Separator)super.clone();

				if(vertexSet != null){
					result.vertexSet = (VertexSet)vertexSet.clone();
				}
				if(parentVertex != null){
					result.parentVertex = Arrays.copyOf(parentVertex, parentVertex.length);
				}
				if(incidentBags != null){
					result.incidentBags = new ArrayList< >(incidentBags);
				}

				return result;
			}
			catch(CloneNotSupportedException cnse){
				throw new AssertionError();
			}
		}
}
