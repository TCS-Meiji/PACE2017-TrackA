#include <vector>
#include <algorithm>
#include <set>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <string>

/*
 * If USE_VECTOR is set, use std::vector to store adjacency lists; this seems to
 * be faster for the instances we observed, where the degrees tend to be small
 */
#define USE_VECTOR

/*
 * An unsigned variant of std::stoi that also checks if the input consists
 * entirely of base-10 digits
 */
unsigned pure_stou(const std::string& s) {
  if(s.empty() || s.find_first_not_of("0123456789") != std::string::npos) {
    throw std::invalid_argument("Non-numeric entry '" + s + "'");
  }
  unsigned long result = std::stoul(s);
  if (result > std::numeric_limits<unsigned>::max()) {
    throw std::out_of_range("stou");
  }
  return result;
}

#ifdef USE_VECTOR
/*
 * The most basic graph structure you could imagine, in adjacency list
 * representation.  This is not supposed to be any kind of general-purpose graph
 * class, but only implements what we need for our computations. E.g., removing
 * vertices is not supported.
 */
struct graph {
  std::vector<std::vector<unsigned> > adj_list;
  unsigned num_vertices = 0;
  unsigned num_edges = 0;

  /*
   * Adds a vertex to the vertex set and returns its index.
   * Vertices in this class are indexed starting with 0 (!).
   * This is important because the vertices in the file format are not.
   */
  unsigned add_vertex() {
    adj_list.push_back(std::vector<unsigned>());
    return num_vertices++;
  }

  /*
   * The neighbors of a given vertex, where the index is, as usual, starting
   * with 0. Does *not* include the vertex itself
   */
  std::vector<unsigned>& neighbors(unsigned vertex_index) {
    return adj_list[vertex_index];
  }

  /*
   * Adds an undirected edge between two vertices, identified by their index; no
   * checks are performed and bad indices can cause segfaults.
   */
  void add_edge(unsigned u, unsigned v) {
    adj_list.at(u).push_back(v);
    adj_list.at(v).push_back(u);
    num_edges++;
  }

  /*
   * Removes an undirected edge
   */
  void remove_edge(unsigned u, unsigned v) {
    bool end1 = false;
    bool end2 = false;
    auto v_it = std::find(adj_list.at(u).begin(), adj_list.at(u).end(), v);
    if (v_it != adj_list.at(u).end()) {
      adj_list.at(u).erase(v_it);
      end1 = true;
    }

    auto u_it = std::find(adj_list.at(v).begin(), adj_list.at(v).end(), u);
    if (u_it != adj_list.at(v).end()) {
      adj_list.at(v).erase(u_it);
      end2 = true;
    }

    if (end1 && end2) {
      num_edges--;
    }
  }
};
#else
struct graph {
  std::vector<std::set<unsigned> > adj_list;
  unsigned num_vertices = 0;
  unsigned num_edges = 0;

  unsigned add_vertex() {
    adj_list.push_back(std::set<unsigned>());
    return num_vertices++;
  }

  std::set<unsigned>& neighbors(unsigned vertex_index) {
    return adj_list[vertex_index];
  }

  void add_edge(unsigned u, unsigned v) {
    adj_list[u].insert(v);
    adj_list[v].insert(u);
    num_edges++;
  }

  void remove_edge(unsigned u, unsigned v) {
    bool end1 = false;
    bool end2 = false;
    auto v_it = adj_list[u].find(v);
    if (v_it != adj_list[u].end()) {
      adj_list[u].erase(v_it);
      end1 = true;
    }

    auto u_it = adj_list[v].find(u);
    if (u_it != adj_list[v].end()) {
      adj_list[v].erase(u_it);
      end2 = true;
    }

    if (end1 && end2) {
      num_edges--;
    }
  }
};
#endif

/*
 * Type for a tree decomposition; i.e. a set of bags (vertices) together with
 * adjacency lists on this set.  As the graph class, this is highly minimalistic
 * and implements all operations in such a way that our algorithms may work on
 * it.
 */
struct tree_decomposition {
  typedef std::set<unsigned> vertex_t;
  std::vector<vertex_t> bags;
  std::vector<std::vector<unsigned>> adj_list;

  /*
   * The number of *relevant* bags currently in the tree; bags that were removed
   * using remove_vertex and continue to exist empty and isolated are not
   * counted.
   */
  unsigned num_vertices = 0;
  unsigned num_edges = 0;

  /*
   * Adds a given bag to the vertex set of the decomposition and returns its
   * index.  Vertices in this class are indexed starting with 0 (!).  This is
   * important because the vertices in the file format are not.
   */
  unsigned add_bag(vertex_t& bag) {
    bags.push_back(bag);
    adj_list.push_back(std::vector<unsigned>());
    return num_vertices++;
  }

  /*
   * See the graph class
   */
  std::vector<unsigned>& neighbors(unsigned vertex_index) {
    return adj_list.at(vertex_index);
  }

  /*
   * See the graph class
   */
  void add_edge(unsigned u, unsigned v) {
    adj_list.at(u).push_back(v);
    adj_list.at(v).push_back(u);
    num_edges++;
  }

  /*
   * See the graph class
   */
  void remove_edge(unsigned u, unsigned v) {
    auto v_it = std::find(adj_list.at(u).begin(),adj_list.at(u).end(),v);
    auto u_it = std::find(adj_list.at(v).begin(),adj_list.at(v).end(),u);
    if (v_it != adj_list.at(u).end() && u_it != adj_list.at(v).end()) {
      adj_list.at(u).erase(v_it);
      adj_list.at(v).erase(u_it);
      num_edges--;
    }
  }

  /*
   * Removes a vertex, in the following sense: The bag corresponding to the
   * index is emptied and all adjacencies are removed, i.e., the bag will
   * contain 0 vertices and have no incident edges. Nevertheless, the number of
   * vertices is reduced (hence num_vertices--).
   */
  void remove_vertex(unsigned u) {
    bags.at(u).clear();
    std::vector<unsigned> remove;
    for (auto it = adj_list.at(u).begin(); it != adj_list.at(u).end(); it++) {
      remove.push_back(*it);
    }
    for (auto it = remove.begin(); it != remove.end(); it++) {
      remove_edge(u,*it);
    }
    num_vertices--;
  }

  /*
   * Get the u-th bag
   */
  vertex_t& get_bag(unsigned u) {
    return bags.at(u);
  }

  /*
   * Checks if the given decomposition constitutes a tree using DFS
   */
  bool is_tree() {
    if ((num_vertices > 0) && num_vertices - 1 != num_edges) {
      return false;
    } else if (num_vertices == 0) {
      return (num_edges == 0);
    }

    std::vector<int> seen(num_vertices, 0);
    unsigned seen_size = 0;

    bool cycle = !tree_dfs(seen,0,-1,seen_size);
    if (cycle || seen_size != num_vertices) {
      return false;
    }
    return true;
  }

  /*
   * Helper method for is_tree(); not to be called from outside of the class
   */
  bool tree_dfs(std::vector<int>& seen, unsigned root, unsigned parent, unsigned& num_seen) {
    if (seen[root] != 0) {
      return false;
    }

    seen[root] = 1;
    num_seen++;

    for (auto it = adj_list[root].begin(); it != adj_list[root].end(); it++) {
      if (*it != parent) {
        if (!tree_dfs(seen, *it, root,num_seen)) {
          return false;
        }
      }
    }
    return true;
  }
};

/*
 * The different states the syntax checker may find itself in while checking the
 * syntax of a *.gr- or *.td-file.
 */
enum State {
  COMMENT_SECTION,
  S_LINE,
  BAGS,
  EDGES,
  P_LINE
};

/*
 * Messages associated with the respective exceptions to be thrown while
 * checking the files
 */
const char* INV_FMT = "Invalid format";
const char* INV_SOLN = "Invalid s-line";
const char* INV_SOLN_BAGSIZE = "Invalid s-line: Reported bagsize and actual bagsize differ";
const char* INV_EDGE = "Invalid edge";
const char* INV_BAG = "Invalid bag";
const char* INV_BAG_INDEX = "Invalid bag index";
const char* INC_SOLN = "Inconsistent values in s-line";
const char* NO_BAG_INDEX = "No bag index given";
const char* BAG_MISSING = "Bag missing";
const char* FILE_ERROR = "Could not open file";
const char* EMPTY_LINE = "No empty lines allowed";
const char* INV_PROB = "Invalid p-line";

/*
 * The state the syntax checker is currently in; this variable is used for both
 * checking the tree *and* the graph
 */
State current_state = COMMENT_SECTION;

/*
 * A collection of global variables that are relentlessly manipulated and read
 * from different positions of the program.  Initially, they are set while
 * reading the input files.
 */

/* The number of vertices of the graph underlying the decomposition, as stated
 * in the *.td-file
 */
unsigned n_graph;

/* The number of bags as stated in the *.td-file */
unsigned n_decomp;

/* The width of the decomposition as stated in the *.td-file */
unsigned width;

/* The number of vertices of the graph as stated in the *.gr-file */
unsigned n_vertices;

/* The number of edges of the graph as stated in the *.gr-file */
unsigned n_edges;

/* The maximal width of some bag, to compare with the one stated in the file */
unsigned real_width;

/* A vector to record which of the bags were seen so far, while going through
 * the *.td-file, as to ensure uniqueness of each bag.
 */
std::vector<int> bags_seen;

/* Temporary storage for all the bags before they are inserted into the actual
 * decomposition; we might as well directly manipulate the tree TODO
 */
std::vector<std::set<unsigned> > bags;

/*
 * Given the tokens from one line (split on whitespace), this reads the
 * s-line from these tokens and initializes the corresponding globals
 */
void read_solution(const std::vector<std::string>& tokens)
{
  if (current_state != COMMENT_SECTION) {
    throw std::invalid_argument(INV_FMT);
  }
  current_state = S_LINE;
  if(tokens.size() != 5 || tokens[1] != "td") {
    throw std::invalid_argument(INV_SOLN);
  }

  n_decomp = pure_stou(tokens[2]);
  width = pure_stou(tokens[3]);
  n_graph = pure_stou(tokens[4]);
  if (width > n_graph) {
    throw std::invalid_argument(INC_SOLN);
  }
}

/*
 * Given the tokens from one line (split on whitespace), this reads the bag
 * represented by these tokens and manipulates the global bags accordingly
 */
void read_bag(const std::vector<std::string>& tokens)
{
  if (current_state == S_LINE) {
    current_state = BAGS;
    bags.resize(n_decomp);
    bags_seen.resize(n_decomp,0);
  }

  if (current_state != BAGS) {
    throw std::invalid_argument(INV_FMT);
  }

  if(tokens.size() < 2) {
    throw std::invalid_argument(NO_BAG_INDEX);
  }

  unsigned bag_num = pure_stou(tokens[1]);
  if (bag_num < 1 || bag_num > n_decomp || bags_seen[bag_num-1] != 0) {
    throw std::invalid_argument(INV_BAG_INDEX);
  }
  bags_seen[bag_num-1] = 1;

  for(unsigned i = 2; i < tokens.size(); i++) {
    if (tokens[i] == "") break;
    unsigned id = pure_stou(tokens[i]);
    if (id < 1 || id > n_graph) {
      throw std::invalid_argument(INV_BAG);
    }

    bags[bag_num-1].insert(id);
  }

  if(bags[bag_num-1].size() > real_width) {
    real_width = bags[bag_num-1].size();
  }
}

/*
 * Given the tokens from one line (split on whitespace) and a tree
 * decomposition, this reads the edge represented by this line (in the
 * decomposition) and adds the respective edge to the tree decomposition
 */
void read_decomp_edge(const std::vector<std::string>& tokens, tree_decomposition &T)
{
  if (current_state == BAGS) {
    for (auto it = bags_seen.begin(); it != bags_seen.end(); it++) {
      if (*it == 0) {
        throw std::invalid_argument(BAG_MISSING);
      }
    }

    for (auto it = bags.begin(); it != bags.end(); it++) {
      T.add_bag(*it);
    }
    current_state = EDGES;
  }

  if (current_state != EDGES) {
    throw std::invalid_argument(INV_FMT);
  }

  unsigned s = pure_stou(tokens[0]);
  unsigned d = pure_stou(tokens[1]);
  if(s < 1 || d < 1 || s > n_decomp || d > n_decomp) {
    throw std::invalid_argument(INV_EDGE);
  }
  T.add_edge(s-1, d-1);
}

/*
 * Given the tokens from one line (split on whitespace), this reads the
 * p-line from these tokens and initializes the corresponding globals
 */
void read_problem(const std::vector<std::string>& tokens, graph& g) {
  if (current_state != COMMENT_SECTION) {
    throw std::invalid_argument(INV_FMT);
  }
  current_state = P_LINE;

  if(tokens.size() != 4 || tokens[1] != "tw") {
    throw std::invalid_argument(INV_PROB);
  }

  n_vertices = pure_stou(tokens[2]);
  n_edges = pure_stou(tokens[3]);

  while (g.add_vertex()+1 < n_vertices) {};
}

/*
 * Given the tokens from one line (split on whitespace) and a tree
 * decomposition, this reads the edge (in the graph) represented by this line
 * and adds the respective edge to the graph
 */
void read_graph_edge(const std::vector<std::string>& tokens, graph& g)
{
  if (current_state == P_LINE) {
    current_state = EDGES;
  }

  if (current_state != EDGES) {
    throw std::invalid_argument(INV_FMT);
  }

  unsigned s = pure_stou(tokens[0]);
  unsigned d = pure_stou(tokens[1]);
  if(s < 1 || d < 1 || s > n_vertices || d > n_vertices) {
    throw std::invalid_argument(INV_EDGE);
  }
  g.add_edge(s-1, d-1);
}

/*
 * Given a stream to the input file in the *.gr-format, this reads from the file
 * the graph represented by this file.  If the file is not conforming to the
 * format, it throws a corresponding std::invalid_argument with one of the error
 * messages defined above.
 */
void read_graph(std::ifstream& fin, graph& g) {
  current_state = COMMENT_SECTION;
  n_edges = -1;
  n_vertices = -1;

  if(!fin.is_open()){
    throw std::invalid_argument(FILE_ERROR);
  }

  std::string line;
  std::string delimiter = " ";

  while(std::getline(fin, line)) {
    if(line == "" || line == "\n") {
      throw std::invalid_argument(EMPTY_LINE);
    }

    std::vector<std::string> tokens;
    size_t oldpos = 0;
    size_t newpos = 0;

    while(newpos != std::string::npos) {
      newpos = line.find(delimiter, oldpos);
      tokens.push_back(line.substr(oldpos, newpos-oldpos));
      oldpos = newpos + delimiter.size();
    }
    if (tokens[0] == "c") {
      continue;
    } else if (tokens[0] == "p") {
      read_problem(tokens,g);
    } else if (tokens.size() == 2){
      read_graph_edge(tokens, g);
    } else {
      throw std::invalid_argument(std::string(INV_EDGE) + " (an edge has exactly two endpoints)");
    }
  }

  if (g.num_edges != n_edges) {
    throw std::invalid_argument(std::string(INV_PROB) + " (incorrect number of edges)");
  }
}

/*
 * Given a stream to the input file in the *.td-format, this reads from the file
 * the decomposition represented by this file.  If the file is not conforming to
 * the format, it throws a corresponding std::invalid_argument with one of the
 * error messages defined above.
 */
void read_tree_decomposition(std::ifstream& fin, tree_decomposition& T)
{
  current_state = COMMENT_SECTION;
  n_graph = -1;
  n_decomp = 0;
  width = -2;
  bags_seen.clear();
  bags.clear();

  if(!fin.is_open()){
    throw std::invalid_argument(FILE_ERROR);
  }

  std::string line;
  std::string delimiter = " ";

  while(std::getline(fin, line)) {
    if(line == "" || line == "\n") {
      throw std::invalid_argument(EMPTY_LINE);
    }

    std::vector<std::string> tokens;
    size_t oldpos = 0;
    size_t newpos = 0;

    while(newpos != std::string::npos) {
      newpos = line.find(delimiter, oldpos);
      tokens.push_back(line.substr(oldpos, newpos-oldpos));
      oldpos = newpos + delimiter.size();
    }

    if (tokens[0] == "c") {
      continue;
    } else if (tokens[0] == "s") {
      read_solution(tokens);
    } else if (tokens[0] == "b") {
      read_bag(tokens);
    } else {
      read_decomp_edge(tokens, T);
    }
  }

  if (current_state == BAGS) {
    for (auto it = bags.begin(); it != bags.end(); it++) {
      T.add_bag(*it);
    }
  }

  if (width != real_width) {
    throw std::invalid_argument(INV_SOLN_BAGSIZE);
  }
}

/*
 * Given a graph and a decomposition, this checks whether or not the set of
 * vertices in the graph equals the union of all bags in the decomposition.
 */
bool check_vertex_coverage(tree_decomposition& T)
{
  if (!(n_graph == n_vertices)) {
    std::cerr << "Error: .gr and .td disagree on how many vertices the graph has" << std::endl;
    return false;
  } else if (n_vertices == 0) return true;

  std::vector<unsigned> occurrence_nums(n_graph, 0);
  for (unsigned i = 0; i < n_decomp; i++) {
    for (auto it = T.get_bag(i).begin(); it != T.get_bag(i).end(); it++) {
      occurrence_nums[*it - 1]++;
    }
  }

  for (unsigned i = 0; i < occurrence_nums.size(); i++) {
    if (occurrence_nums[i] == 0) {
      std::cerr << "Error: vertex " << (i+1) << " appears in no bag" << std::endl;
      return false;
    }
  }
  return true;
}

/*
 * Given a graph and a decomposition, this checks whether or not each edge is
 * contained in at least one bag.  This has the side effect of removing from the
 * graph all those edges of the graph that are in fact contained in some bag.
 * The emptiness of the edge set of the resulting pruned graph is used to decide
 * whether the decomposition has this property.
 */
bool check_edge_coverage(tree_decomposition& T, graph& g)
{
  std::vector<std::pair<unsigned,unsigned> > to_remove;
  /*
   * We go through all bags, and for each vertex in each bag, we remove all its
   * incident edges.  If all the edges are indeed covered by at least one bag,
   * this will leave the graph with an empty edge-set, and it won't if they
   * aren't.
   */
  for(unsigned i = 0; i < T.bags.size() && g.num_edges > 0; i++){
    std::set<unsigned>& it_bag = T.get_bag(i);
    for (std::set<unsigned>::iterator head = it_bag.begin(); head != it_bag.end(); head++) {
      for(auto tail = g.neighbors(*head-1).begin(); tail != g.neighbors(*head-1).end(); tail++) {
        if(it_bag.find(*tail+1) != it_bag.end()) {
          to_remove.push_back(std::pair<unsigned, unsigned>(*head,*tail));
        }
      }
      for (std::vector<std::pair<unsigned, unsigned> >::iterator rem_it = to_remove.begin(); rem_it != to_remove.end(); rem_it++) {
        g.remove_edge(rem_it->first-1,rem_it->second);
      }
      to_remove.clear();
    }
  }

  if (g.num_edges > 0)
  {
    for (unsigned u = 0; u < g.num_vertices; u++)
    {
      if (! g.adj_list.at(u).empty() )
      {
        unsigned v=g.adj_list.at(u).front();
        std::cerr << "Error: edge {"<< (u+1) << ", " << (v+1) << "} appears in no bag" << std::endl;
        break;
      }
    }
  }
  return (g.num_edges == 0);
}

/*
 * Given a graph and a decomposition, this checks whether or not the set of bags
 * in which a given vertex from the graph appears forms a subtree of the tree
 * decomposition.  It does so by successively removing leaves from the
 * decomposition until the tree is empty, and hence the decomposition will
 * consist only of isolated empty bags after calling this function.
 */
bool check_connectedness(tree_decomposition& T)
{
  /*
   * At each leaf, we first check whether it contains some forgotten vertex (in
   * which case we return false), and if it doesn't, we compute whether there
   * are any vertices that appear in the leaf, but not in its parent, and if so,
   * we add those vertices to the set of forgotten vertices (Now that I come to
   * think of it, 'forbidden' might be a better term TODO.) We then remove the
   * leaf and continue with the next leaf.  We return true if we never encounter
   * a forgotten vertex before the tree is entirely deleted.
   *
   * It is quite easy to see that a tree decomposition satisfies this property
   * (given that it satisfies the others) if and only if it satisfies the
   * condition of the bags containing any given vertex forming a subtree of the
   * decomposition.
   */
  std::set<unsigned> forgotten;


  /* A vector to keep track of those bags that were removed during the check for
   * subtree connectivity */
  std::vector<int> bags_removed;
  bags_removed.resize(T.bags.size(),0);

  while (T.num_vertices > 0) {
    /* In every iteration, we first find a leaf of the tree. We do this in an
     * overly naive way by running through all of the tree, but given the small
     * size of the instances, this does not matter much.  This can be formulated
     * using some form of DFS-visitor-pattern, but this gets the job done as
     * well.
     */
    for(unsigned i = 0; i < T.bags.size(); i++) {
      /*
       * If we are dealing with a leaf (or an isolated, non-empty bag, which may
       * only happen in the last iteration when there is only one non-empty bag
       * left, by the semantics of the remove_vertex-method), then we first see
       * if there is a non-empty intersection with the set of forgotten
       * vertices, and if so, return false. If this is not the case, we add all
       * vertices appearing in the bag but not its parent to the set of
       * forgotten vertices and continue to look for the next leaf.
       */
      if (T.neighbors(i).size() == 1 || (T.neighbors(i).size() == 0 && bags_removed.at(i) == 0)) {
        std::set<unsigned> intersection;
        std::set_intersection(forgotten.begin(), forgotten.end(),
            T.get_bag(i).begin(), T.get_bag(i).end(),
            std::inserter(intersection, intersection.begin()));
        if(!intersection.empty()) {
          return false;
        }

        if (T.neighbors(i).size() > 0) {
          unsigned parent = T.neighbors(i).at(0);
          std::set_difference(T.get_bag(i).begin(), T.get_bag(i).end(),
              T.get_bag(parent).begin(), T.get_bag(parent).end(),
              std::inserter(forgotten, forgotten.begin()));
        }

        T.remove_vertex(i);
        bags_removed.at(i) = 1;
        break;
      }
    }
  }
  return true;
}

/*
 * Using all of the above functions, this simply checks whether a given
 * purported tree decomposition for some graph actually is one.
 */
bool is_valid_decomposition(tree_decomposition& T, graph& g)
{
  if (!T.is_tree()) {
    std::cerr << "Error: not a tree" << std::endl;
    return false;
  } else if (!check_vertex_coverage(T)) {
    return false;
  } else if (!check_edge_coverage(T,g)) {
    return false;
  } else if (!check_connectedness(T)) {
    std::cerr << "Error: some vertex induces disconnected components in the tree" << std::endl;
    return false;
  }
  else {
    return true;
  }
}

int main(int argc, char** argv) {
  bool is_valid = true;
  bool empty_td_file = false;
  if (argc < 2 || argc > 3) {
    std::cerr << "Usage: " << argv[0] << " input.gr [input.td]" << std::endl;
    std::cerr << std::endl;
    std::cerr << "Validates syntactical and semantical correctness of .gr and .td files. If only a .gr file is given, it validates the syntactical correctness of that file." << std::endl;
    exit(1);
  }
  tree_decomposition T;
  graph g;

  std::ifstream fin(argv[1]);
  try {
    read_graph(fin,g);
  } catch (const std::invalid_argument& e) {
    std::cerr << "Invalid format in " << argv[1] << ": " << e.what() << std::endl;
    is_valid = false;
  }
  fin.close();

  if(argc==3 && is_valid) {
    fin.open(argv[2]);
    if (fin.peek() == std::ifstream::traits_type::eof()) {
      is_valid = false;
      empty_td_file = true;
    } else {
      try {
        read_tree_decomposition(fin, T);
      } catch (const std::invalid_argument& e) {
        std::cerr << "Invalid format in " << argv[2] << ": " << e.what() << std::endl;
        is_valid = false;
      }
    }
    fin.close();

    if (is_valid) {
      is_valid = is_valid_decomposition(T,g);
    }
  }

  if (is_valid) {
    std::cerr << "valid" << std::endl;
    return 0;
  } else if (empty_td_file) {
    std::cerr << "invalid: empty .td file" << std::endl;
    return 2;
  } else {
    std::cerr << "invalid" << std::endl;
    return 1;
  }
}
