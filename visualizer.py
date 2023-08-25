import networkx as nx
import matplotlib.pyplot as plt
import sys
import ast

# copy these from the haskell output
DEFAULT_NODES = [(-24, 21), (-17, 34), (-14, -27),
                 (21, 1), (25, -20), (33, 29)]
DEFAULT_EDGES = [(-24, 21, -3), (-17, -14, -24), (21, -24, 2), (21, 33, -8),
                 (25, -17, 10), (25, -17, 4), (25, -14, 4), (33, 25, -25)]

nodes, edges = (ast.literal_eval(sys.argv[1]), ast.literal_eval(
    sys.argv[2])) if len(sys.argv) >= 3 else (DEFAULT_NODES, DEFAULT_EDGES)

# Create a graph
G = nx.Graph()

# Add nodes
G.add_nodes_from(list(map(lambda x: x[0], nodes)))

# Add weighted edges
edges_with_weights = edges
G.add_weighted_edges_from(edges_with_weights)

# Draw the graph
pos = nx.circular_layout(G)  # positions for all nodes
labels = nx.get_edge_attributes(G, 'weight')
nx.draw_networkx_nodes(G, pos, node_color='lightblue', node_size=500)
nx.draw_networkx_edges(G, pos, width=2.0, alpha=0.5)
nx.draw_networkx_labels(G, pos, font_size=10, font_color='darkblue')
nx.draw_networkx_edge_labels(G, pos, edge_labels=labels, font_color='red')

# Show the plot
plt.show()
