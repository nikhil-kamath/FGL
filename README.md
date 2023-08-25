# FGL
This suite is made for automatic, model-based testing of graph algorithms!

#### How it Works
Essentially, a model-based test compares two implementations of the same problem to ensure an algorithm provides the same output on both of them.

I've created a variety of pre-programmed tests which compare the outputs of builtin graph implementations in Haskell, namely the `Patricia Tree` and the `Tree`.

The suite:
- Generates an arbitrary graph
- Represents it using both data structures
- Runs an algorithm on both equal representations
- Ensures they return the same result

And repeats, thousands of times, automatically!

#### Running the Tests
To execute the test suite, run:
 ```
 $ stack build; stack run
 ```
All of the tests correspond to a particular graph function in the builtin `FGL` library.

#### Extra Configuration
You can make the generator only create `undirected`, `connected`, or `positive` graphs by adjusting those settings within `src/Config.hs`

#### Visualization
The tests will output any counter-example graphs to the terminal. It prints them out as:
 ```
 <test name>
 mkGraph [node] [edge] ?=:? mkGraph [node] [edge]
 <the conflicting outputs of the algorithm>
 ```
I included a lightweight python graph visualizer, which you can call using:
```
$ python visualizer.py "[node]" "[edge]"
```
Note that it requires `networkx` and `matplotlib` to be in your environment.