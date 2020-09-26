state: Represents a partially completed RHS of a rule. The grammar
provides compiled trie of rule RHSs where each node is called a
state. Each node has an associated list of nonterminals which that RHS
"completes", i.e., nonterminals which are LHSs for that RHS.

edge: An edge represents a discovered covering of nonterminals over a
span. There are two possible types. An active edge consists of a state
(i.e., some portion of the RHS of a rule) and the start and end
indices of the span which is covered by that state. An active edge
still needs to be completed. A passive edge consists of a constituent
symbold and the state and end indices of that consitituent. A passive
edge is complete.

traversal: A traversal records one way of discovering extending an
active edge to an active or passive edge. It consists of an active
edge and a passive edge (i.e., a complete constituent that can extend
the state of the active edge one further).
