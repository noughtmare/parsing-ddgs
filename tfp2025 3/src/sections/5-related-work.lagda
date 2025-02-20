\section{Related Work}\label{sec:related-work}

Formal languages have a long history; too long to summarize here. We refer the
interested reader to Hocroft et al.~\cite{hopcroft-book} which is an overview of
traditional formal language theory.

The main inspiration for our work is the work by Elliott on automatic and
symbolic differentiation of languages \cite{conal-languages}. As the title
suggests, it shows a duality between two styles of implementing language
derivatives in Agda. In this paper, we focus on the symbolic approach to
differentiation, but we still benefit from Elliott's clear and concise
presentation. Our work is an extension of Elliott's symbolic differentiation to
a more expressive subset of context-free languages.

Previous work has shown that context-free (or similar) languages can be
implemented in Agda. For example, Danielsson and
Anders~\cite{total-parser-combinators} and Allais~\cite{agdarsec} show how to
implement a form of parser combinators in Agda. Both ensure termination by
requiring that parsers consume at least some input each recursion. In our work,
we lift this restriction, freeing programmers from having to ensure their
parsers consume input.

Another approach to writing context-free grammars in Agda is to first convert
arbitrary context-free grammars to a form more amenable to parsing. For example,
Brink et al.~\cite{dependently-typed-grammars} show how to formalize the
left-corner transformation in Agda, which removes left-recursion from the
grammar, thus allowing the use of a more naive parsing algorithm. Another
example of this approach is by Bernardy and Jannson, who first transform the
grammar into Chomsky Normal Form and subsequently formalize and the efficient
Valiant's algorithm. For the sake of simplicity, we avoid such pre-processing
transformations in our work.

Perhaps the closest related work to ours can be found outside of Agda
formalizations, namely Thiemann's~\cite{Thiemann17} work on partial derivatives
for context-free languages. His work does cover mutually recursive nonterminals
and furthermore relates derivative-based parsers to pushdown automata.  In
contrast to our type-theoretic approach, Thiemann's approach is based on set
theory which means languages are just sets of strings and the result of parsing
is only the boolean which tells you whether the input string is in the language
or not. In this way, the information about the tree structure that naturally
results from parsing---and which is often desired in practice---remains
implicit. Furthermore, our proofs are mechanized in Agda, which gives us confidence in the correctness, but also facilitates computer-aided experimentation.