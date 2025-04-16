\section{Related Work}\label{sec:related-work}

Formal languages have a long history. We refer the interested reader to Hopcroft
et al.~\cite{hopcroft-book} which is an overview of traditional formal language
theory.

The main inspiration for our work is the work by Elliott on automatic and
symbolic differentiation of languages \cite{conal-languages}. As the title
suggests, it shows a duality between two styles of implementing language
derivatives in Agda. In this paper, we focus on the symbolic approach to
differentiation, but we still benefit from Elliott's clear and concise
presentation. Our work is an extension of Elliott's symbolic differentiation to
a more expressive subset of context-free languages.

For the idea behind our derivative rule for fixed points of languages, we were
inspired by Grenrus's blog post~\cite{fix-ing-regular-expressions}.

Previous work has implemented context-free (or similar) languages in Agda. For
example, Danielsson~\cite{total-parser-combinators} and Allais~\cite{agdarsec}
show how to implement a form of parser combinators in Agda. Both ensure
termination by requiring that parsers consume at least some input each
recursion. In our work, we lift this restriction, freeing programmers from
having to ensure their parsers consume input.

Another approach to parsing context-free grammars in Agda is to first convert
arbitrary context-free grammars to a form more amenable to parsing. For example,
Brink et al.~\cite{dependently-typed-grammars} show how to formalize the
left-corner transformation in Agda, which removes left-recursion from the
grammar, thus allowing the use of a more naive parsing algorithm. Another
example of this approach is by Bernardy and Jannson~\cite{certified-valiant},
who first transform the grammar into Chomsky Normal Form and subsequently
formalize and the efficient Valiant's algorithm.
For the sake of simplicity, we avoid such pre-processing transformations in our
work.

Perhaps the closest related work to ours can be found outside of Agda
formalizations, namely Thiemann's~\cite{Thiemann17} work on partial derivatives
for context-free languages.
His work supports μ-regular expressions without single-variable restriction of
our approach, which allows him to encode context free grammars with mutually
recursive nonterminals.
In Thiemann's approach, however, languages are sets of strings and parsing only
determines whether a string is in the set or not, whereas our parsers
conststruct a parse tree.
Furthermore, our proofs are mechanized in Agda, which gives us confidence in the
correctness, but also facilitates computer-aided experimentation.

Finally, there are some works which focus less on formalization and more on the
practical implementation of parsing μ-regular expressions.
Might et al.~\cite{parsing-with-derivatives} show how to parse μ-regular
 expressions using derivatives.
They use laziness and memoization to avoid nontermination.
Krishnaswami and Yallop~\cite{yallop} propose an alternative approach to parsing
μ-regular expressions.
They introduce a type system which enforces their languages to be in LL(1),
which they parse efficiently using staging. 