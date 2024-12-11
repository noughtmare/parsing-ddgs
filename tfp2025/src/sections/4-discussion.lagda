\begin{code}[hide]
module 4-discussion where
\end{code}

\section{Discussion}

% TODO

\begin{itemize}
\item Ambiguity is naturally expressed from this type theoretic perspective.
\item We want to write a parser which has the property that it takes only linear time on unambiguous grammars. One potential line of reasoning is that taking the derivative of an unambiguous grammar never makes the grammar grow larger than some constant multiple of its original size. That would ensure linear time parsing.
\item Might and Darais have written an implementation that uses continuations and caching to improve performance. Can we also formalize their implementation using this type theoretic approach?
\item What benefits does this approach have compared to more traditional formalizations of context free grammars?
\item We want to extend this approach to cover data-dependent grammars. To achieve that, we can add a data parameter to the fixed points such that we can pass a piece of data in at the start and update it on every recursive call. This data can be used to disambiguate grammars.
\item Can we avoid the fuel approach? We have explored using guarded type theory, but it did not seem to simplify the presentation as much as we hoped. Another alternative that we have not explored in much depth is to ... tree/trie of strings.
\item Elliot also presents an approach to parsing using coinductive tries, does that also apply to context-free languages?
\end{itemize}
