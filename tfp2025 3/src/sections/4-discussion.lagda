\begin{code}[hide]
module 4-discussion where
\end{code}

\section{Discussion}

Finally, we want to discuss three aspects of our work: expressiveness, performance, and simplicity.

\jr{TODO: μ-regular expressions have been studied before, cite}
\paragraph{Expressiveness} We conjecture that our grammars which include variables and fixed points can describe any context-free language.
\jr{mention that we only support context-free languages without mutual recursion and how we use a subset of μ-regular languages}.
% We have shown the example of balanced the bracket language which is known to be context-free. Furthermore, Grenrus shows that any context-free grammar can be converted to his grammars \cite{fix-ing-regular-expressions}, which are similar to our grammars. The main problem is showing that mutually recursive nonterminals can be expressed using our simple fixed points, which requires Beki\'c's bisection lemma~\cite{Bekic1984}. Formalizing this in our framework is future work.

Going beyond context-free languages, many practical programming languages cannot be adequately described as context-free languages. For example, features such as associativity, precedence, and indentation sensitivity cannot be expressed directly using context-free grammars. Recent work by Afroozeh and Izmaylova~\cite{one-parser-to-rule-them-all} shows that all these advanced features can be supported if we extend our grammars with data-dependencies. Our framework can form a foundation for such extensions and we consider formalizing it as future work.

\paragraph{Performance}
\jr{cite Jeremy Yallop's work}
For a parser to practically useful, it must at least have linear asymptotic complexity for practical grammars. Might et al. \cite{parsing-with-derivatives} show that naively parsing using derivatives does not achieve that bound, but optimizations might make it possible. In particular, they argue that we could achieve $O(n|G|)$ time complexity (where $|G|$ is the grammar size) if the grammar size stays approximately constant after every derivative. By compacting the grammar, they conjecture it is possible to achieve this bound for any unambiguous grammar. We want to investigate if similar optimizations could be applied to our parser and if we can prove that we achieve this bound.

\paragraph{Simplicity}
One of the main contributions of Elliott's type theoretic formalization of languages~\cite{conal-languages} is its simplicity of implementation and proof. To be able to extend his approach to context-free languages we have had to introduce some complications.
\jr{TODO: finish this paragraph}
% Most notably, we use fuel to define the semantics of our grammars. We have explored other approaches such as using guarded type theory, but we did not manage to significantly simplify our formalization. Furtheremore, we expect that many proofs remain simple despite our fuel-based approach.