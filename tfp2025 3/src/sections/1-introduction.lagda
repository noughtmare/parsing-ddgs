\begin{code}[hide]
{-# OPTIONS --cubical --guarded #-}
module 1-introduction where

\end{code}

\section{Introduction}

Parsing is the conversion of flat, human-readable text into a tree structure
that is easier for computers to manipulate.  As one of the central
pillars of compiler tooling since the 1960s, today almost every automated
transformation of computer programs requires a form of parsing.
Though it is such a mature research subject, it is still actively studied, for example the question of how to resolve ambiguities in context-free grammars \cite{one-parser-to-rule-them-all}. 

Recent work by Elliot uses interactive theorem provers to state simple specifications of languages and that proofs of desirable properties of these language specifications transfer easily to their parsers \cite{conal-languages}. Unfortunately, this work only considers regular languages which are not powerful enough to describe practical programming languages.

In this paper, we formalize context-free languages and show how to parse them, extending Elliot’s type theoretic approach to language specfication.  One of the main challenges is that the recursive nature of context-free languages does not map directly onto automated theorem provers as they do not support general recursion. We use a fuel-based approach to solve this problem.

We make the following concrete contributions:
\begin{itemize}
\item We extend Elliot's type theoretic formalization of regular languages to context-free languages.
\end{itemize}

For this paper we have chosen Agda as our type theory and interactive theorem prover. We believe our definitions should transfer easily to other theories and tools. This paper itself is a literate Agda file; all highlighted Agda code has been accepted by Agda's type checker, giving us a high confidence of correctness. Unfortunately, we are still working out the proof of three postulates in \cref{sec:cfg-parsing}. These are the only postulates that we have yet to prove.