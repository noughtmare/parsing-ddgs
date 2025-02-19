\begin{code}[hide]
{-# OPTIONS --cubical --guarded #-}
module 1-introduction where

open import Data.Unit

\end{code}

\section{Introduction}

Parsing remains an open problem

E.g., dealing with ambiguities, but also dealing with programming languages beyond context-free languages

While parsing serves a practical purpose, it is important to also have a deep theoretical understanding of the semantics of parsing

While parsing is often studied using automata theory [CITE], there is also value in studying more denotational approaches to parsing.

Indeed, a main purpose of denotational semantics is to abstract away operational concerns, as such concerns tends to be a hindrance for equational reasoning.

A denotational approach could thus provide a framework for studying and proving the correctness of, e.g., parser optimizations and disambiguation techniques.

It could also provide a building block for obtaining correct parsers of expressive grammar formalisms, such as data-dependent grammars [CITE].

Recent work by Elliott demonstrated that parsers for regular grammars can be given a simple and direct semantics

In turn, we can obtain parsers for such languages that are (practically) correct by construction, by taking their \emph{derivatives}.

While it was well-known~\cite{brzozowski} that we can parse regular grammars using Brzozowski derivatives, Elliot provides a simple and direct mechanization in Agda of the denotational semantics of these derivatives.

Elliot leaves open the question of how the approach scales to more expressive grammar formalisms, such as context-free languages and beyond.

This paper addresses that question.

Specifically, we study the problem of mechanizing, also in Agda, (1) the denotational semantics of context-free grammars; and (2) a simple and direct denotational semantics of the derivative of context-free grammars.

A main challenge for this mechanization is dealing with the recursive nature of context-free languages.

\subsection{The Challenge with Automated Differentiation of Context-Free Grammars}

Derivatives provide an automated procedure for differentiation of languages.

In this subsection we consider the problem of automatically taking the derivative of a context-free grammar w.r.t. a given symbol.

To illustrate, let us consider the following context-free grammar of palindromic bit strings:

\[
\langle\mathit{pal}\rangle ::= 0 \mid 1 \mid 0\, \langle\mathit{pal}\rangle\, 0 \mid 1\, \langle\mathit{pal}\rangle\, 1
\]

Say we want to use this grammar to parse the string 0110.

The idea of atuomatic differentiation is this:

We first compute the derivative of the grammar w.r.t. the first bit (0) of our bit string (0110).

Let us call this grammar $\langle pal_0\rangle$.

Then, we take the derivative of $\langle pal_0\rangle$ w.r.t. the next bit (1).

We continue this procedure until we either (1) get stuck because the derivative is invalid, in which case the bit string is not well-formed w.r.t. our grammar, or (2) the derivative grammar contains the empty production (we will use the symbol ε to denote the empty grammar), in which case the bit string is well-formed w.r.t. our grammar.

Taking the derivative of the $\langle\mathit{pal}\rangle$ grammar w.r.t. the bit 0 yields the following derived grammar:

\[
\langle\mathit{pal}_0\rangle ::= ε \mid \langle\mathit{pal}\rangle\, 0
\]

This grammar essentially represents the residual parsing obligations after parsing a 0 bit.

The derived grammar contains fewer productions than the original grammar because we have pruned those productions that started with the bit 1 (because the derivative of the bit 0 w.r.t. the terminal symbol 1 is invalid).

Now, how do we take the derivative of the grammar $\langle\mathit{pal}_0\rangle$ w.r.t. the next bit (1) in our string?

A simple solution is to recursively unfold the $\langle \mathit{pal} \rangle$ non-terminal.

Doing so for the $\langle\mathit{pal}\rangle$ grammar yields the following derived grammar:

\[
\langle\mathit{pal}_0'\rangle ::= ε \mid 0\, 0 \mid 1\, 0 \mid 0\, \langle\mathit{pal}\rangle\, 0\, 0 \mid 1\, \langle\mathit{pal}\rangle\, 1\, 0
\]

By continuing this procedure, with additional recursive unfolding where needed, we eventually yield a grammar that contains the the empty production ε, whereby we can conclude that 0110 is, in fact, a palindromic bit string.

However, the recursive unfolding we performed above is not safe to do for all grammars.

Consider, for example, the infinitely recursive grammar:

\[
\langle\mathit{rec}\rangle ::= \langle\mathit{rec}\rangle
\]

We cannot ever unfold this grammar to expose a terminal symbol to derive w.r.t., akin to the informal procedure we applied above.

Another challenge with context-free grammars is how to encode their recursive nature in a proof assistant such as Agda in a way that our encoding of grammars is strictly positive, and in a way that ensures that automated differentiation---that is, continuously applying the method we informally illustrated above for taking the derivative of a grammar w.r.t. a symbol---is guaranteed to terminate.


\subsection{Contributions}


This paper tackles the challenges discussed in the previous section by providing a mechanization in Agda of automated differentiation of a subset of context-free grammars.

The subset we consider corresponds to context-free grammars with non-terminal symbols without mutual recursion.

We conjecture that our approach is compatible with all context-free grammars, at the cost of some additional book-keeping while taking the derivative.

We leave verifying this conjecture as a challenge for future work.

We make the following technical contributions:

1. We provide a semantics in Agda of context-free grammars without mutual recursion.

2. We provide a semantics of automated differentiation for this class of grammars, along with its simple and direct correctness proof.

The rest of this paper is structured as follows: [...]

We assume basic familiarity with Agda.




\endinput

Parsing is the conversion of flat, human-readable text into a tree structure
that is easier for computers to manipulate.  As one of the central
pillars of compiler tooling since the 1960s, today almost every automated
transformation of computer programs requires a form of parsing.
Though it is a mature research subject, it is still actively studied, for example the question of how to resolve ambiguities in context-free grammars \cite{one-parser-to-rule-them-all}. 

Most parsing works mix the essence of the parsing technique with operational details \jr{such as... state machines, continuations, memoization?}. Our understanding and ability to improve upon these parsing techniques is hindered by the additional complexity of these inessential practical concerns. To address this issue, we are developing natural denotational semantics for traditional parsing techniques.

\jr{Elliott has kicked off this effort...}
Recent work by Elliott uses interactive theorem provers to state simple specifications of languages and that proofs of desirable properties of these language specifications transfer easily to their parsers \cite{conal-languages}. Unfortunately, this work only considers regular languages which are not powerful enough to describe practical programming languages.

\jr{Make the problem clear through an example: if we have a left-recursive grammar then naively unfolding it gets us into an infinite loop. }

In this paper, we formalize context-free languages and show how to parse them, extending Elliott’s type theoretic approach to language specfication.  One of the main challenges is that the recursive nature of context-free languages does not map directly onto interactive theorem provers as they do not support general recursion (for good reasons). We encode context-free languages as fixed points of functors (initial algebras).

\jr{Say something about the limitation that we only study acyclic grammars: there must be a total order on nonterminals and a nonterminal is not allowed to refer to nonterminals that come before it. We wanted to start by limiting ourselves to grammars with only one nonterminal, but those are not closed under derivatives.}

We make the following concrete contributions:
\begin{itemize}
\item We extend Elliott's type theoretic formalization of regular languages to context-free languages.
\end{itemize}

For this paper we have chosen Agda as our type theory and interactive theorem prover. We believe our definitions should transfer easily to other theories and tools. This paper itself is a literate Agda file; all highlighted Agda code has been accepted by Agda's type checker, giving us a high confidence of correctness.

% The goal is to give a denotational semantics to context-free languages
% And mechanize this in a proof assistants

% Challenge:
% Give a simple non-recursive example
% Expand to a recursive variant

% We could use full blown domain theory, but that is quite a big hammer

% In section 2:
% * Could: "This is a background section"
% * We recall Elliott's ...
% * To make it easier to add fixed points in the next section

% Look for a simple example in Section 2. Can be contrived
