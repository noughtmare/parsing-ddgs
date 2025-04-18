\begin{code}[hide]
module 1-introduction where

open import Data.Unit

\end{code}

\section{Introduction}

Parsing---i.e., the process of recovering structure from strings---is an essential building block for many practical programming applications.
While parsing has been extensively studied, it remains a relevant subject of research where new research questions continuously emerge.
For example, how to compose grammars and parsers~(e.g.,~\cite{SchwerdfegerW09}), dealing with ambiguous parse trees~(e.g.,~\cite{BrabrandGM10,basten-thesis,vinju-evcs}), and parsing grammar formalisms beyond context-free grammars~(e.g.,~\cite{one-parser-to-rule-them-all}).
Research questions such as these serve a practical purpose, but answering them often requires a deep theoretical understanding of the semantics of parsing.

This theoretical understanding can be approached in different ways.
Parsing is often studied using automata theory~\cite{hopcroft-book}.
However, it is valuable to study more \emph{denotational} approaches to parsing too.
A main purpose of denotational semantics is to abstract away operational concerns, as such concerns tends to be a hindrance for equational reasoning.
Such equational reasoning could be used to study and answer some of the open research questions in the parsers of today and tomorrow.

This paper studies the denotational semantics of parsing for context-free grammars.
While the study is theoretical in nature, the motivation is to provide a foundation for practical future studies on proving the correctness of, e.g., parser optimizations and disambiguation techniques, as well as potentially providing a foundation for building and reasoning about parsers for more expressive grammar formalisms, such as data-dependent grammars~\cite{one-parser-to-rule-them-all}.

We approach the question of giving a denotational semantics of parsing by building on existing work by Elliott~\cite{conal-languages}.
In his recent work, Elliott demonstrated that regular grammars have a simple and direct denotational semantics.
And that we can obtain parsers for such languages that are correct by construction, using \emph{derivatives}.
While it was well-known that we can parse regular grammars using Brzozowski derivatives~\cite{brzozowski}, Elliott's work provides a simple and direct mechanization in Agda's type theory of the denotational semantics of these derivatives.
This mechanization provides an implementation of parsing that is correct by construction, and that we can reason about without relying on (bi-)simulation arguments.
While the parsers obtained in this manner are not designed to be performant, the denotational approach opens up the door to exploiting grammar structure to obtain optimized parsers.

Elliott leaves open the question of how the approach scales to more expressive grammar formalisms, such as context-free languages and beyond.
However, the question of using derivatives to parse context-free grammars has been considered by others.
Might et al.~\cite{parsing-with-derivatives} demonstrate how to build parsers from context-free grammars using derivatives and optimizations applied to them, to obtain reasonable performance.
Thiemann's work~\cite{Thiemann17} uses lattice theory and powerset semantics to formalize a notion of partial derivative for a variant of context-free grammars.
In this work, we build on the approach of Elliott and study how to build a simple and direct mechanization in Agda's type theory of the denotational semantics of derivatives for context-free grammars.

The main challenge for our mechanization is the question of how to deal with the recursive nature of context-free languages.

\subsection{The Challenge with Parsing Context-Free Grammars}

We give an overview of what it means to take the derivative of a grammar, how this provides an approach to parsing, and which challenges it poses.

To illustrate, consider the following context-free grammar of palindromic bit strings:
\[
\langle\mathit{pal}\rangle ::= ε \mid 0 \mid 1 \mid 0\, \langle\mathit{pal}\rangle\, 0 \mid 1\, \langle\mathit{pal}\rangle\, 1
\]
Say we want to use this grammar to parse the string 0110.
The idea of parsing with derivatives is to divide the problem into separate steps for each input symbol, each narrowing down the grammar.
After all input symbols have been processed, we can simply check if the final grammar accepts the empty string to see if the whole input is accepted by the original grammar.

We call each of these transformation steps derivatives.
Taking the derivative of a grammar with respect to an input symbol can be done naively by keeping only the productions which start with that symbol and then removing that symbol from the start of each of the productions.
Empty productions (ε) are always removed when taking a derivative.

Using this naive derivation procedure on the $\langle\mathit{pal}\rangle$ grammar with respect to the bit 0 yields the following derived grammar:
\[
\langle\mathit{pal}_0\rangle ::= ε \mid \langle\mathit{pal}\rangle\, 0
\]
This grammar essentially represents the residual parsing obligations after parsing a 0 bit.
The derived grammar contains fewer productions than the original grammar because we have pruned those productions that started with the terminal symbol 1.

For the next derivative step, we encounter a new special case: one of the productions starts with a nonterminal.
A naive solution is to recursively unfold nonterminals until the production starts with a terminal symbol.
For the $\langle\mathit{pal}\rangle$ grammar, we only have to unfold $\langle \mathit{pal} \rangle$ once which yields the following grammar:
\[
\langle\mathit{pal}_0'\rangle ::= ε \mid 0\, 0 \mid 1\, 0 \mid 0\, \langle\mathit{pal}\rangle\, 0\, 0 \mid 1\, \langle\mathit{pal}\rangle\, 1\, 0
\]
By continuing this procedure, with additional recursive unfolding where needed, we eventually yield a grammar that contains the the empty production ε, whereby we can conclude that 0110 is, in fact, a palindromic bit string.

However, naive recursive unfolding does not work for all grammars.
Consider, for example, the infinitely recursive grammar:
\[
\langle\mathit{rec}\rangle ::= \langle\mathit{rec}\rangle
\]
Unfolding this grammar never reveals a starting nonterminal.
While the $\langle\mathit{rec}\rangle$ grammar is contrived, the same issue arise for any \emph{left-recursive} grammar, such as the following grammar of arithmetic expressions (left-recursive because of the $\langle\mathit{expr}\rangle$ non-terminal in the left-most position in the first production):
\[
\langle\mathit{expr}\rangle ::= \langle\mathit{expr}\rangle\, +\, \langle\mathit{expr}\rangle \mid 0 \mid 1
\]

Parsing context-free grammars, thus, requires more sophisticated techniques.

\subsection{Contributions}

This paper tackles the challenges discussed in the previous section by providing a mechanization in Agda of parsing a subset of context-free grammars with derivatives.
We represent grammars using a restricted form of μ-regular expressions, which extend regular expressions with fixed points and which can express all context-free languages.

The subset of grammars that we consider corresponds to context-free grammars without mutually recursive nonterminals.
In other words, the grammars can consist of multiple nonterminals which may refer to themselves and others, but there may not be a cycle which involves more than one nonterminal.
For example, the following mutually recursive grammar does not fit into the subset of grammars we consider:
\begin{align*}
\langle\mathit{expr}\rangle &::= \langle\mathit{expr}\rangle\, +\, \langle\mathit{expr}\rangle \mid 0 \mid 1 \mid \langle\mathit{stmt}\rangle
\\
\langle\mathit{stmt}\rangle &::= \langle\mathit{expr}\rangle \mid \langle\mathit{stmt}\rangle ; \langle\mathit{stmt}\rangle
\end{align*}
The $\langle\mathit{pal}\rangle$, $\langle\mathit{rec}\rangle$, and $\langle\mathit{expr}\rangle$ grammars from the previous section are all examples of grammars that are in the subset.
We conjecture that our approach can be extended to deal with all context-free grammars, at the cost of some additional bookkeeping.
We leave verifying this conjecture as a challenge for future work.

We make the following technical contributions:
\begin{itemize}
\item We provide a semantics in Agda of context-free grammars without mutual recursion.
\item We provide a derivative-based parser for this class of grammars, along with its simple and direct correctness proof.
\end{itemize}

The paper assumes basic familiarity with Agda.
The rest of this paper is structured as follows.
\Cref{sec:finite-languages} recalls the essential definition from Elliott's work which we subsequently extend in \cref{sec:context-free} to context-free grammars.
\Cref{sec:discussion} discusses expressiveness, performance, and simplicity of our approach, whereas
\cref{sec:related-work} discusses related work, and \cref{sec:conclusion} concludes.




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

%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:
