\begin{code}[hide]
module 2-overview where

open import Data.List

data Token : Set where

\end{code}

\section{Languages}

In this section, we recapitulate the basic definitions from previous work by Elliot~\cite{conal-languages} and .

A language is a set of strings $\mathbb{2}^{\af{List}~\af{Token}}$.


\begin{code}[hide]
Lang : Set₁
\end{code}
\begin{code}
Lang = List Token → Set
\end{code}

This type has a very rich structure. It forms an ... algebra with union and intersection and a semiring with union and sequential composition.

Going behond work by Elliot, we can try to define context-free grammars.
Unfortunately, we quickly run into issues due to nontermination. It is not easy
to show that a grammar defined in this way is well-founded. To solve this issue
we can use guarded type theory, in our case provided by guarded cubical Agda.
This allows us to define arbitrary fixed points of languages.