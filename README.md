<script type="text/x-mathjax-config"> 
    MathJax.Hub.Config({ TeX: { equationNumbers: { autoNumber: "all" } } }); 
</script>

<script type="text/x-mathjax-config">
    MathJax.Hub.Config({tex2jax: {
            inlineMath: [ ['$','$'], ["\\(","\\)"] ],
            processEscapes: true
        }
        });
</script>

<script src="https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML" type="text/javascript">
</script>

# Automated Theorem Proving

## **Background**

Wang's idea is based around the notion of a sequent (this idea had been introduced years earlier by
Gentzen) and the manipulation of sequents. A sequent is essentially a list of formulae on either side
of a sequent (or provability) symbol $\vdash$. The sequent $\pi \vdash \rho$, where $\pi$ and $\rho$ are strings (i.e., lists) of formulae, can be read as "the formulae in the string $\rho$ follow from the formulae in the string $\pi$" (or,
equivalently, "the formulae in string $\pi$ prove the formulae in string $\rho$").

To prove whether a given sequent is true all you need to do is start from some basic sequents and
successively apply a series of rules that transform sequents until you end up with the sequent you
desire. This process is detailed below.

Additionally, determining whether a formula $\phi$ is a theorem, is equivalent to determining whether the
sequent $\emptyset \vdash \phi$ is true (e.g. $\vdash \neg \phi \lor \phi $).

## **Formulae**

### **Connectives**

We allow the following connectives in decreasing order of precedence:

symbol            | meaning
------------------|-------------
$\neg $           | negation
$\land$           | conjunction
$\lor$            | disjunction
$\to$             | implication
$\leftrightarrow$ | biconditional (both same precedence)

### **Formula**

- A propositional symbol (e.g. $ p, q, ... $) is an *atomic* formula (and thus a formula).
- If $\phi, \psi $ are formulae, then $\neg\phi,\ \phi \land\ \psi,\ \phi \lor\ \psi,\ \phi \rightarrow \psi,\ \phi \leftrightarrow \psi$ are formulae.

### **Sequent**

If $\pi$ and $\rho$ are strings of formulae (possibly empty strings) and $\phi$ is a formula, then $\pi,\ \phi,\ \rho\$ is a string and $\pi \vdash \rho$ is a sequent.

### **Rules**

The logic consists of the following sequent rules. The rst rule (P1) gives a characterisation of simple
theorems. The remaining rules are simply ways of transforming sequents into new sequents. The
manner in which you can construct a proof for a sequent to determine whether it holds or not is given
below.

**P1** Initial Rule: If $\lambda,\ \zeta$ are strings of atomic formulae, then $\lambda \vdash \zeta$ is a theorem if some atomic formula occurs on both side of the sequent $\vdash$.
In the following ten rules  and  are always strings (possibly empty) of formulae.

**P2a** Rule $\vdash \neg$: If $\phi,\ \zeta \vdash \lambda,\ \rho$ then $\zeta \vdash \lambda,\ \neg \phi,\ \rho$


**P2b** Rule $\neg \vdash$: If $\lambda,\ \rho \vdash \pi,\ \phi$ then $\lambda,\ \neg\phi,\ \rho \vdash \phi$


**P3a** Rule $\vdash\land$: If $\zeta\ \vdash \lambda,\ \phi,\ \rho$ and $\zeta\ \vdash\lambda,\ \psi,\ \rho$ then $ \zeta\ \vdash \lambda,\ \phi\land\psi,\ \rho$


**P3b** Rule $\land\vdash$: If $\lambda,\ \phi,\ \psi,\ \rho \vdash \pi$ then $\lambda,\ \phi\land\psi,\ \rho \vdash \pi$


**P4a** Rule $\vdash\lor$: If $\zeta \vdash \lambda,\ \phi,\ \psi,\ \rho$ then $\zeta \vdash \lambda,\ \phi \lor \psi,\ \rho$


**P4b** Rule $\lor\vdash$: If $\lambda,\ \phi,\ \rho \vdash \pi$ and $\lambda,\ \psi,\ \rho \vdash \pi $ then $\lambda,\ \phi\lor\psi,\ \rho \vdash \pi$


**P5a** Rule $\vdash\to$: If $\zeta,\ \phi \vdash \lambda,\ \psi,\ \rho$ then $\zeta,\ \phi\to\psi \vdash \lambda,\ \rho$


**P5b** Rule $\to\vdash$: If $\lambda,\ \psi,\ \rho \vdash \pi$ and $\lambda,\ \rho \vdash \pi,\ \phi$ then $\lambda,\ \phi\to\psi,\ \rho \vdash \pi$ 


**P6a** Rule $\vdash\leftrightarrow$: If $\phi,\ \zeta \vdash \lambda,\ \psi,\ \rho$ and $\psi,\ \zeta\vdash \lambda,\ \phi,\ \rho$ then $ \zeta \vdash\lambda,\ \phi\leftrightarrow\psi,\ \rho $


**P6b** Rule $\leftrightarrow\vdash$: If $\phi,\ \psi,\ \lambda,\ \rho \vdash \pi$ and $\lambda,\ \rho \vdash \phi,\ \psi,\ \pi$ then $ \lambda,\ \phi\leftrightarrow\psi,\ \rho \vdash \pi $


## **Proof**

The basic idea in proving a sequent $\pi \vdash \rho$ is to begin with instance(s) of Rule P1 and successively
apply the remaining rules until you end up with the sequent you are hoping to prove.
For example, suppose you wanted to prove the sequent $\neg (p \lor q) \vdash \neg p$. One possible proof would proceed
as follows.

|||
----------------------|------------
1. $ p \vdash p,\ q $ | Rule **P1**
2. $ p \vdash p \lor q $ | Rule **P4a**
3. $ \vdash \neg p,\ p \lor q $ | Rule **P2a**
4. $ \neg (p \lor q) \vdash \neg p$ | Rule **P2b**
|||
$QED.$

However, a simpler idea (as it will involve much less search) is to begin with the sequent(s) to be proved
and apply the rules above in the "backward" direction until you end up with the sequent you desire.
In the example then, you would begin at step 4 and apply each of the rules in the backward direction
until you end up at step 1 at which point you can conclude the original sequent is a theorem.

## **Input**

The input will consist of a single sequent on the command line. Sequents will be written as:
[_List of Formulae_] seq [_List of Formulae_] To construct formulae, atoms can be any string of characters (without space) and connectives as follows:

- $\neg$: neg
- $\land$: and
- $\lor$: or
- $\to$: imp
- $\leftrightarrow$: iff
- $\vdash$: seq
  
So, for example, the sequent $p \to q,\ \neg r \to \neg q \vdash p \to r$ would be written as:

    [p imp q, (neg r) imp (neg q)] seq [p imp r]

Your program should be called assn1q3 and run as follows:

    python Auto-Prove.py "Sequent"

For example

- MAC or linux OS
    ```shell
    $python3 AutoProve.py '[p imp q, (neg r) imp (neg q)] seq [p imp r]'
    ```
-  window 10
    ```powershell
    >python AutoProve.py '[p imp q, (neg r) imp (neg q)] seq [p imp r]'
    ```

## **Output**

the output will be either True or False and give the proof process.

## **Reference**

- [1] Hao Wang, Toward Mechanical Mathematics, IBM Journal for Research and Development, volume
4, 1960. (Reprinted in: Hao Wang, "Logic, Computers, and Sets", Sciene Press, Peking, 1962. Hao
Wang, "A Survey of Mathematical Logic", North Holland Publishing Company, 1964. Hao Wang,
"Logic, Computers, and Sets", Chelsea Publishing Company, New York, 1970.)

- [2] Alfred North Whitehead and Bertrand Russell, Principia Mathematica, 2nd Edition, Cambridge
University Press, Cambridge, England, 1927.



_Note: please install the plugin for google chrome named_ [_**MathJex**_](https://chrome.google.com/webstore/detail/mathjax-plugin-for-github/ioemnmodlmafdkllaclgeombjnmnbima)