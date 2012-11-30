A tiny type-checker, based on ideas from


* ΠΣ: Dependent Types without the Sugar (Altenkirch, Danielsson, Löh,  Oury)
* On the Algebraic Foundation of Proof Assistants for Intuitionistic Type Theory (Abel, Coquand, Dybjer)
* A Tutorial Implementation of a Dependently Typed Lambda Calculus (Löh, McBride, Swierstra)
* A Calculus of Definitions (Coquand)


Features:

* A hierarchy of universes (A la Agda)
* Finite types
* Dependent products and sums (ΠΣ)
* A top-level definition (this) which can be used recursively (general recursion)

Structure:

* RawSyntax.hs: definition of the syntax using BNFC 
* AbsSynToTerm.hs: conversion form the raw syntax to Terms (as below)
* Terms.hs: internal representation for Terms (using DeBrujn indices)
* TypeChecker.hs: integrated type-checker and normaliser
* Main.hs/Options.hs: driver
